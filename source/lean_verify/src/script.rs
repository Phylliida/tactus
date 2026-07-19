//! N3-M2: provenance-driven proof scripts (DESIGN-N3-provenance-scripts.md
//! §4–§6). The emitter — which holds each obligation's full causal history
//! (its frame list with provenance, the goal's shape, the user's proof-body
//! structure) — AUTHORS the Lean proof script directly, instead of leaving
//! a searched `first|`-chain to re-derive that knowledge at proof time.
//!
//! A script is a `Vec<Move>`; each `Move` renders to fixed Lean tactic
//! text. Scripts are emitted PRIMARY with the derived closer as fallback
//! (§8):
//!
//! ```lean
//! by
//!   <haves block (unchanged)>
//!   first
//!   | (<script>)          -- when author_v1 returned Some
//!   | (<derived closer>)  -- the M1 chain, verbatim
//! ```
//!
//! Every referenced name must be a binder/have visible in the same
//! theorem — `author_v1` builds scripts only from names it can see in the
//! `GoalShape` spine or the goal itself (a script citing an unknown name
//! is an emitter bug: `debug_assert` at author time).
//!
//! M2 v1 scope: forms A and B, on the N1-hoisted (flat-goal) path only.

use crate::lean_ast::{Binder, CloserCensus, Expr, ExprNode, GoalShape, GoalSpine, HypProvenance};
use crate::tactic_select::{goal_unfold_names, recursive_lhs_head, DtDefInventory};

/// One scripted tactic step. Renders to fixed Lean tactic text — no
/// proof-time search beyond the fail-fast leaf closers.
#[derive(Debug, Clone)]
pub enum Move {
    /// `intro a b _ …` — named spine intros (source: goal spine).
    Intros(Vec<String>),
    /// `intro x; subst x` — a goal-let binder intro + subst (the
    /// render_peel pattern: only subst turns a let-bound fact into a
    /// usable rewrite).
    IntroSubst(String),
    /// `subst h1 h2 …` — substitute the named N1 hoist-equations.
    SubstHoists(Vec<String>),
    /// `simp only [f, g, …]` — unfold the named NON-recursive spec fns.
    UnfoldSet(Vec<String>),
    /// `rw [f]` — ONE measured unfold of a recursive spec fn (the loop
    /// law: recursive fns never ride simp sets).
    UnfoldOnce(String),
    /// `simp only [h1, …, if_true, …] at *` — the guard simp, applied
    /// EVERYWHERE (goal + hyps), with the branch/fact hypotheses NAMED
    /// (provenance), never the broadcast haves. `at *` is what lets a
    /// fact hyp (`len (push p c) = 1`) normalize the bounds inside
    /// OTHER fact hyps (`subrange … ↑(len (push p c)) = empty`) —
    /// the M1-provenance-free arms could not reach this case.
    GuardSimpStar(Vec<String>),
    /// `simp only [h1, …, if_true, …]` — goal-only guard simp (N1
    /// path: facts are already named binders, no normalization needed).
    GuardSimp(Vec<String>),
    /// `split <;> <moves>` — split an ite goal, each leg closed by the
    /// same per-leg sequence.
    SplitIf(Vec<Move>),
    /// `exact h` — the goal syntactically equals hyp `h`
    /// (post-normalization — the author compared the texts at
    /// emission; cheap because the emitter HOLDS both).
    ExactHyp(String),
    /// `rfl` — the sides differ only by let-defeq / ctor-eta after the
    /// unfold.
    Defeq,
    /// `done` — succeeds vacuously on zero goals (an earlier move may
    /// have closed the goal: `rfl`/`omega`/`intro` all ERROR on zero
    /// goals, so close alternatives must end with `done` or the script
    /// dies with "No goals to be solved" after succeeding).
    Done,
    /// `first | assumption | omega | with_reducible rfl` — the fail-fast
    /// terminal ladder.
    LeafClose,
    /// `simp_all; omega` — the form-E leg: broadcast haves rewrite the
    /// guard facts (`len (empty _) = 0`) omega then consumes.
    LeafSimpAllOmega,
    /// The structural simp ladder (rung tail) for sides that differ by
    /// further non-recursive unfolds. Carries the ext-have exclusions
    /// (`-_tactus_bc_<i>` for the PROP-valued equation rewrites — the
    /// ext axioms that would otherwise explode the goal's own Seq
    /// equality; the arithmetic seq axioms stay in).
    StructuralTail(Vec<String>, Vec<String>),
    /// `first | (m1) | (m2) | …` — alternation (the ONLY backtracking
    /// in a script; each alternative stays fail-fast).
    FirstOf(Vec<Move>),
}

/// Which corpus family the authored script belongs to (drives the
/// census class).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptForm {
    /// Form A — branch + woven fact (probe zpoly_probe.lean).
    A,
    /// Form B — definitional step of a recursive spec fn (probe
    /// pmul_conv.lean).
    B,
}

impl ScriptForm {
    pub fn census(&self) -> CloserCensus {
        match self {
            ScriptForm::A => CloserCensus::ScriptFormA,
            ScriptForm::B => CloserCensus::ScriptFormB,
        }
    }
}

/// Render one move to tactic text.
fn render_move(m: &Move) -> String {
    match m {
        Move::Intros(names) => format!("intro {}", names.join(" ")),
        Move::IntroSubst(x) => format!("intro {0}; subst {0}", x),
        Move::SubstHoists(names) => format!("subst {}", names.join(" ")),
        Move::UnfoldSet(fns) => {
            if fns.is_empty() {
                "simp only []".to_string()
            } else {
                format!("simp only [{}]", fns.join(", "))
            }
        }
        Move::UnfoldOnce(f) => format!("rw [{}]", f),
        Move::GuardSimpStar(names) => {
            let base = "if_true, if_false, reduceIte, reduceCtorEq, Nat.succ_ne_zero, Nat.add_one, Nat.zero_add, Nat.add_zero".to_string();
            if names.is_empty() {
                format!("simp only [{}] at *", base)
            } else {
                format!("simp only [{}, {}] at *", names.join(", "), base)
            }
        }
        Move::GuardSimp(names) => {
            let base = "if_true, if_false, reduceIte, reduceCtorEq, Nat.succ_ne_zero, Nat.add_one, Nat.zero_add, Nat.add_zero".to_string();
            if names.is_empty() {
                format!("simp only [{}]", base)
            } else {
                format!("simp only [{}, {}]", names.join(", "), base)
            }
        }
        Move::SplitIf(legs) => {
            let alts = legs
                .iter()
                .map(|m| format!("({})", render_move(m)))
                .collect::<Vec<_>>()
                .join(" | ");
            format!("split <;> (first | {})", alts)
        }
        Move::ExactHyp(h) => format!("exact {}", h),
        Move::Defeq => "rfl".to_string(),
        Move::Done => "done".to_string(),
        Move::LeafClose => "first | assumption | omega | with_reducible rfl".to_string(),
        Move::LeafSimpAllOmega => "simp_all; omega".to_string(),
        Move::StructuralTail(unfolds, exclusions) => {
            let base = format!(
                "{}, {}",
                crate::tactic_select::CORE_LEMMAS,
                crate::tactic_select::STRUCTURAL_EXTRA_LEMMAS
            );
            let mut list = base;
            if !unfolds.is_empty() {
                list = format!("{}, {}", list, unfolds.join(", "));
            }
            for x in exclusions {
                list = format!("{}, -{}", list, x);
            }
            format!("simp_all +zetaDelta only [{}] <;> omega", list)
        }
        Move::FirstOf(alts) => {
            let parts: Vec<String> =
                alts.iter().map(|m| format!("({})", render_move(m))).collect();
            format!("first | {}", parts.join(" | "))
        }
    }
}

/// Render a whole script: `; `-joined tactic text.
pub fn render_script(moves: &[Move]) -> String {
    moves.iter().map(render_move).collect::<Vec<_>>().join("; ")
}

// ────────────────────────────────────────────────────────────────────
// Authoring inputs from the GoalShape
// ────────────────────────────────────────────────────────────────────

/// One hypothesis visible to the script: its theorem-binder name, its
/// proposition, and its provenance.
struct ShapeHyp {
    name: String,
    prop: Expr,
    prov: HypProvenance,
}

/// Collect the hypotheses the script may cite: every binder/hyp in the
/// goal shape that carries hypothesis provenance, plus requires-binders.
/// Broadcast haves are NOT here by construction (they live in the
/// tactic prefix, not the goal spine) — the M2 cleanliness over M1's
/// exclusion hack.
fn shape_hyps(shape: &GoalShape) -> Vec<ShapeHyp> {
    let mut out = Vec::new();
    for node in &shape.spine {
        match node {
            GoalSpine::All(b, Some(prov)) => {
                if let Some(name) = &b.name {
                    out.push(ShapeHyp {
                        name: name.as_str().to_string(),
                        prop: b.ty.clone(),
                        prov: prov.clone(),
                    });
                }
            }
            GoalSpine::Imp(p, prov) => {
                // Imps land in the goal as antecedents, not named
                // binders — scripts on the N1 path can't cite them by
                // name; the spine walk intros them as `_`.
                let _ = (p, prov);
            }
            _ => {}
        }
    }
    out
}

/// The binder names of N1 hoist-equations (SubstHoists' targets).
fn hoist_eq_names(hyps: &[ShapeHyp]) -> Vec<String> {
    hyps.iter()
        .filter(|h| matches!(h.prov, HypProvenance::HoistEq { .. }))
        .map(|h| h.name.clone())
        .collect()
}

/// Apply the hoist-equation substitutions to an expression: replace
/// `Var(binder)` by the equation RHS, for every HoistEq hyp. Used by
/// the ExactHyp cheap check (the author holds both texts — no
/// proof-time hoping).
fn apply_hoist_substs(e: &Expr, hyps: &[ShapeHyp]) -> Expr {
    let mut out = e.clone();
    for h in hyps {
        if let HypProvenance::HoistEq { binder } = &h.prov {
            if let ExprNode::BinOp { op: crate::lean_ast::BinOp::Eq, lhs, rhs } = &h.prop.node {
                if matches!(&lhs.node, ExprNode::Var(n) if n.as_str() == binder.as_str()) {
                    out = subst_var(&out, binder.as_str(), rhs);
                }
            }
        }
    }
    out
}

fn subst_var(e: &Expr, name: &str, val: &Expr) -> Expr {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => subst_var(inner, name, val),
        ExprNode::Var(n) if n.as_str() == name => val.clone(),
        _ => Expr::new(crate::lean_ast::map_children(&e.node, |c| subst_var(c, name, val))),
    }
}

// ────────────────────────────────────────────────────────────────────
// The author (v1: forms A and B)
// ────────────────────────────────────────────────────────────────────

/// Author a script for one obligation. The author walks the goal's
/// leading ∀/→/let spine itself, naming antecedent hypotheses as it
/// goes (`h_scr_N` — the script's own names, cited later in the same
/// script). Returns the moves and the form. `None` when no v1 form
/// applies — the caller emits the derived chain (the census counts
/// that separately).
pub fn author_v1(
    goal: &Expr,
    shape: &GoalShape,
    dts: &DtDefInventory,
    ext_haves: &[String],
) -> Option<(Vec<Move>, ScriptForm)> {
    let hyps = shape_hyps(shape);
    fn peel_transparent(mut e: &Expr) -> &Expr {
        loop {
            match &e.node {
                ExprNode::SpanMark { inner, .. } => e = inner,
                ExprNode::TypeAnnot { expr, .. } => e = expr,
                _ => return e,
            }
        }
    }
    // Walk the spine: Forall → intro names; Implies antecedent → a
    // script-chosen hyp name (cited in GuardSimp); Let → intro+subst,
    // EXCEPT N1's trailing equation wrapper (`let tmp := v; tmp`),
    // which must stay a goal-position let for `rw` to search through.
    let mut spine_moves: Vec<Move> = Vec::new();
    let mut ant_names: Vec<String> = Vec::new();
    let mut cur = goal;
    loop {
        match &cur.node {
            ExprNode::SpanMark { inner, .. } => cur = inner,
            ExprNode::TypeAnnot { expr, .. } => cur = expr,
            ExprNode::Forall { binders, body } => {
                let names: Vec<String> = binders
                    .iter()
                    .map(|b| match &b.name {
                        Some(n) => n.as_str().to_string(),
                        None => "_".to_string(),
                    })
                    .collect();
                spine_moves.push(Move::Intros(names));
                cur = body;
            }
            ExprNode::BinOp { op: crate::lean_ast::BinOp::Implies, rhs, .. } => {
                let n = format!("h_scr_{}", ant_names.len());
                ant_names.push(n.clone());
                spine_moves.push(Move::Intros(vec![n]));
                cur = rhs;
            }
            ExprNode::Let { name, value, body } => {
                let b = peel_transparent(body);
                if matches!(&b.node, ExprNode::Var(n) if n.as_str() == name.as_str()) {
                    // Trailing wrapper: look through to the value.
                    cur = value;
                } else {
                    spine_moves.push(Move::IntroSubst(name.as_str().to_string()));
                    cur = body;
                }
            }
            _ => break,
        }
    }
    let core = peel_transparent(cur);
    // ── Form B: Eq/Iff core with a recursive spec fn as LHS head. ──
    if let Some(f) = recursive_lhs_head(core, dts) {
        let mut moves = spine_moves;
        moves.push(Move::UnfoldOnce(f.to_string()));
        // GuardSimp everywhere: every shape hyp + the script-named
        // antecedents — the goal's OWN facts, no broadcast haves.
        // `at *` is what normalizes fact-hyps' bounds through each
        // other (M1's unreachable case).
        let names: Vec<String> =
            hyps.iter().map(|h| h.name.clone()).chain(ant_names).collect();
        moves.push(Move::GuardSimpStar(names));
        let unfolds = goal_unfold_names(goal, dts, &shape_binders(shape));
        moves.push(Move::FirstOf(vec![
            Move::Defeq,
            Move::StructuralTail(unfolds, ext_haves.to_vec()),
            Move::Done,
        ]));
        debug_assert!(script_names_resolve(&moves, shape, dts));
        return Some((moves, ScriptForm::B));
    }
    // ── Form A: branch + woven fact (N1-hoisted flat path). ──
    let unfolds = goal_unfold_names(goal, dts, &shape_binders(shape));
    if unfolds.is_empty() {
        return None;
    }
    let has_call_fact = hyps.iter().any(|h| matches!(h.prov, HypProvenance::CallFact(_)));
    // ExactHyp justification: a shape hyp whose proposition, after the
    // hoist substs, textually equals the goal core.
    let exact = find_exact_hyp(&hyps, core);
    if !has_call_fact && exact.is_none() {
        return None;
    }
    let mut moves = spine_moves;
    let hoists = hoist_eq_names(&hyps);
    if !hoists.is_empty() {
        moves.push(Move::SubstHoists(hoists));
    }
    moves.push(Move::UnfoldSet(unfolds));
    // Legs: omega (arithmetic contradictions), the form-E leg
    // (simp_all; omega — broadcast haves rewrite guard facts), then
    // the matching hyp when the author computed one.
    let mut legs = vec![Move::LeafClose, Move::LeafSimpAllOmega];
    if let Some(h) = exact {
        legs.push(Move::ExactHyp(h));
    }
    legs.push(Move::Done);
    moves.push(Move::SplitIf(legs));
    debug_assert!(script_names_resolve(&moves, shape, dts));
    Some((moves, ScriptForm::A))
}

/// The goal shape's binders as a `Binder` slice (for the unfold scan).
fn shape_binders(shape: &GoalShape) -> Vec<Binder> {
    shape
        .spine
        .iter()
        .filter_map(|n| match n {
            GoalSpine::All(b, _) => Some(b.clone()),
            _ => None,
        })
        .collect()
}

/// Find a shape hyp whose proposition — after applying the hoist
/// substitutions — textually equals the goal core (also after
/// substs). The author compares pp texts (it HOLDS both — no
/// proof-time hoping); the check is deliberately exact (no fuzzy
/// matching): when nothing matches, the legs simply omit ExactHyp.
fn find_exact_hyp(hyps: &[ShapeHyp], core: &Expr) -> Option<String> {
    let core_pp = crate::lean_pp::pp_expr(&apply_hoist_substs(core, hyps));
    for h in hyps {
        let subst = apply_hoist_substs(&h.prop, hyps);
        if crate::lean_pp::pp_expr(&subst) == core_pp {
            return Some(h.name.clone());
        }
    }
    None
}

/// Debug self-check: every name a script cites must be visible in the
/// goal shape or be a known global (spec fn / CORE lemma / tactic
/// keyword). A script citing an unknown name is an emitter bug.
fn script_names_resolve(moves: &[Move], shape: &GoalShape, dts: &DtDefInventory) -> bool {
    let mut visible: std::collections::HashSet<String> = std::collections::HashSet::new();
    for node in &shape.spine {
        if let GoalSpine::All(b, _) = &node {
            if let Some(n) = &b.name {
                visible.insert(n.as_str().to_string());
            }
        }
    }
    for m in moves {
        let cited: Vec<&str> = match m {
            Move::SubstHoists(ns) | Move::GuardSimp(ns) | Move::GuardSimpStar(ns) => {
                ns.iter().map(|s| s.as_str()).collect()
            }
            Move::ExactHyp(h) => vec![h.as_str()],
            Move::UnfoldSet(fs) => fs.iter().map(|s| s.as_str()).collect(),
            Move::StructuralTail(fs, _) => fs.iter().map(|s| s.as_str()).collect(),
            Move::UnfoldOnce(f) => vec![f.as_str()],
            Move::Intros(_) | Move::IntroSubst(_) | Move::Defeq | Move::Done | Move::LeafClose | Move::LeafSimpAllOmega => {
                vec![]
            }
            Move::SplitIf(legs) | Move::FirstOf(legs) => {
                if !script_names_resolve(legs, shape, dts) {
                    return false;
                }
                vec![]
            }
        };
        for c in cited {
            let global = dts.spec_fns.contains(c)
                || dts.recursive_spec_fns.contains(c)
                || dts.trait_methods.contains(c)
                || crate::tactic_select::CORE_LEMMAS.contains(c)
                || crate::tactic_select::STRUCTURAL_EXTRA_LEMMAS.contains(c)
                || c.contains('.');
            if !visible.contains(c) && !global {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
#[path = "tests/script.rs"]
mod tests;
