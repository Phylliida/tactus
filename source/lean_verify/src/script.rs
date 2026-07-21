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
    /// `simp only [f, g, …] at ⊢` — unfold the named NON-recursive
    /// spec fns, goal-only (the default — no context blowup).
    UnfoldSet(Vec<String>),
    /// `simp only [f, g, …] at ⊢ <targets>` — unfold in the goal and
    /// the NAMED hyps whose text mentions an unfold name (the
    /// den-equality class: the hyps carry the `denom` forms). Bare
    /// `at *` over a large context whnf-times-out and burns the
    /// theorem's whole heartbeat budget (divmod regression).
    UnfoldSetTargeted(Vec<String>, Vec<String>),
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
    /// `refine ⟨h1, h2⟩` — a 2-conjunct goal where each
    /// side matched a hyp (form C).
    RefineExact(Vec<String>),
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
    /// `simp_all only [set] <;> omega` — the ONLY leg simp: bare
    /// `simp_all` is opaque and version-unstable (the default simp set
    /// drifts with Mathlib, silently changing a script's meaning on
    /// upgrade — Danielle's law, 2026-07-20; see LEG_SIMP_LEMMAS). The
    /// spine already unfolded the goal's fns, context hyps rewrite
    /// regardless of `only` (broadcast haves, branch facts), the ite
    /// set collapses the split guards, omega finishes. Replaces both
    /// the wild `simp_all` leg (which mangled recip-shaped contexts)
    /// and the ite-only backstop.
    LeafSimpOnlyOmega(Vec<String>),
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
    /// Form C — equivalence chaining (§11.2): the goal's spine is the
    /// user's proof trace; the final fact IS a hyp post-substitution.
    C,
}

impl ScriptForm {
    pub fn census(&self) -> CloserCensus {
        match self {
            ScriptForm::A => CloserCensus::ScriptFormA,
            ScriptForm::B => CloserCensus::ScriptFormB,
            ScriptForm::C => CloserCensus::ScriptFormC,
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
                "simp only [] at ⊢".to_string()
            } else {
                format!("simp only [{}] at ⊢", fns.join(", "))
            }
        }
        Move::UnfoldSetTargeted(fns, targets) => {
            // The spine set is the goal's unfold names ONLY: every
            // normalizer added here has mangled a script family
            // (ofNat_toNat rewrites subrange's toNat forms out from
            // under divmod's `split`; if_pos/if_neg collapse the ites
            // `split` needs. Both live in the LEG set instead —
            // after `split` has peeled the outer guard, where the
            // recip sign branches actually need them. 2026-07-20.)
            let base = format!("simp only [{}] at ⊢", fns.join(", "));
            if targets.is_empty() {
                base
            } else {
                format!("{} {}", base, targets.join(" "))
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
        Move::RefineExact(hs) => {
            // `refine` takes a TERM: the conjunct proofs are the hyp names
            // themselves. `refine ⟨exact h1, exact h2⟩` is a syntax error
            // ("Unknown identifier `exact`") — the arm used to die on parse
            // and the failure surfaced as the LAST arm's error instead.
            format!("refine ⟨{}⟩", hs.join(", "))
        }
        Move::Defeq => "rfl".to_string(),
        Move::Done => "done".to_string(),
        Move::LeafClose => "first | assumption | omega | with_reducible rfl".to_string(),
        Move::LeafSimpOnlyOmega(fns) => format!(
            "simp_all only [{}] <;> omega",
            fns.join(", ")
        ),
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
/// proof-time hoping). Transparent wrappers are stripped and the
/// substitutions applied to a fixpoint — see `apply_let_substs`.
fn apply_hoist_substs(e: &Expr, hyps: &[ShapeHyp]) -> Expr {
    let mut substs: Vec<(String, Expr)> = Vec::new();
    for h in hyps {
        if let HypProvenance::HoistEq { binder } = &h.prov {
            if let ExprNode::BinOp { op: crate::lean_ast::BinOp::Eq, lhs, rhs } = &h.prop.node {
                if matches!(&lhs.node, ExprNode::Var(n) if n.as_str() == binder.as_str()) {
                    substs.push((binder.as_str().to_string(), rhs.as_ref().clone()));
                }
            }
        }
    }
    apply_let_substs(e, &substs)
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
    // Antecedent propositions and let-bindings are recorded too: the
    // form C normalized-match check applies the let-substs to both the
    // candidate facts and the goal (the emitter HOLDS all the texts).
    let mut spine_moves: Vec<Move> = Vec::new();
    let mut ant_names: Vec<String> = Vec::new();
    let mut ant_props: Vec<(String, Expr)> = Vec::new();
    let mut let_substs: Vec<(String, Expr)> = Vec::new();
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
            ExprNode::BinOp { op: crate::lean_ast::BinOp::Implies, lhs, rhs } => {
                let n = format!("h_scr_{}", ant_names.len());
                ant_names.push(n.clone());
                ant_props.push((n.clone(), lhs.as_ref().clone()));
                spine_moves.push(Move::Intros(vec![n]));
                cur = rhs;
            }
            ExprNode::Let { name, value, body } => {
                let b = peel_transparent(body);
                if matches!(&b.node, ExprNode::Var(n) if n.as_str() == name.as_str()) {
                    // Trailing wrapper: look through to the value.
                    cur = value;
                } else {
                    let_substs.push((name.as_str().to_string(), value.as_ref().clone()));
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
    // ── Form C: equivalence chaining (probe criterion §11.2). The
    // goal's own spine IS the user's proof trace: the last antecedents
    // (CallFact ensures from the user's explicit trans/cong calls)
    // textually equal the goal once the tmp lets are substituted. The
    // author applies the let-substs to every candidate and compares
    // pp texts — ExactHyp only when the match is exact.
    if std::env::var("TACTUS_DEBUG_FORMC").is_ok() {
        eprintln!(
            "[formc] V1 core={}",
            crate::lean_pp::pp_expr(core)
        );
    }
    if let Some(moves) = author_form_c(goal, core, &spine_moves, &hyps, &ant_props, &let_substs, shape, dts) {
        return Some((moves, ScriptForm::C));
    }
    // ── Defeq bridge (R1, the Rational story): a raw comparison goal
    // (`a.num * denom b = b.num * denom a`) with a class-projection
    // hyp over the same atoms (`eqv a b`). `exact h` closes it by
    // defeq through the inlined instance — sound, and the derived
    // chain catches any miss.
    if let Some(h) = find_defeq_bridge(core, &hyps, dts) {
        let mut moves = spine_moves;
        moves.push(Move::ExactHyp(h));
        debug_assert!(script_names_resolve(&moves, shape, dts));
        return Some((moves, ScriptForm::C));
    }
    // ── Form A: branch + woven fact (N1-hoisted flat path). ──
    let unfolds = goal_unfold_names(goal, dts, &shape_binders(shape));
    if unfolds.is_empty() {
        return None;
    }
    let has_call_fact = hyps.iter().any(|h| matches!(h.prov, HypProvenance::CallFact(_)))
        || shape
            .spine
            .iter()
            .any(|n| matches!(n, GoalSpine::Imp(_, HypProvenance::CallFact(_))));
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
    // Targeted unfold: the goal, plus exactly the hyps whose text
    // mentions an unfold name (the den-equality class's `denom`
    // facts). Bare `at *` would whnf-time-out on divmod-sized
    // contexts and burn the theorem's heartbeat budget before the
    // fallback ever runs.
    let mentioning = hyps_mentioning_any_unfold(&hyps, &ant_props, &unfolds);
    moves.push(Move::UnfoldSetTargeted(unfolds.clone(), mentioning));
    // The leg close: leaf ladder, then the ONE named leg simp
    // (LEG_SIMP_LEMMAS — every emitted simp is `simp only [named
    // things]`; see the const's doc), then ExactHyp, then Done.
    let leg_set: Vec<String> = crate::tactic_select::LEG_SIMP_LEMMAS
        .split(", ")
        .map(|s| s.to_string())
        .collect();
    let mut legs = vec![
        Move::LeafClose,
        Move::LeafSimpOnlyOmega(leg_set),
    ];
    if let Some(h) = exact {
        legs.push(Move::ExactHyp(h));
    }
    legs.push(Move::Done);
    moves.push(Move::FirstOf(vec![Move::LeafClose, Move::SplitIf(legs)]));
    debug_assert!(script_names_resolve(&moves, shape, dts));
    Some((moves, ScriptForm::A))
}

// ────────────────────────────────────────────────────────────────────
// Form C: equivalence chaining
// ────────────────────────────────────────────────────────────────────

/// Apply a list of let-substitutions (in spine order) to an expression.
/// The result is used ONLY for pp-text comparison (form C's exact-match
/// check): transparent wrappers are stripped, since `pp_expr` renders
/// each `SpanMark` as a leading `/- @rust:LOC -/` comment and each
/// `TypeAnnot` as `(e : Ty)` — the two sides of a real match carry
/// different wrappers from different emission paths (call-site args vs
/// the callee's instantiated ensures; antecedent props arrive with a
/// `(P : Prop)` ascription) that would otherwise never compare equal.
///
/// The substitutions are applied TO A FIXPOINT, not in a single pass:
/// hoist values mention earlier-bound names (`tmp19 := …(t)…` with
/// `t := subrange …`), and a single ordered pass leaves the inserted
/// values' inner names unexpanded on whichever side mentions them only
/// indirectly — the goal side kept `t` while the candidate side
/// expanded it, and textually-identical facts compared unequal
/// (pmul_comm's 890 precondition). The hoist graph is acyclic
/// (later binders reference earlier ones), so the fixpoint exists;
/// the iteration cap is a belt-and-suspenders bound.
fn apply_let_substs(e: &Expr, substs: &[(String, Expr)]) -> Expr {
    let mut out = e.clone();
    for _ in 0..16 {
        let next = substs.iter().fold(out.clone(), |cur, (name, val)| subst_var(&cur, name, val));
        if crate::lean_pp::pp_expr(&next) == crate::lean_pp::pp_expr(&out) {
            out = next;
            break;
        }
        out = next;
    }
    crate::lean_ast::strip_transparent(&out)
}

/// Form C (§11.2): the goal core, after applying the goal's own
/// let-substitutions, textually equals one of the candidate facts (the
/// antecedent hyps from the goal's implication spine — the user's own
/// trans/cong calls' ensures — or a shape hyp). Single goal →
/// `exact h`; a 2-conjunct goal → `refine ⟨h1, h2⟩`.
/// Anything else declines (the derived chain gets it).
fn author_form_c(
    goal: &Expr,
    core: &Expr,
    spine_moves: &[Move],
    hyps: &[ShapeHyp],
    ant_props: &[(String, Expr)],
    let_substs: &[(String, Expr)],
    shape: &GoalShape,
    dts: &DtDefInventory,
) -> Option<Vec<Move>> {
    if spine_moves.is_empty() && hyps.is_empty() {
        return None;
    }
    let dbg = std::env::var("TACTUS_DEBUG_FORMC").is_ok();
    if dbg {
        eprintln!(
            "[formc] ENTER core={} hyps={} ant={}",
            crate::lean_pp::pp_expr(core),
            hyps.len(),
            ant_props.len()
        );
    }
    // Normalization substs: the goal's own lets (wrap path) PLUS the
    // N1 hoist-equations (hoisted path — the tmp binders are binder
    // equations there, applied by the script's SubstHoists move).
    let mut substs: Vec<(String, Expr)> = let_substs.to_vec();
    let mut hoist_names: Vec<String> = Vec::new();
    for h in hyps {
        if let HypProvenance::HoistEq { binder } = &h.prov {
            if let ExprNode::BinOp { op: crate::lean_ast::BinOp::Eq, lhs, rhs } = &h.prop.node {
                if matches!(&lhs.node, ExprNode::Var(n) if n.as_str() == binder.as_str()) {
                    substs.push((binder.as_str().to_string(), rhs.as_ref().clone()));
                    hoist_names.push(h.name.clone());
                }
            }
        }
    }
    // Candidates: (name, normalized proposition pp). Antecedent hyps
    // first (the freshest facts — the user's own calls), then shape
    // hyps. Normalization = the substs the script applies at proof
    // time (IntroSubst on the wrap path, SubstHoists on the hoisted
    // path) — the author compares against exactly those forms.
    let mut cands: Vec<(String, String)> = Vec::new();
    for (n, p) in ant_props {
        cands.push((n.clone(), crate::lean_pp::pp_expr(&apply_let_substs(p, &substs))));
    }
    for h in hyps {
        cands.push((
            h.name.clone(),
            crate::lean_pp::pp_expr(&apply_let_substs(&h.prop, &substs)),
        ));
    }
    let norm_core = crate::lean_pp::pp_expr(&apply_let_substs(core, &substs));
    // Split the goal into top-level conjuncts (right-nested ∧).
    let mut conjuncts: Vec<&Expr> = Vec::new();
    let mut c = core;
    loop {
        match &c.node {
            ExprNode::BinOp { op: crate::lean_ast::BinOp::And, lhs, rhs } => {
                conjuncts.push(lhs.as_ref());
                c = rhs;
            }
            _ => {
                conjuncts.push(c);
                break;
            }
        }
    }
    let norm_conj: Vec<String> =
        conjuncts.iter().map(|e| crate::lean_pp::pp_expr(&apply_let_substs(e, &substs))).collect();
    // Every conjunct must have an exact candidate — partial matches
    // are no script (the derived chain gets the whole thing).
    let mut exacts: Vec<String> = Vec::new();
    for nc in &norm_conj {
        let mut found: Option<String> = None;
        for (n, cp) in &cands {
            if cp == nc {
                found = Some(n.clone());
                break;
            }
        }
        if found.is_none() && std::env::var("TACTUS_DEBUG_FORMC").is_ok() {
            eprintln!("[formc] DECLINE conjunct: {nc}");
            for (n, cp) in &cands {
                eprintln!("[formc]   cand {n}: {cp}");
            }
        }
        exacts.push(found?);
    }
    let _ = norm_core;
    let mut moves: Vec<Move> = spine_moves.to_vec();
    // On the hoisted path the tmp binders are binder equations: apply
    // them before the exact close, or the goal still has tmps.
    if !hoist_names.is_empty() {
        moves.push(Move::SubstHoists(hoist_names));
    }
    let close = match exacts.as_slice() {
        [h] => Move::ExactHyp(h.clone()),
        [h1, h2] => Move::RefineExact(vec![h1.clone(), h2.clone()]),
        _ => return None,
    };
    moves.push(close);
    debug_assert!(script_names_resolve(&moves, shape, dts));
    let _ = goal;
    Some(moves)
}

/// Does the expression mention any of the unfold names as an
/// application head or a bare reference?
fn mentions_any_unfold(goal: &Expr, unfolds: &[String]) -> bool {
    fn go(e: &Expr, unfolds: &[String], found: &mut bool) {
        if *found {
            return;
        }
        match &e.node {
            ExprNode::App { head, args } => {
                if let ExprNode::Var(n) = &head.node {
                    if unfolds.iter().any(|u| u == n.as_str()) {
                        *found = true;
                        return;
                    }
                }
                for a in args {
                    go(a, unfolds, found);
                }
            }
            ExprNode::Var(n) => {
                if unfolds.iter().any(|u| u == n.as_str()) {
                    *found = true;
                }
            }
            _ => e.for_each_child(|c| go(c, unfolds, found)),
        }
    }
    let mut found = false;
    go(goal, unfolds, &mut found);
    found
}

/// The hyps (shape hyps + script-named antecedents) whose proposition
/// mentions an unfold name — the `simp … at ⊢ <targets>` list.
fn hyps_mentioning_any_unfold(
    hyps: &[ShapeHyp],
    ant_props: &[(String, Expr)],
    unfolds: &[String],
) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for (n, p) in ant_props {
        if mentions_any_unfold(p, unfolds) {
            out.push(n.clone());
        }
    }
    for h in hyps {
        if mentions_any_unfold(&h.prop, unfolds) {
            out.push(h.name.clone());
        }
    }
    out
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
    // Names the script itself introduces (spine intros / let substs)
    // are visible after their intro move.
    for m in moves {
        match m {
            Move::Intros(ns) => {
                for n in ns {
                    if n != "_" {
                        visible.insert(n.clone());
                    }
                }
            }
            Move::IntroSubst(n) => {
                visible.insert(n.clone());
            }
            _ => {}
        }
    }
    for m in moves {
        let cited: Vec<&str> = match m {
            Move::SubstHoists(ns) | Move::GuardSimp(ns) | Move::GuardSimpStar(ns) => {
                ns.iter().map(|s| s.as_str()).collect()
            }
            Move::ExactHyp(h) => vec![h.as_str()],
            Move::RefineExact(hs) => hs.iter().map(|s| s.as_str()).collect(),
            Move::UnfoldSet(fs) => fs.iter().map(|s| s.as_str()).collect(),
            Move::UnfoldSetTargeted(fs, _) => fs.iter().map(|s| s.as_str()).collect(),
            Move::LeafSimpOnlyOmega(fs) => fs.iter().map(|s| s.as_str()).collect(),
            Move::StructuralTail(fs, _) => fs.iter().map(|s| s.as_str()).collect(),
            Move::UnfoldOnce(f) => vec![f.as_str()],
            Move::Intros(_) | Move::IntroSubst(_) | Move::Defeq | Move::Done | Move::LeafClose => {
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
                || crate::tactic_select::ITE_COLLAPSE_LEMMAS.contains(c)
                || crate::tactic_select::LEG_SIMP_LEMMAS.contains(c)
                || crate::tactic_select::TERM_SIMP_LEMMAS.contains(c)
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

/// R1 defeq bridge: the goal core is a raw comparison (Eq/Le/Lt/Ne)
/// and some shape hyp is a two-arg class-projection application
/// (`eqv a b`, `le a b`, `lt a b`) whose both argument atoms occur in
/// the goal. For concrete instances with inlined bodies (Rational's
/// cross-multiplied eqv/le/lt), `exact h` closes by defeq through the
/// instance projection; for abstract instances the goal could never
/// be a raw comparison, so the check can't misfire. A miss is caught
/// by the derived chain.
fn find_defeq_bridge(core: &Expr, hyps: &[ShapeHyp], dts: &DtDefInventory) -> Option<String> {
    use crate::lean_ast::BinOp;
    if !matches!(&core.node, ExprNode::BinOp {
        op: BinOp::Eq | BinOp::Le | BinOp::Lt | BinOp::Ge | BinOp::Gt | BinOp::Ne, ..
    }) {
        return None;
    }
    let goal_vars = collect_var_names(core);
    for h in hyps {
        let prop = peel_annots(&h.prop);
        if let ExprNode::App { head, args } = &prop.node {
            if let ExprNode::Var(n) = &head.node {
                if dts.trait_methods.contains(n.as_str()) && args.len() == 2 {
                    let a = peel_annots(&args[0]);
                    let b = peel_annots(&args[1]);
                    if let (ExprNode::Var(x), ExprNode::Var(y)) = (&a.node, &b.node) {
                        if goal_vars.contains(x.as_str()) && goal_vars.contains(y.as_str()) {
                            return Some(h.name.clone());
                        }
                    }
                }
            }
        }
    }
    None
}

fn peel_annots(mut e: &Expr) -> &Expr {
    loop {
        match &e.node {
            ExprNode::SpanMark { inner, .. } => e = inner,
            ExprNode::TypeAnnot { expr, .. } => e = expr,
            _ => return e,
        }
    }
}

fn collect_var_names(e: &Expr) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    match &e.node {
        ExprNode::Var(n) => {
            out.insert(n.as_str().to_string());
        }
        _ => e.for_each_child(|c| {
            out.extend(collect_var_names(c));
        }),
    }
    out
}
