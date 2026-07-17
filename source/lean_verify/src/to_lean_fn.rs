//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use vir::ast::*;
use crate::lean_ast::{
    and_all, Axiom, Binder as LBinder, BinderKind, Command, Datatype, Instance, InstanceMethod,
    DatatypeKind, Def, Expr as LExpr, Field,
    MatchArm, Pattern as LPattern, Theorem, Tactic, Variant,
};
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

// The trait/class/instance subsystem lives in `trait_emit.rs`
// (REFACTORING2 § 1.3 extraction). Re-exported here so external call
// paths (`to_lean_fn::trait_to_ast`, …) and the `use super::*` unit
// tests keep working unchanged.
pub use crate::trait_emit::{compute_trait_outparams, trait_impl_to_ast, trait_to_ast};
pub(crate) use crate::trait_emit::trait_bounds_to_ast;

// ── Shared constants ────────────────────────────────────────────────────

/// Auto-tactic used for the proof slot of `⟨witness, _⟩` pairs emitted
/// as instance method bodies for non-unit-return proof-fn trait methods.
/// `rfl` closes when the witness expression matches the ensures' RHS
/// literally; `simp_all` handles unfolding through standalone def chains.
/// Used in both `trait_to_ast` (class default) and `trait_impl_to_ast`
/// (instance body) — extract here so phrasing changes propagate to
/// both sites at once.
pub(crate) const SUBTYPE_WITNESS_AUTO_PROOF: &str = "first | rfl | simp_all";

/// Fallback tactic when `tactic_bodies` lookup misses for a proof-fn
/// trait method. Lean accepts `sorry` with a warning rather than a
/// hard error, preserving the "soundness escape hatch with surfaced
/// signal" model — but in practice every proof fn with `tactic_span`
/// should be readable, so the fallback is defensive only.
pub(crate) const TACTIC_BODY_FALLBACK: &str = "sorry";

/// `decreasing_by` tactic for recursive spec/proof fns whose `decreases`
/// measure produces an obligation Lean's default `decreasing_tactic`
/// can't discharge on its own.
///
/// **This is termination-replay, not verification.** Verus's own
/// `decreases` checker already certified termination before Tactus ran;
/// this clause only re-establishes that fact for Lean's kernel so it
/// accepts the recursive `def`/`theorem`. It is visible in the generated
/// `.lean` and is the same substrate-class machinery as `termination_by`
/// itself and the datatype `height` fn's `decreasing_by` (which uses a
/// `simp_all; omega` variant for its `sizeOf`-with-`.deref` goals).
///
/// The branches, tried in order via `first` (which backtracks cleanly on
/// a failed branch — including branches whose head *name doesn't exist*
/// in this crate's emission, verified empirically, so the seq-companion
/// branches are safe to include unconditionally):
/// - `omega` — linear-arithmetic measures: `(n - 1) < n` (fact/pow/fib),
///   Nat-subtraction (`(a - b) + b < a + b`, subtractive Euclid).
/// - `apply Nat.mod_lt <;> omega` — the **modular** obligation `a % b < b`
///   (Euclidean gcd), which `omega` *cannot* prove because the divisor
///   `b` is a variable, not a literal. `apply` leaves the side goal
///   `b > 0`, which `omega` discharges from the `¬ b = 0` branch guard.
/// - `apply Nat.div_lt_self <;> omega` — the **division** obligation
///   `a / b < a` (base-conversion loops); side goals `0 < a`, `1 < b`
///   close from the branch guards.
/// - `apply Nat.div_lt_self <;> (simp_all <;> omega)` — SAME division
///   obligation, but for a fn whose branch guard reaches the termination
///   context wrapped in an `ite`/`dite` over `Prop` (a Prop-valued
///   recursive spec fn like `numbers_word`: `if alpha = 0 then True else
///   if m ≤ 1 then False else … ∧ recurse (alpha/m)` hands the goal a
///   single combined hyp `h✝ : ¬if x : alpha = 0 then True else m ≤ 1`).
///   `omega` alone can't read `0 < alpha` / `1 < m` out of that Prop-ite;
///   `simp_all` first decomposes the negated ite into plain arithmetic,
///   then `omega` closes. Added as its OWN rung after the plain-`omega`
///   div rung so the cheap clean-hypothesis path is unchanged and the
///   other measures are untouched (bootstrap-44). Verified against the
///   real emitted `word_numbering` defs part.
/// - `apply Seq.subrange_tail_len_lt <;> …` — **drop-k seq measures**
///   `len (subrange u j (len u)) < len u` for any `j ≥ 1` (bootstrap-46).
///   A raw `subrange u k (len u)` recursion (k ≠ 1, so NOT routed through
///   `drop_first`) — e.g. `m3_blinker.ffnf` recursing on
///   `subrange u 2 (len u)` — has no `drop_{first,last}` head to unify, so
///   it dispatches to this GENERAL companion (emitted once beside the
///   drop_first companion, see `seq_subrange_tail_companion_cmd` in
///   `generate.rs`). `apply` unifies `j` from the literal subrange start and
///   leaves side goals `1 ≤ j` (omega) and `j ≤ len u` (from the nested
///   dite guard `len u ≥ k`, closed by the same
///   `assumption`/`omega`/`(simp_all <;> omega)`/`simp_all` ladder as the
///   drop_first rung). Placed BEFORE the drop_first rung; heads are disjoint
///   (`subrange` vs `Seq.drop_first`) so ordering is immaterial to
///   correctness.
/// - `apply Seq.drop_{first,last}_len_lt <;> …` — vstd **seq measures**
///   `len (drop_first w) < len w`: dispatches to the measure-companion
///   theorem emitted next to the corresponding def (see
///   `seq_measure_companion_cmd` in `generate.rs`; B3 in
///   DESIGN-lean-all-proofs-bugs.md). The side goal `¬ len w = 0` closes
///   from the branch guard via `assumption`/`omega`/`(simp_all <;> omega)`/
///   `simp_all` — `omega` for arithmetic guards (`3 ≤ len w` under F2c's
///   wf_preprocess threading, which assumption/simp_all can't bridge). The
///   `(simp_all <;> omega)` rung (bootstrap-45) handles the case where the
///   THEN-branch guard reaches the termination context as a Bool-wrapped
///   `decide (len w > 0 ∧ …) = true` hypothesis (a conjunction-guarded
///   recursive spec fn like `m1_guard.lead`, whose guard elaborates to a
///   `decide … = true` under the in-gate ambient env's Decidable-instance
///   resolution): `omega` cannot read `0 < len w` out of an opaque
///   `decide … = true`, and the bare `simp_all` fallback DECODES the decide
///   into a plain conjunction but then STOPS (it made progress yet did not
///   close the arithmetic goal `¬ len w = 0` — and being the last `first`
///   alternative, `first` accepts that partial success and leaves the goal
///   unsolved). `(simp_all <;> omega)` decodes+normalizes with `simp_all`,
///   THEN closes with `omega` — the same shape as the div-rung Prop-`ite`
///   fix (bootstrap-44), now applied to the seq-companion rungs. Placed
///   BEFORE the bare `simp_all` so the cheap `assumption`/`omega` clean
///   path is unchanged and only genuine decide-wrapped guards fall through.
///   In a crate that never emits the def/companion the `apply` head is
///   unknown and the branch just fails over.
/// - `(repeat split) <;> omega` — **Int-typed measures** (F2b,
///   DESIGN-lean-all-proofs-followons.md): with `wrap_int_measure`'s
///   `Int.toNat` embedding, an Int-abs measure (`if 0 ≤ t then t else
///   -t`) yields goals with value-position ifs on both sides; `split`
///   is deterministic (ite/match only) and bounded by the ifs present,
///   then `omega` closes over the branch guards + `Int.toNat`.
/// - `decreasing_tactic` — Lean's default, kept as a final fallback so
///   spec fns recursing on a structural / `sizeOf` / datatype-height
///   measure (which no earlier branch handles) terminate exactly as
///   they do today (those currently pass via the implicit default).
///
/// Tested against Lean 4.25.0 (BUG-spec-fn-decreases-mod-termination.md;
/// div + seq branches: /tmp-prototype validation 2026-07-09, B3).
/// Built per-call rather than a const: the seq companion names must be
/// FULLY QUALIFIED (`{ns}.Seq.drop_first_len_lt`) under Option B naming.
/// The bare `Seq.drop_first_len_lt` form only resolved via Lean's
/// declaration-namespace walk (a decl named `lib.m.f` elaborates as-if
/// inside `namespace lib.m`, so relative names try `lib.m.Seq.…` then
/// `lib.Seq.…`) — verified empirically 2026-07-11. That implicit walk is
/// a capture surface (a crate module named `Seq` would shadow the
/// companion), so the rung cites the absolute name like every other
/// emitted reference. `crate_ns() == None` (ns-less unit-test renders)
/// keeps the bare form.
thread_local! {
    /// Names of length-monotonicity companions (`{fn}_len_le`,
    /// bootstrap-47) emitted so far in the current defs build.
    /// `decreasing_by_tactic` splices a `Nat.lt_of_le_of_lt` chaining rung
    /// citing these so a NESTED suffix measure like
    /// `len (drop_base_run (drop_first W)) < len W` (m3_blinker.split_q)
    /// closes: the `≤` subgoal unifies one of these monos, the `<` subgoal
    /// unifies the `drop_first` companion. Populated by the defs loop as
    /// each suffix-recursive spec fn's companion lands (dep-order emits a
    /// consumer AFTER the companions it needs). Cleared per emission entry
    /// (`generate::install_emit_tables`), so per-fn proof/exec files never
    /// inherit a prior build's names. Read here as a GROWING BAG —
    /// `first | apply m1 | apply m2 | …` offloads the "which mono?" choice
    /// to Lean unification (only the mono whose `≤`-head matches fires;
    /// names not imported in a given file fail over harmlessly inside
    /// `first`, exactly like the existing seq-companion rungs).
    static SUFFIX_MONO_NAMES: std::cell::RefCell<Vec<String>> =
        std::cell::RefCell::new(Vec::new());
}

/// Reset the suffix-mono companion bag (bootstrap-47). Called from
/// `generate::install_emit_tables`, the single choke point every emission
/// entry routes through — so each defs build starts empty and per-fn
/// proof/exec files never cite a prior build's companion names.
pub(crate) fn clear_suffix_mono_names() {
    SUFFIX_MONO_NAMES.with(|s| s.borrow_mut().clear());
}

/// Register a length-monotonicity companion name so later fns'
/// `decreasing_by` can cite it in the chaining rung (bootstrap-47). Deduped
/// (idempotent); order is the dep-order emission order, which is
/// deterministic, keeping the emitted `decreasing_by` strings stable
/// across runs (cache-friendly).
pub(crate) fn register_suffix_mono_name(name: String) {
    SUFFIX_MONO_NAMES.with(|s| {
        let mut v = s.borrow_mut();
        if !v.contains(&name) {
            v.push(name);
        }
    });
}

fn decreasing_by_tactic() -> String {
    let q = |n: &str| match crate::to_lean_type::crate_ns() {
        Some(ns) => format!("{}.{}", ns, n),
        None => n.to_string(),
    };
    // bootstrap-47: chaining rung for NESTED suffix measures
    // (`len (g (drop_first W)) < len W`, g length-non-increasing). Spliced
    // ONLY when ≥1 mono companion is in scope, so files without any keep
    // their exact prior `decreasing_by` string (no cache churn).
    // `apply Nat.lt_of_le_of_lt` splits `a < c` into `a ≤ ?b` and `?b < c`;
    // `<;>` runs the inner `first` on both — a mono closes the `≤` subgoal
    // (binding `?b := len (drop_first W)`), the `drop_first` companion
    // closes the `<`. Placed LAST before `decreasing_tactic`: its outer
    // `apply Nat.lt_of_le_of_lt` matches ANY `_ < _` goal (not head-
    // disjoint), so simple direct-measure goals must reach their own rungs
    // first; only genuinely-nested goals fall through to here.
    let chain_rung = SUFFIX_MONO_NAMES.with(|s| {
        let monos = s.borrow();
        if monos.is_empty() {
            String::new()
        } else {
            let applies: String = monos.iter()
                .map(|m| format!("apply {} | ", m))
                .collect();
            format!(
                " | (apply Nat.lt_of_le_of_lt <;> (first | {applies}(apply {df} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all))))",
                df = q("Seq.drop_first_len_lt"),
            )
        }
    });
    format!(
        "all_goals (first | omega | (apply Nat.mod_lt <;> omega) | (apply Nat.div_lt_self <;> omega) | (apply Nat.div_lt_self <;> (simp_all <;> omega)) | (apply {ds} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all)) | (apply {df} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all)) | (apply {dl} <;> (first | assumption | omega | (simp_all <;> omega) | simp_all)) | ((repeat split) <;> omega){chain_rung} | decreasing_tactic)",
        ds = q("Seq.subrange_tail_len_lt"),
        df = q("Seq.drop_first_len_lt"),
        dl = q("Seq.drop_last_len_lt"),
    )
}

/// True when this param needs a body shadow because the shadow is
/// load-bearing for the **mutation encoding** — `*x = e` lowers to
/// `let x := e` in Lean, requiring `x` to be at the inner-typ level
/// throughout the body.
///
/// Post-U2 (wrapper-arch use-site coercion): `&`-only reference
/// decorations (Ref/Box/Rc/Arc) do NOT need a shadow. The renderer's
/// bidirectional `apply_ref_coercion_if_needed` inserts `.deref`
/// chains at use sites that expect inner-typed values, and `Tactus.X.mk`
/// wraps at use sites that expect wrapper-typed. The shadow was the
/// "always strip, then re-wrap on demand" approach; the post-U2
/// renderer handles strip + wrap symmetrically at use sites, so the
/// shadow is unnecessary clutter for read-only references.
///
/// Mutation-encoding cases (legacy `is_mut: true`, new-mode `MutRef<T>`,
/// `Decorate(MutRef, _, _)`, plus BorrowMut locals) DO need shadow:
/// the `let x := e` mutation lowering requires `x`'s Lean type to
/// match `e`'s inner-value type so the shadow composes.
pub(crate) fn needs_param_deref(p: &Param) -> bool {
    crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut)
}

/// Wrap a body expression with `let p := p.deref` for each param whose
/// Lean binder is wrapper-typed, so the body sees `p` as the inner type.
/// Lean's shadowing means the binder `(p : Tactus.Ref T)` survives at
/// the param position (for dispatch) while the body's references to `p`
/// resolve to the derefed inner.
///
/// Non-wrapped params pass through unchanged.
///
/// Applied at every site that emits a body containing references to
/// reference-decorated params: spec_fn_to_ast standalone defs,
/// trait_impl_to_ast instance method bodies, trait_to_ast class default
/// bodies, proof_fn_to_ast requires/ensures.
/// True iff the decreases measure is exactly one bare parameter whose
/// (decoration-stripped) typ is a user datatype — the shape Lean's
/// `termination_by structural` accepts: structural (subterm) recursion
/// on that param, with Lean itself checking each recursive call. Nat/
/// Int measures (`decreases n` with `(n-1) as nat` recursion) and
/// computed measures (`decreases len(s) - i`) are NOT structural and
/// keep WF emission.
fn structural_measure_is_bare_datatype_param(decrease: &Exprs, params: &Params) -> bool {
    if decrease.len() != 1 {
        return false;
    }
    let v = match &decrease[0].x {
        ExprX::ReadPlace(place, _) => match &place.x {
            PlaceX::Local(v) => v,
            _ => return false,
        },
        ExprX::Var(v) => v,
        _ => return false,
    };
    // UNDECORATED datatype only: a `&Tree`-typed param binds at
    // `Tactus.Ref Tree` in Lean, and structural inference on a
    // one-field-structure-wrapped binder is not a shape we've
    // validated — decorated params keep WF emission (silent, like
    // every other unsupported measure).
    params.iter().any(|p| {
        p.x.name == *v && matches!(&*p.x.typ, TypX::Datatype(..))
    })
}

pub(crate) fn wrap_body_with_param_derefs(body: LExpr, params: &Params) -> LExpr {
    // Iterate in REVERSE so the FIRST param's let-binding ends up
    // outermost (after building the wrap by repeatedly prepending).
    let mut wrapped = body;
    for p in params.iter().rev() {
        if needs_param_deref(p) {
            let param_name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
            wrapped = LExpr::let_bind(
                param_name.clone(),
                LExpr::field_proj(LExpr::var(param_name), "deref"),
                wrapped,
            );
        }
    }
    wrapped
}

// ── Source map ──────────────────────────────────────────────────────────

/// Maps Lean line numbers back to the user's source.
///
/// Proof fns and exec fns use different mapping mechanisms — the
/// enum split makes the dichotomy explicit instead of having one
/// struct with conditionally-meaningful fields.
#[derive(Clone)]
pub enum LeanSourceMap {
    /// Proof fns: the user-written tactic body starts at
    /// `tactic_start_line` and runs `tactic_line_count` lines.
    /// `find_tactic_line` returns the offset within that block.
    ProofFn {
        fn_name: String,
        /// 1-indexed line in generated `.lean` where the tactic body starts.
        tactic_start_line: usize,
        tactic_line_count: usize,
    },
    /// Exec fns (#51 source mapping): `span_marks` is a list of
    /// landmarks populated by the pp as it visits
    /// `ExprNode::SpanMark` nodes. `find_span_mark` returns the
    /// closest preceding obligation-kind mark for a given Lean
    /// error line.
    ExecFn {
        fn_name: String,
        span_marks: Vec<crate::lean_pp::SpanMarkLandmark>,
    },
}

impl LeanSourceMap {
    /// Proof-fn path: 1-indexed offset within the tactic body for
    /// a given Lean line number, or `None` outside the body.
    pub fn find_tactic_line(&self, lean_line: usize) -> Option<usize> {
        match self {
            LeanSourceMap::ProofFn { tactic_start_line, tactic_line_count, .. } => {
                let end = tactic_start_line + tactic_line_count;
                if lean_line >= *tactic_start_line && lean_line < end {
                    Some(lean_line - tactic_start_line)
                } else {
                    None
                }
            }
            LeanSourceMap::ExecFn { .. } => None,
        }
    }

    /// Exec-fn path: closest preceding **obligation-kind**
    /// `SpanMarkLandmark` for a Lean error line. Returns `None`
    /// for proof-fn maps or when no obligation-kind mark
    /// precedes the line.
    ///
    /// Structurally exact for per-obligation theorems (D, Stages
    /// 1-4): each theorem has exactly one "obligation mark" at
    /// the innermost (latest, in source order) position of its
    /// goal. Hypothesis-kind marks (LoopCondition for the
    /// loop's cond, BranchCondition for an `if`'s cond) appear
    /// earlier in the goal but are filtered out here via
    /// `AssertKind::is_obligation_kind` — they exist for the
    /// `/- @rust:LOC -/` comments in the generated `.lean`
    /// (visual debugging) but never fire as error labels.
    /// Lean's `pos.line` for a failure points at the theorem's
    /// tactic invocation, which is just after the goal; the
    /// closest preceding obligation mark is therefore the
    /// obligation mark for that theorem, with the right
    /// `AssertKind` for the failing obligation.
    pub fn find_span_mark(&self, lean_line: usize) -> Option<&crate::lean_pp::SpanMarkLandmark> {
        match self {
            LeanSourceMap::ExecFn { span_marks, .. } => {
                span_marks.iter()
                    .rev()
                    .find(|m| m.line <= lean_line && m.kind.is_obligation_kind())
            }
            LeanSourceMap::ProofFn { .. } => None,
        }
    }
}

// ── Spec fn ─────────────────────────────────────────────────────────────

/// Build a top-level command for a spec fn. Returns `Command::Def`
/// when the fn has a body, `Command::Axiom` when it doesn't.
///
/// Body-less cases that route through the Axiom branch:
/// - `pub uninterp spec fn` (deliberately uninterpreted on the Verus side).
/// - `external_body` spec fns (Verus's escape hatch for FFI/spec gaps).
/// - Cross-crate spec fns whose body was stripped at `export_crate` time
///   (private or closed specs from imported crates).
///
/// Lean's `axiom` is the right encoding: it declares a constant whose
/// value is unspecified, matching Verus's "this is just a symbol with
/// a type" semantics. (The previous `def ... := sorry` shape was dead
/// code, unreachable because dep_order's `build_spec_fn_map` filtered
/// body=None fns out — which produced "unresolved" sanity-check
/// rejections at the call site. Audit 2026-05-12 unfiltered the map
/// and routes through `Axiom` here.)
/// Uninterpreted signature axiom for a spec fn whose BODY has no Lean
/// form (`BuiltinSpecFun` — closure `call_requires`/`call_ensures`
/// etc.). Emitting the signature keeps DEPENDENT spec fns renderable
/// (e.g. vstd's `cloned` references `strictly_cloned`; skipping the
/// def poisons every reference with unknown-identifier). Restricted
/// to Prop-returning fns: a Prop-valued function type is inhabited by
/// `fun … => True`, so the axiom is unconditionally conservative — no
/// Nonempty premise needed. Non-Prop builtin-bodied fns keep the skip
/// (their value axiom would need the nonempty machinery's premises).
pub fn builtin_spec_fn_signature_axiom(
    f: &FunctionX,
    ectx: &crate::emit_ctx::EmitCtx,
) -> Option<Command> {
    if !matches!(&*f.ret.x.typ, vir::ast::TypX::Bool) {
        return None;
    }
    Some(Command::Axiom(Axiom {
        name: lean_name(&f.name.path),
        binders: fn_binders_without_bound_hyps(f, &ectx.unemittable),
        ret_ty: typ_to_expr(&f.ret.x.typ),
        attrs: vec![],
        comment: Some(
            "uninterpreted: body is a BuiltinSpecFun with no Lean form; \
             Prop-valued fn types are inhabited, so this is conservative"
                .to_string(),
        ),
    }))
}

pub fn spec_fn_to_ast(f: &FunctionX, ectx: &crate::emit_ctx::EmitCtx) -> Vec<Command> {
    // Spec fns are Lean defs (mathematical definitions). The
    // u-type / i-type refinement bounds belong on theorems
    // (proof fns + exec fn obligations), not on the spec fn's
    // signature — including them would change the spec fn's
    // type from `Int → Int` to `Int → Bound → Int` and break
    // call sites that pass only the value. Surfaced 2026-05-09
    // by `test_diag_exec_plain_assert_with_spec_call` (#147).
    let binders = fn_binders_without_bound_hyps(f, &ectx.unemittable);
    let ret_ty = typ_to_expr(&f.ret.x.typ);
    let name = lean_name(&f.name.path);
    // `#[verifier::tactus_lean_axiom_eq]`: emit an uninterpreted value
    // axiom PLUS a defining-equation axiom named `<f>.eq_def`, instead
    // of a Lean def. For recursive spec fns whose termination goal
    // Lean's decreasing_by can't discharge (e.g. Seq-recursion via
    // `drop_first`, whose measure fact `len (subrange s 1 len) < len s`
    // is a broadcast axiom emitted AFTER the def in the preamble
    // layout). SOUND: Verus verified the fn's termination Z3-side
    // (SpecTermination query), so the defining equation has a model —
    // the same stipulation shape as broadcast axioms. The `.eq_def`
    // name matches Lean's auto-generated equation for real defs, so
    // proof-block tactics (`rw [f.eq_def]`) are uniform across both
    // emissions. The value axiom rides nonempty.rs Seed 2 like any
    // bodyless spec fn (via `spec_fn_emits_as_axiom`).
    if f.attrs.tactus_lean_axiom_eq {
        if let Some(b) = &f.body {
            let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
            let body = wrap_body_with_param_derefs(
                crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &binder_ctx, &crate::expr_shared::RenderCtx::empty()),
                &f.params,
            );
            let value_axiom = Command::Axiom(Axiom {
                name: name.clone(),
                binders: binders.clone(),
                ret_ty: ret_ty.clone(),
                attrs: vec![],
                comment: Some(
                    "#[verifier::tactus_lean_axiom_eq]: value axiom + defining equation below; \
                     termination was verified by Verus (Z3) — see the attribute's doc"
                        .to_string(),
                ),
            });
            // LHS: f applied to every named non-instance binder (typ
            // params + value params, in binder order). Instance binders
            // ([Nonempty A]) resolve implicitly at the application.
            let applied = crate::lean_ast::Expr::app(
                crate::lean_ast::Expr::var(crate::lean_name::LeanName::synthetic(name.clone())),
                binders.iter()
                    .filter(|bi| !matches!(bi.kind, crate::lean_ast::BinderKind::Instance))
                    .filter_map(|bi| bi.name.clone())
                    .map(crate::lean_ast::Expr::var)
                    .collect(),
            );
            let eq_body = crate::lean_ast::Expr::binop(
                crate::lean_ast::BinOp::Eq, applied, body,
            );
            let eq_axiom = Command::Axiom(Axiom {
                name: format!("{}.eq_def", name),
                binders,
                ret_ty: eq_body,
                attrs: vec![],
                comment: None,
            });
            return vec![value_axiom, eq_axiom];
        }
    }
    // Bodies containing `CallTarget::BuiltinSpecFun` fall back to the
    // Axiom branch — see `expr_shared::spec_fn_emits_as_axiom`.
    let body = if crate::expr_shared::spec_fn_emits_as_axiom(f) { &None } else { &f.body };
    match body {
        Some(b) => {
            let attrs = if matches!(f.opaqueness, Opaqueness::Opaque) {
                vec!["irreducible".into()]
            } else {
                vec![]
            };
            // `uN -> nat` casts are kept as `Clip{Nat}` by Verus's
            // `--lean-backend` lowering (replaces the old `nat_coercion`
            // pre-pass), so the rendered VIR is already Lean-typed.
            let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
            // Self-calls render as the full dotted name (Option B —
            // resolves fine mid-declaration at root scope, the
            // `List.myLen` idiom; relative-rendering machinery retired).
            let body = wrap_body_with_param_derefs(
                crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &binder_ctx, &crate::expr_shared::RenderCtx::empty()),
                &f.params,
            );
            let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| {
                crate::expr_shared::wrap_int_measure(
                    crate::to_lean_expr::vir_expr_to_ast_with_binders(d, &binder_ctx, &crate::expr_shared::RenderCtx::empty()),
                    d,
                )
            }).collect();
            // `#[verifier::structural_decreases]`: emit
            // `termination_by structural <param>` (kernel-computable,
            // axiom-free) when the measure is a bare datatype-typed
            // param; Lean itself checks that every recursive call
            // passes a subterm. Unsupported measure shapes fall back
            // to WF emission with a note — never a hard failure
            // (DESIGN-bootstrap.md W1.5).
            let termination_structural = f.attrs.tactus_structural_decreases
                && !termination_by.is_empty()
                && structural_measure_is_bare_datatype_param(&f.decrease, &f.params);
            // Recursive spec fns get an explicit `decreasing_by` so measures
            // Lean's default tactic can't discharge (notably the modular
            // `a % b < b` of Euclidean gcd) still verify. Non-recursive defs
            // (empty `termination_by`) get `None` — a bare `decreasing_by`
            // without `termination_by` is a Lean error. See DECREASING_BY_TACTIC.
            let decreasing_by = (!termination_by.is_empty() && !termination_structural)
                .then(decreasing_by_tactic);
            vec![Command::Def(Def { attrs, name, binders, ret_ty, body, termination_by, termination_structural, decreasing_by })]
        }
        None => {
            // Transparency: when the fallback DROPPED a body (vs. the fn
            // being genuinely bodyless), the artifact says so — the
            // reader should never have to guess why a def is an axiom.
            let comment = (f.body.is_some()).then(|| format!(
                "body contains `call_ensures`/`call_requires` (no Lean encoding); \
                 axiomatized signature — see expr_shared::spec_fn_emits_as_axiom"
            ));
            vec![Command::Axiom(Axiom { name, binders, ret_ty, attrs: vec![], comment })]
        }
    }
}

// ── Proof fn ────────────────────────────────────────────────────────────

/// Build a `Theorem` AST node for a proof fn with the given tactic text.
///
/// `fn_map` is consulted to insert `Int.toNat` coercions at Call sites
/// where args render as Lean `Int` but the callee's params render as
/// Lean `Nat` (BUG-as-nat-cast.md). Pass an empty map if no fn-map
/// info is available; the only effect is that uncoerced Int → Nat
/// calls would fail Lean elaboration (matching the pre-fix state).
/// Build the `(binders, goal)` signature for a proof fn: typ-param +
/// value-param + bound-hyp binders (`fn_binders`), each `require` as an
/// explicit `(h<i> : req)` hypothesis binder, and the conjoined
/// `ensure` clauses as the goal. Both `require` and `ensure` get
/// nat-coercion insertion + `let p := p.deref` ref-decoration wrapping.
///
/// Shared by `proof_fn_to_ast` (wraps it in a `Theorem` with the user's
/// tactic body) and `broadcast_lemma_axiom_cmd` (wraps it in a
/// `Command::Axiom` — no proof, the lemma is Verus/Z3-certified
/// upstream). Keeping the binder/goal construction in one place means
/// the deref-wrapping + nat-coercion treatment can't drift between the
/// two emission paths.
fn proof_fn_signature(
    f: &FunctionX,
    ectx: &crate::emit_ctx::EmitCtx,
) -> (Vec<LBinder>, LExpr) {
    let mut binders = fn_binders(f, &ectx.unemittable);
    let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
    // Render with the fn_map in scope so the call-arg bridge can look up
    // each callee's param types (instantiated with the call's typ_args)
    // and coerce — e.g. recovering `Box::new(*k)` (erased by Verus to a
    // bare `*k : Q`) as `Tactus.Box.mk k.deref` when the callee's key
    // param instantiates to `Box<Q>`. Without the fn_map, `fn_param_typs`
    // returns None and the bridge is a no-op (the pre-fix behaviour, which
    // left a raw `k.deref : Q` in a `Box Q` slot). `FnMap` and
    // `RenderFnMap` are the same `HashMap<&Fun, &FunctionX>` type.
    let render_ctx = ectx.render_ctx();
    for (i, req) in f.require.iter().enumerate() {
        // Wrap with `let p := p.deref` for ref-decorated params so the
        // hypothesis body sees inner types. (`uN -> nat` casts are kept
        // as `Clip{Nat}` upstream by Verus's `--lean-backend` lowering.)
        let req_ty = wrap_body_with_param_derefs(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(req, &binder_ctx, &render_ctx),
            &f.params);
        binders.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("h{}", i)), req_ty));
    }
    let goal_raw = and_all(f.ensure.0.iter().map(|e| {
        crate::to_lean_expr::vir_expr_to_ast_with_binders(e, &binder_ctx, &render_ctx)
    }).collect());
    let goal = wrap_body_with_param_derefs(goal_raw, &f.params);
    (binders, goal)
}

/// Emit a cross-crate broadcast lemma (`broadcast axiom fn` /
/// `broadcast proof fn`) as a Lean `axiom`. The lemma's body is None
/// in the merged krate (cross-crate-stripped), but its `require` /
/// `ensure` survive — that's the broadcast fact. We emit
/// `axiom <name> <binders> : <∀ params, reqs → ensures>` and trust it
/// the same way DESIGN.md § "Cross-crate spec fn availability"
/// trusts an axiomatized cross-crate ensures: sound assuming the
/// source crate (vstd) verified the lemma, which `vargo build` checks
/// (1530/0). The user opts in explicitly via `broadcast use <group>;`
/// (#122); `collect_broadcast_lemma_funs` resolves the group to its
/// member lemmas, this emits them, and `exec_fn_theorems_to_ast`
/// injects `have _tactus_bc_i := <name>` so the closer can use them.
pub fn broadcast_lemma_axiom_cmd(
    f: &FunctionX,
    ectx: &crate::emit_ctx::EmitCtx,
) -> Command {
    let (binders, goal) = proof_fn_signature(f, ectx);
    Command::Axiom(crate::lean_ast::Axiom {
        comment: None,
        name: lean_name(&f.name.path),
        binders,
        ret_ty: goal,
        attrs: Vec::new(),
    })
}

/// The Lean name of a proof fn's statement def in package emission:
/// `<lean name>_stmt`. Shared by the Stmts renderer (below), the
/// hypothesis binders consumers take (M2), and the Link module (M3) —
/// one chokepoint so the three sites can't disagree on the name.
pub fn stmt_name(path: &Path) -> String {
    format!("{}_stmt", lean_name(path))
}

/// The hypothesis binder a package-mode consumer takes for helper
/// lemma `path` (DESIGN-emit-module.md §4.2): the binder is named by
/// the helper's SHORT name — exactly the identifier raw tactic text
/// references (`have := lemma_a x hx`) — so binder shadowing makes the
/// tactic body elaborate unchanged against the local hypothesis where
/// the island file had a global theorem. The type is the helper's
/// statement def, whose reducibility (M0 finding F2) lets the
/// application elaborate without `unfold`.
pub fn helper_hyp_binder(path: &Path) -> LBinder {
    LBinder::explicit(
        crate::lean_name::LeanName::lit(short_name(path)),
        LExpr::var_lit(&stmt_name(path)),
    )
}

/// Fold a proof fn's `(binders, goal)` signature into one ∀-closed
/// Prop. Zero binders → the bare goal (a nullary lemma's statement is
/// just its conjoined ensures).
fn forall_close(binders: Vec<LBinder>, goal: LExpr) -> LExpr {
    if binders.is_empty() { goal } else { LExpr::forall(binders, goal) }
}

/// Assemble a statement def from an already-built signature:
/// `@[reducible] noncomputable def <name> : Prop := ∀ <binders>, <goal>`.
/// Split from `proof_fn_stmt_cmd` so unit tests can drive it with
/// synthetic binders/goals without constructing a full `FunctionX`.
///
/// `@[reducible]` is load-bearing (DESIGN-emit-module.md M0 finding
/// F2, the `abbrev` form): it lets `intro` peel the stmt name inside
/// the prover, lets a hypothesis `(h : <name>)` be applied to
/// arguments at use sites, and lets the Link module's direct
/// application unify — no `unfold` anywhere. (`noncomputable` is the
/// always-on `write_def` default; harmless on a Prop def.)
fn stmt_cmd(name: String, binders: Vec<LBinder>, goal: LExpr) -> Command {
    Command::Def(Def {
        attrs: vec!["reducible".to_string()],
        name,
        binders: Vec::new(),
        ret_ty: LExpr::var_lit("Prop"),
        body: forall_close(binders, goal),
        termination_by: Vec::new(),
        termination_structural: false,
        decreasing_by: None,
    })
}

/// Emit a proof fn's contract as its statement def — the Stmts layer
/// of package emission (DESIGN-emit-module.md §2.1/§4.1). Consumers
/// take the def as a hypothesis binder instead of citing an axiom or
/// re-elaborating the helper's theorem; the fn's own theorem proves
/// it; the Link module applies one to the other.
///
/// Built on the same `proof_fn_signature` as `proof_fn_to_ast` and
/// `broadcast_lemma_axiom_cmd` (including the same standalone
/// augmentation), so the statement def and the theorem that proves it
/// cannot drift — the statement-identity property the emit-module
/// trust argument rests on.
pub fn proof_fn_stmt_cmd(
    f: &FunctionX,
    ectx: &crate::emit_ctx::EmitCtx,
) -> Command {
    let f = &crate::impl_subst::maybe_augment_standalone_fn(f, &ectx.trait_outparams);
    let (binders, goal) = proof_fn_signature(f, ectx);
    stmt_cmd(stmt_name(&f.name.path), binders, goal)
}

/// Statement def for one EXEC obligation theorem (M6.2): the
/// theorem's ∀-closed goal as a `@[reducible] Prop` def, named
/// `<theorem name>_stmt` (obligation theorem names are already unique
/// per fn). Same `stmt_cmd` shape as proof-fn statement defs, so the
/// M6.3 Link composition treats both uniformly.
pub fn exec_obligation_stmt_cmd(thm: &Theorem) -> Command {
    stmt_cmd(
        format!("{}_stmt", thm.name),
        thm.binders.clone(),
        thm.goal.clone(),
    )
}

pub fn proof_fn_to_ast(
    f: &FunctionX,
    tactic_body: &str,
    ectx: &crate::emit_ctx::EmitCtx,
) -> Theorem {
    // Lift assoc-type projections in the theorem's OWN clauses/binders —
    // the same `maybe_augment_standalone_fn` spec fns, helpers, and
    // broadcast axioms get at their emission sites. Without it a tactic
    // proof fn generic over `A: Getter` whose ensure carries
    // `<A as Getter>::Out` rendered the malformed accessor `Getter.Out A`
    // and an under-applied `[Getter A]` bracket
    // (BUG-vstd-preamble-cluster.md bug 3, root-clause half). Applied here
    // (not per-caller) so the standalone, batch (crate_defs), and helper
    // paths all get it; idempotent when a caller already augmented
    // (`ImplSubst::build` skips slots covered by an existing TypEquality);
    // no-op for projection-free fns.
    let f = &crate::impl_subst::maybe_augment_standalone_fn(f, &ectx.trait_outparams);
    let (binders, goal) = proof_fn_signature(f, ectx);
    let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
    // Honor Verus's `decreases` clause for recursive proof fns. Lean often
    // auto-infers termination for simple structural recursion, but cases
    // where the measure is non-obvious (Collatz, lex pairs, computed
    // descent) require the explicit clause. Mirrors `spec_fn_to_ast`.
    let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| {
        crate::expr_shared::wrap_int_measure(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(d, &binder_ctx, &crate::expr_shared::RenderCtx::empty()),
            d,
        )
    }).collect();
    // Recursive proof fns get the same explicit `decreasing_by` as spec fns,
    // so a measure Lean's default tactic can't discharge (the modular
    // `a % b < b`) still verifies. Gated on non-empty `termination_by` — a
    // bare `decreasing_by` on a non-recursive theorem is a Lean error.
    let decreasing_by = (!termination_by.is_empty())
        .then(decreasing_by_tactic);
    Theorem {
        name: lean_name(&f.name.path),
        binders,
        goal,
        tactic: Tactic::Raw(tactic_body.to_string()),
        requires_preamble: Vec::new(),
        heartbeats: f.attrs.tactus_heartbeats,
        termination_by,
        decreasing_by,
    }
}

// ── Datatype ────────────────────────────────────────────────────────────

/// Emit a datatype declaration plus, for multi-variant inductives,
/// the per-variant discriminator (`Type.is<Variant>`) and accessor
/// (`Type.<Variant>_<field>`) defs that exec-fn match-desugaring
/// references.
///
/// Why accessors: Lean's `structure` auto-derives field accessors
/// (`Point.x`), so single-variant structs work out of the box. But
/// `inductive` doesn't auto-derive per-variant discriminators or
/// field accessors — in Lean you normally pattern-match on the value.
/// Exec fns reach this path because `ast_simplify` lowers `match` to
/// an if-chain built from `UnaryOpr::IsVariant` + `UnaryOpr::Field`,
/// and the desugared form expects accessor fns to exist. So we
/// synthesise them.
///
/// `emit_accessors` controls whether the accessor defs are produced.
/// The exec-fn preamble passes `true` — the desugared if-chain
/// needs them. The proof-fn preamble passes `false` — proof fns
/// render match as native Lean match (spec fns preserve match
/// through to VIR-AST), never reach the desugared Field/IsVariant
/// form, and don't benefit from accessors. More importantly,
/// emitting accessors for datatypes that proof fns reference but
/// whose field types lack `Inhabited` (the accessor's fallback
/// case calls `default`) breaks Lean elaboration even when the
/// accessor is never called.
///
/// Returns an empty `Vec` for `Dt::Tuple` (no declaration needed —
/// tuples are rendered as `T × U` products).
/// Name inventory of the `@[simp]` defs `datatype_to_cmds` /
/// `datatype_group_to_cmds` emit per datatype, for
/// `tactic_select::structural_rung`'s derived unfold lists. MUST
/// mirror the emission naming exactly (discriminators from the
/// `is{Variant}` loop, accessors from `multi_variant_accessor_defs`'
/// `{Variant}_{field_name}` loop, `height` from
/// `datatype_height_cmd`) — a drifted name here surfaces as an
/// unknown-identifier failure of the structural rung (the `first`
/// combinator recovers, so drift degrades to a loud goal failure,
/// never a wrong proof).
///
/// Gates mirrored: external-body datatypes emit no defs (opaque
/// axioms); tuples emit nothing; single-variant STRUCTS (variant
/// named like the type) emit no accessors (they render as Lean
/// `structure` with real projections). `height` is emitted for every
/// declared `Dt::Path` datatype. Over-inclusion relative to the
/// referenced-datatype pruning is harmless: a name only enters a
/// simp list when the goal itself mentions it.
pub(crate) fn datatype_simp_def_inventory(
    datatypes: &[vir::ast::Datatype],
) -> crate::tactic_select::DtDefInventory {
    let mut by_type = std::collections::HashMap::new();
    for d in datatypes.iter() {
        if matches!(d.x.transparency, DatatypeTransparency::Never) {
            continue;
        }
        let (path, short) = match &d.x.name {
            Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
            Dt::Tuple(_) => continue,
        };
        let mut defs: std::collections::HashSet<String> = Default::default();
        defs.insert("height".to_string());
        let is_single_variant_struct =
            d.x.variants.len() == 1 && d.x.variants[0].name.as_str() == short;
        if !is_single_variant_struct {
            for v in d.x.variants.iter() {
                let var_san = sanitize(&v.name);
                defs.insert(format!("is{}", var_san));
                for f in v.fields.iter() {
                    defs.insert(format!("{}_{}", var_san, field_name(&f.name)));
                }
            }
        }
        by_type.insert(path, defs);
    }
    crate::tactic_select::DtDefInventory { by_type }
}

pub fn datatype_to_cmds(
    dt: &DatatypeX,
    emit_accessors: bool,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Vec<Command> {
    // External-body types (`#[verifier::external_body] struct Foo {}`,
    // and the `external_type_specification` proxy variant) have no
    // user-visible structure; Verus stipulates them as opaque carriers
    // for axiomatized methods. Emitting them as an empty Lean `structure`
    // gives them a unique inhabitant (`Foo.mk`), so any two values
    // collapse via `cases` — a soundness gap. Route to opaque-axiom
    // emission instead. See `external_body_type_cmds`.
    if matches!(dt.transparency, DatatypeTransparency::Never) {
        return external_body_type_cmds(dt);
    }
    // Single-element SCC. The set's lifetime is tied to `dt`'s name
    // path; constructed locally because non-mutual datatypes never
    // cross outside their own SCC.
    let mut scc_paths: std::collections::HashSet<&Path> = std::collections::HashSet::new();
    if let Dt::Path(p) = &dt.name {
        scc_paths.insert(p);
    }
    let mut cmds = Vec::new();
    if let Some(decl) = datatype_decl_cmd(dt, &scc_paths, external_body_paths) {
        cmds.push(decl);
    }
    if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths, external_body_paths) {
        cmds.push(inst);
    }
    if let Some(inst) = datatype_nonempty_instance_cmd(dt, &scc_paths, external_body_paths) {
        cmds.push(inst);
    }
    cmds.extend(datatype_accessor_cmds(dt, emit_accessors));
    if let Some(height) = datatype_height_cmd(dt, &scc_paths) {
        cmds.push(height);
    }
    cmds
}

/// Emit external_body types as opaque axioms:
/// ```text
/// axiom T : Type → Type → ... → Type
/// @[instance] axiom T.instInhabited (A : Type) (B : Type) ... :
///     Inhabited (T A B ...)
/// ```
///
/// Two axioms per type:
/// 1. The type itself, curried through its type params. No equations,
///    no constructors — values are distinguishable only via whatever
///    axiomatized spec fns the user provides.
/// 2. An `Inhabited` instance stipulated by axiom. Required because
///    Tactus emits `| _ => default` fallback arms in multi-variant
///    enum accessors; an external_body field type needs an Inhabited
///    instance for the accessor to elaborate. The `@[instance]` attribute
///    plugs it into Lean's typeclass resolution.
///
/// Both shapes are sound under classical+choice: the type stipulator
/// (e.g., vstd) is claiming "this type is nonempty" and "this is the
/// signature." Tactus's role is to faithfully encode that stipulation.
fn external_body_type_cmds(dt: &DatatypeX) -> Vec<Command> {
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return vec![],
    };
    // Type axiom: `axiom T : Type → ... → Type`, currying type params
    // into the return type so the result is `Type → ... → Type`.
    let type_ret_ty = curry_type_to_type(dt.typ_params.len());
    let type_axiom = Axiom {
        comment: None,
        name: path.clone(),
        binders: vec![],
        ret_ty: type_ret_ty,
        attrs: vec![],
    };
    // Inhabited axiom: `@[instance] axiom T.instInhabited (A : Type) ... :
    //   Inhabited (T A ...)`.
    let inhabited_binders: Vec<LBinder> = dt.typ_params.iter()
        .map(|(id, _)| LBinder::typ_param(id.as_str(), BinderKind::Explicit))
        .collect();
    let parent_applied = if dt.typ_params.is_empty() {
        LExpr::var_lit(&path)
    } else {
        let args: Vec<LExpr> = dt.typ_params.iter()
            .map(|(id, _)| LExpr::var_tp(id.as_str()))
            .collect();
        LExpr::app(LExpr::var_lit(&path), args)
    };
    let inhabited_ret_ty = LExpr::app(LExpr::var_lit("Inhabited"), vec![parent_applied]);
    let inhabited_axiom = Axiom {
        comment: None,
        name: format!("{}.instInhabited", path),
        binders: inhabited_binders,
        ret_ty: inhabited_ret_ty,
        attrs: vec!["instance".into()],
    };
    vec![Command::Axiom(type_axiom), Command::Axiom(inhabited_axiom)]
}

/// Build `Type → Type → ... → Type` with `arity` arrows. For `arity = 0`,
/// returns just `Type`. For `arity = 2`, returns `Type → Type → Type`.
///
/// Used for external_body type axiom signatures (`axiom T : Type → Type`
/// for `T<A>`).
///
/// Lean's `→` for non-`Prop` types is the same syntactic arrow as the
/// implication arrow on Props (both render via `BinOp::Implies` which
/// pretty-prints as `→` — see `to_lean_type::SpecFn` for the same
/// convention applied to spec fn types).
fn curry_type_to_type(arity: usize) -> LExpr {
    let type_ = LExpr::var_lit("Type");
    let mut result = type_.clone();
    for _ in 0..arity {
        result = LExpr::implies(type_.clone(), result);
    }
    result
}

/// Emit a group of datatypes — `Single` for non-mutual, `Mutual` for
/// SCCs of size >1 (#109). For mutual SCCs:
/// 1. Inductive declarations are wrapped in a `mutual ... end` block
///    so cross-type field references resolve.
/// 2. Accessors emit OUTSIDE the mutual block — they're per-datatype
///    structural defs that don't recurse across the SCC.
/// 3. Height fns are wrapped in a SECOND `mutual ... end` block —
///    cross-type recursive calls (e.g., `A.height` calling
///    `B.height`) require the mutual scope to typecheck.
///
/// `deriving Inhabited` stays on each `inductive` declaration even
/// inside the mutual block — Lean accepts inline deriving for
/// mutually-recursive inductives and produces conditional instances.
pub fn datatype_group_to_cmds<'a>(
    group: &crate::dep_order::DatatypeGroup<'a>,
    emit_accessors: bool,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Vec<Command> {
    use crate::dep_order::DatatypeGroup;
    let all_dts: Vec<&'a DatatypeX> = match group {
        DatatypeGroup::Single(dt) => return datatype_to_cmds(dt, emit_accessors, external_body_paths),
        DatatypeGroup::Mutual(dts) => dts.clone(),
    };

    // External-body types in a mutual SCC are exotic — they have no
    // fields so they can't recurse into other types. If `dep_order` ever
    // groups one into an SCC (currently it shouldn't), peel them off and
    // emit as opaque axioms separately; the remaining members go through
    // the mutual emission path.
    let mut cmds = Vec::new();
    let dts: Vec<&'a DatatypeX> = all_dts.iter().copied().filter(|dt| {
        if matches!(dt.transparency, DatatypeTransparency::Never) {
            cmds.extend(external_body_type_cmds(dt));
            false
        } else {
            true
        }
    }).collect();
    if dts.is_empty() {
        return cmds;
    }

    // Build the SCC path set once for all (non-external-body) members of
    // the group.
    let scc_paths: std::collections::HashSet<&Path> = dts.iter()
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some(p),
            Dt::Tuple(_) => None,
        })
        .collect();

    // 1. mutual block of inductives.
    let inductive_cmds: Vec<Command> = dts.iter()
        .filter_map(|dt| datatype_decl_cmd(dt, &scc_paths, external_body_paths))
        .collect();
    cmds.push(Command::Mutual(inductive_cmds));

    // 1b. Manual `Inhabited` instances for any indexed-style members of
    // the SCC (Lean rejects `deriving Inhabited` on indexed inductives).
    // Emitted OUTSIDE the mutual block — Lean's instance system can
    // resolve cross-references to types declared earlier in the file
    // (the mutual block above) without needing the instance itself to
    // be inside it.
    for dt in &dts {
        if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths, external_body_paths) {
            cmds.push(inst);
        }
        if let Some(inst) = datatype_nonempty_instance_cmd(dt, &scc_paths, external_body_paths) {
            cmds.push(inst);
        }
    }

    // 2. accessors per-datatype, outside the mutual block.
    for dt in &dts {
        cmds.extend(datatype_accessor_cmds(dt, emit_accessors));
    }

    // 3. mutual block of height fns. Each height fn reaches the
    //    others by name; the mutual scope makes those names visible.
    //    full-name rendering over the WHOLE SCC: a sibling `.height`
    //    reference inside the mutual block must render relatively —
    //    the sibling is not yet a global constant, so a root-anchored
    //    `_root_.{ns}.Sibling.height` is `Unknown identifier` (same
    //    rule as mutual spec-fn groups; 2026-07-09 review, finding #1).
    let height_cmds: Vec<Command> = dts.iter()
        .filter_map(|dt| datatype_height_cmd(dt, &scc_paths))
        .collect();
    if !height_cmds.is_empty() {
        cmds.push(Command::Mutual(height_cmds));
    }

    cmds
}

/// Returns `true` iff `dt` has at least one variant field whose type is a
/// recursive reference to a datatype in `scc_paths` AND whose type-arguments
/// don't match the parent's `typ_params` positionally — i.e., the recursive
/// arm uses a different instantiation than the parent declares.
///
/// Example trigger: `enum Mut<A> { Plain(A), Recurse(Mut<u8>) }` — the
/// `Recurse` arm uses `Mut<u8>` while the parent's typ_params are `[A]`.
/// Lean's parameter-style strict-positivity check rejects this; we route
/// to indexed-style emission instead (which Lean accepts).
///
/// Counterexample (uniform recursion): `enum List<A> { Cons(A, List<A>) }`
/// — recursive arm uses `List<A>`, args match parent's params. Returns false.
///
/// Counterexample (no generics): `enum Tree { Leaf, Node(Tree, Tree) }` —
/// no parent params to compare against; recursion is trivially uniform.
/// Returns false.
/// Returns `true` iff `typ` peels to a `Dt::Path(p)` reference where `p`
/// is in `external_body_paths`. Used by the Inhabited-emission gate
/// (`has_field_referencing_external_body`) to decide whether the parent
/// datatype's auto-derived Inhabited would fail Lean's compiler IR check.
///
/// Only the outermost path is checked — nested generic args don't matter
/// here because Lean's `deriving Inhabited` constructs the default by
/// picking a variant and applying `default` to each field's TYPE. A field
/// of type `Vec<Opaque>` produces `Vec.nil` via Vec's polymorphic
/// Inhabited (no Opaque value constructed); only a field DIRECTLY typed
/// `Opaque` forces calling `default : Opaque` which lacks code.
fn typ_references_external_body(
    typ: &Typ,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> bool {
    let peeled = crate::to_lean_type::peel_typ_wrappers(typ);
    match &**peeled {
        TypX::Datatype(Dt::Path(p), _, _) => external_body_paths.contains(p),
        _ => false,
    }
}

/// Returns `true` iff any variant field of `dt` references an external_body
/// datatype directly (via `typ_references_external_body`). See that helper's
/// docstring for why a shallow check suffices.
fn has_field_referencing_external_body(
    dt: &DatatypeX,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> bool {
    dt.variants.iter().any(|v|
        v.fields.iter().any(|f| typ_references_external_body(&f.a.0, external_body_paths))
    )
}

fn has_cross_instantiation_recursion(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
) -> bool {
    let parent_params: Vec<&str> = dt.typ_params.iter().map(|(id, _)| id.as_str()).collect();
    if parent_params.is_empty() {
        return false; // no params → no cross-instantiation possible.
    }
    for variant in dt.variants.iter() {
        for field in variant.fields.iter() {
            let field_typ = crate::to_lean_type::peel_typ_wrappers(&field.a.0);
            let TypX::Datatype(Dt::Path(p), args, _) = &**field_typ else { continue; };
            if !scc_paths.contains(p) { continue; }
            // Recursive arm. Compare args to parent's typ_params positionally.
            if args.len() != parent_params.len() { return true; }
            for (arg, &param_name) in args.iter().zip(parent_params.iter()) {
                let arg_peeled = crate::to_lean_type::peel_typ_wrappers(arg);
                let TypX::TypParam(n) = &**arg_peeled else { return true; };
                if n.as_str() != param_name { return true; }
            }
        }
    }
    false
}

/// Emit the `inductive` (or `structure`) declaration for a datatype.
/// Returns None for `Dt::Tuple` (no decl needed; tuples render as products).
///
/// Branches on `has_cross_instantiation_recursion` to pick parameter-style
/// vs indexed-style. Indexed-style requires a companion `Inhabited`
/// instance — emitted separately by `datatype_inhabited_instance_cmd`.
fn datatype_decl_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let (path, self_rel, short) = match &dt.name {
        Dt::Path(p) => (
            lean_name(p),
            crate::to_lean_type::lean_name_relative(p),
            short_name(p).to_string(),
        ),
        Dt::Tuple(_) => return None,
    };
    let typ_params: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();

    let is_single_variant_struct =
        dt.variants.len() == 1 && dt.variants[0].name.as_str() == short;

    let cross_inst = has_cross_instantiation_recursion(dt, scc_paths);

    // Recursive/sibling field types render as full dotted names —
    // resolves fine mid-declaration at root scope (Option B, verified
    // empirically for single and mutual inductives; the former
    // relative-rendering machinery is retired).
    let kind = if is_single_variant_struct {
            let variant = &dt.variants[0];
            DatatypeKind::Structure {
                fields: variant.fields.iter().map(|f| Field {
                    name: field_name(&f.name),
                    ty: typ_to_expr(&f.a.0),
                }).collect(),
            }
        } else {
            let variants: Vec<Variant> = dt.variants.iter().map(|v| Variant {
                name: sanitize(&v.name),
                fields: v.fields.iter().map(|f| Field {
                    name: field_name(&f.name),
                    ty: typ_to_expr(&f.a.0),
                }).collect(),
            }).collect();
            if cross_inst {
                DatatypeKind::IndexedInductive { variants }
            } else {
                DatatypeKind::Inductive { variants }
            }
        };

    // Derive `Inhabited` automatically for parameter-style. Lean rejects
    // `deriving Inhabited` on indexed-style inductives, so we drop the
    // derive and emit a manual instance via
    // `datatype_inhabited_instance_cmd` instead. For self-referential
    // types like `enum Stack { Empty, Push(u8, Box<Stack>) }`,
    // `Push_val1 : Stack → Stack` needs `Inhabited Stack`. For generic
    // datatypes (#108), Lean's `deriving Inhabited` auto-generates a
    // conditional instance `[Inhabited A] → Inhabited (List A)`. For
    // mutually recursive SCCs (#109), Lean accepts `deriving Inhabited`
    // inline even inside a `mutual` block (parameter-style only).
    //
    // ALSO drop the derive when any field references an external_body
    // type: Lean's auto-derived Inhabited is *computable* and depends on
    // the field's Inhabited.default at code-gen time. External_body
    // types have axiomatic Inhabited instances with no executable code,
    // so the compiler IR check fails on the parent's auto-derived
    // instance. `datatype_inhabited_instance_cmd` emits a manual
    // `noncomputable instance` in this case (and the cross-instantiation
    // case above).
    let has_external_body_field =
        has_field_referencing_external_body(dt, external_body_paths);
    let derives = if cross_inst || has_external_body_field {
        vec![]
    } else {
        vec!["Inhabited".into()]
    };
    Some(Command::Datatype(Datatype {
        name: path,
        self_name: self_rel,
        typ_params,
        kind,
        derives,
    }))
}

/// For indexed-style datatypes (cross-instantiation recursion), emit a
/// manual `Inhabited` instance of shape:
/// ```text
/// noncomputable instance {A : Type} [Inhabited A] : Inhabited (T A) where
///   default := T.<base> default default ...
/// ```
/// where `<base>` is a non-recursive variant (one whose fields don't
/// reference any datatype in the SCC). Each field gets `default` from the
/// `[Inhabited A]` typeclass param (for type-param fields) or the global
/// `Inhabited Int` etc. instances (for primitive fields).
///
/// Returns `None` for parameter-style datatypes (Lean's `deriving Inhabited`
/// handles those) and for tuple datatypes (no decl). Also returns `Some`
/// when any variant field references an external_body type — the parent
/// must then have a *noncomputable* Inhabited instance (axiom-backed
/// child Inhabited instances have no executable code; Lean's auto-derived
/// computable instance would fail the IR check).
/// Conditional `Nonempty` instance for a GENERIC datatype:
/// `@[instance] noncomputable def T.instNonempty {A…} [Nonempty A…] :
///  Nonempty (T A…) := Nonempty.intro (T.<base> Classical.ofNonempty …)`.
///
/// Needed because B4's accessors fall back to `Classical.ofNonempty` at
/// the FIELD type: for a field typed `Inner A`, `Nonempty (Inner A)` is
/// not synthesizable from a bare `[Nonempty A]` — `deriving Inhabited`'s
/// conditional instance needs `Inhabited A`, and core's
/// `instNonemptyOfInhabited` bridge is one-way (2026-07-09 review,
/// finding #2). Emitting the Nonempty analog per generic datatype closes
/// the chain: param fields use the binder, concrete fields use the
/// Inhabited bridge, generic-datatype fields use the field type's own
/// instNonempty (datatype emission is dep-ordered). Parameterless
/// datatypes need nothing — their derived/axiom `Inhabited` bridges to
/// `Nonempty` unconditionally. Base-variant selection mirrors
/// `datatype_inhabited_instance_cmd`. Emitted as an `@[instance]` Def
/// (not `Command::Instance`) because `Nonempty` is an inductive Prop
/// with an anonymous constructor, not a structure with fields — the
/// `where`-methods form doesn't apply.
fn datatype_nonempty_instance_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    if dt.typ_params.is_empty() {
        return None;
    }
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return None,
    };
    let base_variant = dt.variants.iter()
        .find(|v| v.fields.iter().all(|f| {
            field_recursive_target(&f.a.0, scc_paths).is_none()
                && !typ_references_external_body(&f.a.0, external_body_paths)
        }))
        .or_else(|| dt.variants.first())?;
    let args: Vec<LExpr> = base_variant.fields.iter()
        .map(|_| LExpr::var_lit("Classical.ofNonempty"))
        .collect();
    let ctor = LExpr::new(crate::expr_shared::ctor_node(&dt.name, &base_variant.name, args));
    let body = LExpr::app1(LExpr::var_lit("Nonempty.intro"), ctor);
    let mut binders: Vec<LBinder> = Vec::new();
    for (id, _) in dt.typ_params.iter() {
        binders.push(LBinder::typ_param(id.as_str(), BinderKind::Implicit));
        binders.push(LBinder::instance(
            LExpr::app1(LExpr::var_lit("Nonempty"), LExpr::var_tp(id.as_str())),
        ));
    }
    let applied_args: Vec<LExpr> = dt.typ_params.iter()
        .map(|(id, _)| LExpr::var_tp(id.as_str()))
        .collect();
    let ret_ty = LExpr::app1(
        LExpr::var_lit("Nonempty"),
        LExpr::app(LExpr::var_lit(&path), applied_args),
    );
    Some(Command::Def(Def {
        attrs: vec!["instance".into()],
        name: format!("{}.instNonempty", path),
        binders,
        ret_ty,
        body,
        termination_by: Vec::new(),
        termination_structural: false,
        decreasing_by: None,
    }))
}

fn datatype_inhabited_instance_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let cross_inst = has_cross_instantiation_recursion(dt, scc_paths);
    let has_external_body_field =
        has_field_referencing_external_body(dt, external_body_paths);
    if !cross_inst && !has_external_body_field {
        return None;
    }
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return None,
    };
    // Find a base constructor — a variant whose fields don't reference any
    // datatype in the SCC AND don't reference any external_body datatype.
    // Such a variant exists for most Rust-constructible enums (a unit-like
    // variant or one with only primitive fields). If none exists (e.g.,
    // every variant has an external_body field), fall back to the first
    // variant: `default` for an external_body field type routes to that
    // type's axiom-backed Inhabited instance, which is valid noncomputable.
    let base_variant = dt.variants.iter()
        .find(|v| v.fields.iter().all(|f| {
            field_recursive_target(&f.a.0, scc_paths).is_none()
                && !typ_references_external_body(&f.a.0, external_body_paths)
        }))
        .or_else(|| dt.variants.first())?;

    // Build `T.<base> default default ...` — the constructor applied to
    // `default` for each field. Lean infers the implicit type-args via the
    // target `Inhabited (T A)` plus the `[Inhabited A]` bound.
    // Naming goes through the shared `ctor_node` rule — a hand-rolled
    // `format!("{}.{}", path, variant)` here once produced
    // `T.T default …` for STRUCTS, whose Lean constructor is `T.mk`
    // (the rule: VIR struct variant name == type short name → `mk`).
    // Latent until CRATEDEFS step 1c: baseline only renders this
    // corner inside exec files that get rejected pre-emission.
    let args: Vec<LExpr> = base_variant.fields.iter()
        .map(|_| LExpr::var_lit("default"))
        .collect();
    let body = LExpr::new(crate::expr_shared::ctor_node(&dt.name, &base_variant.name, args));

    // Binders: `{A : Type} [Inhabited A]` per type parameter.
    let mut binders: Vec<LBinder> = Vec::new();
    for (id, _) in dt.typ_params.iter() {
        binders.push(LBinder::typ_param(id.as_str(), BinderKind::Implicit));
        binders.push(LBinder::instance(
            LExpr::app1(LExpr::var_lit("Inhabited"), LExpr::var_tp(id.as_str())),
        ));
    }

    // Target: `Inhabited (T A B ...)`.
    let parent_applied = if dt.typ_params.is_empty() {
        LExpr::var_lit(&path)
    } else {
        let args: Vec<LExpr> = dt.typ_params.iter()
            .map(|(id, _)| LExpr::var_tp(id.as_str()))
            .collect();
        LExpr::app(LExpr::var_lit(&path), args)
    };
    let target = LExpr::app(LExpr::var_lit("Inhabited"), vec![parent_applied]);

    Some(Command::Instance(Instance {
        binders,
        target,
        methods: vec![InstanceMethod {
            name: "default".into(),
            body,
        }],
    }))
}

/// Emit per-variant accessor / discriminator defs for a datatype.
/// Empty for single-variant structs (handled via Lean's auto-generated
/// `structure` projections) and when `emit_accessors == false` (proof-
/// fn paths preserve native Lean match instead of routing through
/// generated accessors).
fn datatype_accessor_cmds(dt: &DatatypeX, emit_accessors: bool) -> Vec<Command> {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
        Dt::Tuple(_) => return vec![],
    };
    let is_single_variant_struct =
        dt.variants.len() == 1 && dt.variants[0].name.as_str() == short;
    if is_single_variant_struct || !emit_accessors {
        return vec![];
    }
    multi_variant_accessor_defs(dt, &path)
}

/// Emit the height fn for a datatype, parameterized by the SCC it
/// belongs to. See `height_fn_for_datatype` for the semantics.
fn datatype_height_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let p = match &dt.name {
        Dt::Path(p) => p,
        Dt::Tuple(_) => return None,
    };
    // The height def's self-calls render as the full dotted name —
    // resolves fine mid-declaration at root scope (Option B).
    let path = lean_name(p);
    height_fn_for_datatype(dt, &path, scc_paths)
}

/// Emit `def T.height : T → Nat` alongside the datatype so that
/// non-int `decreases` measures on `T` can discharge the
/// termination obligation emitted by `sst_exp_to_ast_checked`'s
/// `CheckDecreaseHeight` arm.
///
/// - **Non-recursive datatype** (no recursive fields w.r.t. the SCC):
///   emit `fun _ => 1`. Doesn't help termination (there's no
///   structural subterm), but keeps the Lean symbol resolvable if a
///   user writes `decreases x` for a non-recursive `x` — the
///   obligation `1 < 1` is simply false, so the recursion fails
///   verification with a clear goal.
/// - **Recursive datatype**: emit a match over variants, summing
///   `1 + height(f)` for each field whose type is in `scc_paths`,
///   treating other fields as 0. The recursive call uses the
///   FIELD's height fn, not the parent's — so for an SCC, a
///   `Tree.Branch f` arm where `f : Forest` calls `Forest.height f`
///   (rather than the trivial `1` in the pre-#109 code that only
///   recursed on self).
///
/// `scc_paths` contains all datatype paths in the SCC the input `dt`
/// belongs to (always at least `dt`'s own path). For non-mutual
/// datatypes the set has size 1 and behavior matches the pre-#109
/// shape. For mutual SCCs (#109) the set has size >1 and the
/// emitted `def` MUST be wrapped in a `mutual ... end` block
/// alongside the other SCC members' height fns — Lean otherwise
/// rejects the cross-type recursive reference.
///
/// Returns `None` for **tuple datatypes** (`Dt::Tuple`) — they're
/// rendered as products with no declaration site.
///
/// The "recursive field" test peels `TypX::Boxed` (poly coercion)
/// and `TypX::Decorate` (e.g., `Box<Self>`, `&Self`) before
/// comparing — this matches how `typ_to_expr` renders field types
/// at the Lean level (Box is transparent).
fn height_fn_for_datatype(
    dt: &DatatypeX,
    path: &str,
    scc_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    if let Dt::Tuple(_) = &dt.name {
        return None;
    }

    // Generic datatypes (#108): emit `T.height : {A : Type} → … → T A B …
    // → Nat`. The implicit type-param binders let callers write just
    // `T.height x` — Lean infers A from x's type. Recursion is on the
    // T A structure, not on A itself; the equation compiler handles this
    // because the recursive arg (e.g. `Tree.Node x rest` → recurse on
    // `rest : Tree A`) decreases by structure regardless of A.
    let typ_param_names: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();
    let typed_input: LExpr = if typ_param_names.is_empty() {
        LExpr::var_synthetic(path)
    } else {
        LExpr::app(
            LExpr::var_synthetic(path),
            typ_param_names.iter()
                .map(|tp| LExpr::var_tp(tp))
                .collect(),
        )
    };
    let implicit_typ_binders: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder::typ_param(tp, BinderKind::Implicit)).collect();

    let has_recursive_field = dt.variants.iter().any(|v|
        v.fields.iter().any(|f| field_recursive_target(&f.a.0, scc_paths).is_some())
    );

    if !has_recursive_field {
        // Non-recursive: simple constant fn. The match-on-binder form
        // is fine here — there's no WF analysis needed.
        let mut binders = implicit_typ_binders;
        binders.push(LBinder::explicit(crate::lean_name::LeanName::lit("_"), typed_input));
        return Some(Command::Def(Def {
            attrs: vec!["simp".into()],
            name: format!("{}.height", path),
            binders,
            ret_ty: LExpr::var_lit("Nat"),
            body: LExpr::lit_int("1"),
            termination_by: vec![],
            termination_structural: false,
            decreasing_by: None,
        }));
    }

    // Recursive: emit match-on-binder form with explicit
    // `termination_by sizeOf s` clause. Pre-collapse the height fn
    // was curried (`| pat => body` form) so Lean's equation compiler
    // could infer well-founded recursion structurally. That breaks
    // for wrapper-containing recursive datatypes (`enum Stack {
    // Push(u8, Box<Stack>) }`): the recursive call `Stack.height
    // val1.deref` for `val1 : Tactus.Box Stack` has `.deref` as a
    // definitional projection that Lean's structural-recursion
    // analyzer doesn't see through, producing "invalid projection"
    // errors.
    //
    // Switching to match-on-binder + explicit `termination_by sizeOf
    // s` bypasses the structural analyzer entirely: Lean's auto-
    // derived `SizeOf` for `Tactus.Box` counts the inner value, so
    // `sizeOf val1.deref < sizeOf val1 < sizeOf (Stack.Push _ val1)`
    // holds and well-founded recursion accepts it.
    //
    // For generics (#108): the implicit type-param binders + the
    // explicit value-arg binder go in `Def.binders`; the return type
    // is `Nat`.
    let arg_name = "s";
    let value_binder = LBinder::explicit(crate::lean_name::LeanName::lit(arg_name), typed_input);
    let mut all_binders = implicit_typ_binders;
    all_binders.push(value_binder);
    let arms: Vec<MatchArm> = dt.variants.iter().map(|v| {
        let var_san = sanitize(&v.name);
        let ctor_name = format!("{}.{}", path, var_san);
        let mut pats = Vec::with_capacity(v.fields.len());
        // (binder name, height fn name, deref count) for each
        // recursive field. The binder name IS the field's declared
        // name (`val1` for positional fields like `Push(u8,
        // Box<Stack>)`; user-given names for named fields like
        // `Tree { left, right }`). This matches the name Lean already
        // uses for the field in the inductive declaration (see
        // `datatype_to_cmds`'s variant rendering), so generated
        // pattern matches read naturally:
        //
        //   | Stack.Push _ val1 => 1 + Stack.height val1.deref
        //   | Tree.Node left right => 1 + Tree.height left + Tree.height right
        //
        // The height fn name uses the FIELD's datatype (which is in
        // the SCC), not the parent's. For self-recursion these match;
        // for mutual recursion across an SCC they differ. The deref
        // count is the number of wrapper layers Lean infers on the
        // binder — for `Box<Stack>` the binder is `Tactus.Box Stack`
        // so we need `<binder>.deref` to reach the inner `Stack`.
        // Each wrapper layer (Box / Ref / MutRef / Rc / Arc)
        // contributes one `.deref`.
        let mut recursive_binders: Vec<(String, String, usize)> = Vec::new();
        for f in v.fields.iter() {
            if let Some(target_path) = field_recursive_target(&f.a.0, scc_paths) {
                // `field_name` is the same val-prefix-if-numeric
                // transform the inductive declaration uses for the
                // field's declared name — so this pattern binder reads
                // identically to the inductive's field declaration.
                let name = field_name(&f.name);
                let height_fn = format!("{}.height", lean_name(target_path));
                let n_derefs = crate::expr_shared::count_ref_decorations(&*f.a.0);
                pats.push(LPattern::Var(crate::lean_name::LeanName::synthetic(name.clone())));
                recursive_binders.push((name, height_fn, n_derefs));
            } else {
                pats.push(LPattern::Wildcard);
            }
        }
        let mut arm_body = LExpr::lit_int("1");
        for (name, height_fn, n_derefs) in &recursive_binders {
            let arg = crate::expr_shared::apply_deref_chain(
                LExpr::var_synthetic(name.clone()),
                *n_derefs,
            );
            arm_body = LExpr::add(
                arm_body,
                LExpr::app1(LExpr::var_synthetic(height_fn.clone()), arg),
            );
        }
        MatchArm {
            pattern: LPattern::Ctor { name: ctor_name, args: pats },
            body: arm_body,
        }
    }).collect();
    let body = LExpr::match_expr(LExpr::var_lit(arg_name), arms);
    // `sizeOf s` — Lean's auto-derived size measure. Works through
    // wrapper structures because their auto-derived SizeOf counts
    // the inner field.
    let termination = LExpr::app1(
        LExpr::var_lit("sizeOf"),
        LExpr::var(crate::lean_name::LeanName::lit(arg_name)),
    );
    // `simp_arith` handles the linear-arithmetic obligation
    // `sizeOf <field>.deref < sizeOf <ctor>` — Lean's default
    // `decreasing_tactic` can't see through wrapper `.deref`
    // projections, but `simp_arith` reduces them via SizeOf's
    // auto-derived equations and closes the resulting Nat inequality.
    Some(Command::Def(Def {
        attrs: vec!["simp".into()],
        name: format!("{}.height", path),
        binders: all_binders,
        ret_ty: LExpr::var_lit("Nat"),
        body,
        termination_by: vec![termination],
        termination_structural: false,
        decreasing_by: Some("all_goals (simp_all; omega)".to_string()),
    }))
}


/// If `typ` is a reference to a datatype path that's in `scc_paths`,
/// returns that path. Otherwise None. Peels `TypX::Boxed` and
/// `TypX::Decorate` to handle `Box<Self>`, `&Self`, etc.
///
/// For non-mutual datatypes, `scc_paths` contains just the datatype's
/// own path — the result is "is this field self-referential?". For
/// mutually-recursive SCCs (#109), `scc_paths` contains every path in
/// the SCC, so a field of type `B` inside datatype `A` matches when
/// `B` is in the same SCC. The returned path is used by the height fn
/// emitter to choose `B.height` vs `A.height` for the recursive call.
///
/// Generic datatypes (#108): a field of type `Tree<A>` inside
/// `enum Tree<A> { … }` matches when its path is in `scc_paths`,
/// regardless of how the type-arg list compares. `Tree.height` is
/// generic over A, so structural recursion on a `Tree<A>`-typed
/// field is the same as on `Tree<U>` — Lean's equation compiler
/// handles both.
fn field_recursive_target<'a>(
    typ: &Typ,
    scc_paths: &'a std::collections::HashSet<&Path>,
) -> Option<&'a Path> {
    match &**crate::to_lean_type::peel_typ_wrappers(typ) {
        TypX::Datatype(Dt::Path(p), _, _) => scc_paths.get(p).copied(),
        _ => None,
    }
}

/// Emit `Type.is<Variant>` discriminators and `Type.<Variant>_<field>`
/// accessors for each (variant, field) pair on a multi-variant
/// inductive.
///
/// Discriminator: `def Type.isFoo : Type → Bool := fun x => match x
/// with | Type.Foo .. => true | _ => false` — one per variant,
/// regardless of whether the variant carries fields. `is_variant_node`
/// in `expr_shared.rs` emits `x.isFoo` references that resolve here.
///
/// Accessor: `noncomputable def Type.Foo_val0 : Type → FieldTy :=
/// fun x => match x with | Type.Foo v _ => v | _ => Classical.arbitrary _`
/// — one per (variant, field) pair. The `_` patterns ignore the other
/// fields in that variant; other variants get `Classical.arbitrary _`
/// because those cases are unreachable when the user's code guards
/// the projection with a prior `isVariant` check, but Lean still
/// requires the match to be total. `Classical.arbitrary` needs
/// `Nonempty` — fine for the primitive types exec-fn match-desugaring
/// actually reaches (ints, bools, references).
fn multi_variant_accessor_defs(dt: &DatatypeX, type_name: &str) -> Vec<Command> {
    let mut cmds = Vec::new();
    // Generic datatypes (#108): the discriminator and accessors need
    // implicit type-param binders `{A : Type}` so the input `x : T A`
    // typechecks. For non-generic datatypes the binders list is empty
    // and `x : T` (no application). Same shape as `height_fn_for_datatype`.
    let typ_param_names: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();
    let typed_input: LExpr = if typ_param_names.is_empty() {
        LExpr::var_synthetic(type_name.to_string())
    } else {
        LExpr::app(
            LExpr::var_synthetic(type_name.to_string()),
            typ_param_names.iter()
                .map(|tp| LExpr::var_tp(tp))
                .collect(),
        )
    };
    // Binder pieces, computed once and cloned per (variant, field).
    // Each piece is a logical group:
    //
    // * `typ_param_pieces`: implicit `{A : Type}` per type param —
    //   needed by both discriminators and accessors (so the input
    //   `x : T A` typechecks).
    // * `inhabited_bound_pieces`: instance `[Nonempty A]` per type
    //   param — needed by accessors only (the unreachable-arm
    //   `Classical.ofNonempty` fallback resolves via `Nonempty`).
    //   Discriminators return `Prop`, no fallback use. `Nonempty` (not
    //   `Inhabited`): it's what tactus threads through every generic
    //   context ([Nonempty A] on broadcast axioms, choose bounds), and
    //   core's `instNonemptyOfInhabited` lets every Inhabited provider
    //   (deriving, manual instances) keep satisfying it — strictly wider
    //   applicability (B4, DESIGN-lean-all-proofs-bugs.md: 713 `failed
    //   to synthesize Inhabited T` errors from accessors instantiated in
    //   Nonempty-only generic contexts).
    // * `x_binder`: the `(x : T A)` value parameter — same for both.
    let typ_param_pieces: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder::typ_param(tp, BinderKind::Implicit)).collect();
    let inhabited_bound_pieces: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder::instance(LExpr::app1(LExpr::var_lit("Nonempty"), LExpr::var_tp(tp)))).collect();
    let x_binder = LBinder::explicit(crate::lean_name::LeanName::lit("x"), typed_input.clone());
    let discriminator_binders = || -> Vec<LBinder> {
        let mut bs = typ_param_pieces.clone();
        bs.push(x_binder.clone());
        bs
    };
    let accessor_binders = || -> Vec<LBinder> {
        let mut bs = typ_param_pieces.clone();
        // The `[Nonempty A]` bounds exist solely for the wildcard-arm
        // `Classical.ofNonempty` fallback, which is only emitted when
        // variants.len() > 1 (single-variant ENUMS get accessors with an
        // exhaustive one-ctor match). Demanding the bound without the
        // arm made single-variant-enum accessors unusable from generic
        // contexts — no caller is ever seeded to supply it (2026-07-09
        // review, finding #4; keeps the gate aligned with Seed 3's
        // multi-variant filter in compute_nonempty_needs).
        if dt.variants.len() > 1 {
            bs.extend(inhabited_bound_pieces.iter().cloned());
        }
        bs.push(x_binder.clone());
        bs
    };
    let match_on_x = |arms: Vec<MatchArm>| LExpr::match_expr(LExpr::var_lit("x"), arms);

    // Discriminators: `def Type.isFoo (x : Type) : Prop := match x with …`.
    // Lean's `inductive` doesn't auto-derive these (only `structure` does);
    // `is_variant_node` in `expr_shared.rs` emits `x.isFoo` references that
    // resolve here.
    //
    // **Prop, not Bool.** Verus's `TypX::Bool` renders as Lean `Prop`
    // (see `to_lean_type::typ_to_expr`). The desugared match-test
    // (`pattern_to_exprs` in ast_simplify) builds expressions typed
    // `TypX::Bool` and combines them with `BinaryOp::And` — which
    // maps to Lean `∧ : Prop → Prop → Prop`. So everything in that
    // chain must be `Prop`. Returning `Bool` would cause the `And`
    // between `x.isFoo` (Bool) and `True` (from the wildcard base
    // case) to be a Prop/Bool mismatch.
    for v in dt.variants.iter() {
        let var_san = sanitize(&v.name);
        let wildcards: Vec<LPattern> = v.fields.iter().map(|_| LPattern::Wildcard).collect();
        let mut arms = vec![MatchArm {
            pattern: LPattern::Ctor {
                name: format!("{}.{}", type_name, var_san),
                args: wildcards,
            },
            body: LExpr::lit_bool(true),
        }];
        // The catch-all false arm is needed for multi-variant inductives
        // (totality) but redundant for single-variant ones — the single
        // ctor pattern is already exhaustive, so Lean would warn
        // "Redundant alternative" and `lean_process` reports that as a
        // verification error. For a one-variant inductive this
        // discriminator always returns `true` anyway.
        if dt.variants.len() > 1 {
            arms.push(MatchArm {
                pattern: LPattern::Wildcard,
                body: LExpr::lit_bool(false),
            });
        }
        cmds.push(Command::Def(Def {
            // `@[simp]`: let `simp_all` unfold the discriminator so
            // `tactus_auto` can close exec-fn goals that turn on a
            // pattern test. Without this, `k.isFoo` stays opaque and
            // the downstream `omega` / `simp_all` can't case-split
            // the enum.
            attrs: vec!["simp".into()],
            name: format!("{}.is{}", type_name, var_san),
            binders: discriminator_binders(),
            ret_ty: LExpr::var_lit("Prop"),
            body: match_on_x(arms),
            termination_by: vec![],
            termination_structural: false,
            decreasing_by: None,
        }));
    }

    // Accessors: `def Type.Foo_val0 (x : Type) : FieldTy := match x with
    //   | Type.Foo v _ _ => v | _ => Classical.arbitrary _`.
    // One per (variant, field) pair. The `_` patterns ignore the other
    // fields in that variant; other variants get `Classical.arbitrary _`
    // — unreachable in practice (the desugared match guards with a
    // prior `isVariant` check), but Lean requires totality.
    // `Classical.arbitrary` needs `[Nonempty α]`, which is auto-derived
    // for the primitive types exec-fn match-desugaring actually reaches.
    for v in dt.variants.iter() {
        let var_san = sanitize(&v.name);
        for (idx, f) in v.fields.iter().enumerate() {
            // Bind the field via the field's declared name (`val0` for
            // positional fields, user-given for named) — matches what
            // the inductive's variant ctor declares the field as, so
            // the accessor's pattern reads like
            // `match x with | Type.Foo val0 _ _ => val0` rather than
            // a synthetic `_tactus_field_<idx>`.
            let field_local = field_name(&f.name);
            let binders_pat: Vec<LPattern> =
                (0..v.fields.len()).map(|i| if i == idx {
                    LPattern::Var(crate::lean_name::LeanName::synthetic(field_local.clone()))
                } else {
                    LPattern::Wildcard
                }).collect();
            let mut arms = vec![MatchArm {
                pattern: LPattern::Ctor {
                    name: format!("{}.{}", type_name, var_san),
                    args: binders_pat,
                },
                body: LExpr::var_synthetic(field_local),
            }];
            // Catch-all `default` arm: needed for multi-variant
            // inductives (Lean requires totality) but redundant for
            // single-variant ones — the ctor pattern already covers
            // every value of the type. Adding the wildcard would
            // surface as Lean's "Redundant alternative" warning and
            // fail verification.
            if dt.variants.len() > 1 {
                arms.push(MatchArm {
                    pattern: LPattern::Wildcard,
                    // `Classical.ofNonempty` resolves via `[Nonempty α]`
                    // — the bound tactus threads everywhere (see the
                    // accessor-binder comment above; B4). The accessor
                    // is already `noncomputable`, so the classical
                    // fallback costs nothing. Unreachable anyway when
                    // call sites guard the accessor with a prior
                    // isVariant check.
                    body: LExpr::var_lit("Classical.ofNonempty"),
                });
            }
            cmds.push(Command::Def(Def {
                // `@[simp]` for the same reason as the discriminator:
                // `simp_all` should unfold the accessor before `omega`
                // tries to reason about its result. Without this the
                // accessor is opaque and goals involving it get stuck.
                attrs: vec!["simp".into()],
                name: format!("{}.{}_{}", type_name, var_san, field_name(&f.name)),
                binders: accessor_binders(),
                ret_ty: typ_to_expr(&f.a.0),
                body: match_on_x(arms),
                termination_by: vec![],
                termination_structural: false,
                decreasing_by: None,
            }));
        }
    }

    cmds
}


// ── Shared helpers ──────────────────────────────────────────────────────

/// Function parameter list as AST binders: type params, trait bounds,
/// then value params. Const generics become explicit `(N : ConstType)`
/// instead of `(N : Type)`.
fn fn_binders(f: &FunctionX, unemittable: &std::collections::HashSet<Path>) -> Vec<LBinder> {
    fn_binders_with_bounds(f, /* include_bound_hyps */ true, unemittable)
}

/// Spec-fn variant of `fn_binders`: omit the `h_<name>_bound` refinement
/// hypotheses. Spec fns are Lean defs, not theorems — bound hyps would
/// change the type from `Int → Int` to `Int → Bound → Int` and break
/// call sites that only pass values. Bounds for spec-fn params are
/// instead established at theorem-call sites (where the corresponding
/// hyps DO exist via `fn_binders` on the calling proof/exec fn).
fn fn_binders_without_bound_hyps(f: &FunctionX, unemittable: &std::collections::HashSet<Path>) -> Vec<LBinder> {
    fn_binders_with_bounds(f, /* include_bound_hyps */ false, unemittable)
}

fn fn_binders_with_bounds(f: &FunctionX, include_bound_hyps: bool, unemittable: &std::collections::HashSet<Path>) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();

    let const_typ_for = |name: &str| -> Option<&TypX> {
        for bound in f.typ_bounds.iter() {
            if let GenericBoundX::ConstTyp(param_typ, val_typ) = &**bound {
                if let TypX::TypParam(n) = &**param_typ {
                    if n.as_str() == name { return Some(val_typ); }
                }
            }
        }
        None
    };

    for tp in f.typ_params.iter() {
        let ty = if let Some(val_typ) = const_typ_for(tp) {
            typ_to_expr(val_typ)
        } else {
            LExpr::var_lit("Type")
        };
        // Synthetic associated-type binders (from impl_subst's projection
        // lift) render IMPLICIT — they're determined by their trait's
        // outParam instance bracket, so Lean infers them and VIR-rendered
        // call sites (passing only the original typ_args) typecheck. All
        // user-written typ_params stay explicit.
        let kind = if crate::impl_subst::is_assoc_binder(tp.as_str()) {
            BinderKind::Implicit
        } else {
            BinderKind::Explicit
        };
        out.push(LBinder {
            name: Some(crate::lean_name::LeanName::typ_param(tp.as_str())),
            ty,
            kind,
        });
    }

    out.extend(trait_bounds_to_ast(&f.typ_bounds, unemittable));

    // Each param → one binder, and (for fixed-width int types in
    // proof/exec contexts, gated by `include_bound_hyps`) one
    // hypothesis binder right after giving the refinement bounds.
    //
    // Three callers, two regimes:
    //   - `fn_binders` (proof fn + exec fn theorem path) → bounds INCLUDED.
    //     Must mirror `sst_to_lean::exec_fn_theorem_to_ast`'s bound
    //     emission so proof-fn-callers and exec-fn-callers see the
    //     same in-scope refinement for shared params.
    //   - `fn_binders_without_bound_hyps` (spec fn def path) → bounds OMITTED.
    //     Spec fns are Lean defs, not theorems; bound hyps would change
    //     the signature from `Int → Int` to `Int → Bound → Int` and
    //     break call sites. Bounds for spec-fn params are established
    //     at theorem-call sites (where the corresponding hyps DO exist
    //     via `fn_binders` on the calling proof/exec fn).
    for p in f.params.iter() {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        out.push(LBinder::explicit(name.clone(), crate::to_lean_type::param_binder_typ(&p.x.typ, p.x.is_mut)));
        if include_bound_hyps {
            // For wrapper-bound params (`Tactus.Ref`/`MutRef`/...), the
            // bound applies to the inner value via `.deref` — the wrapper
            // itself has no order/arithmetic instance.
            let bound_value = if needs_param_deref(p) {
                LExpr::field_proj(LExpr::var(name.clone()), "deref")
            } else {
                LExpr::var(name.clone())
            };
            if let Some(pred) = crate::to_lean_sst_expr::type_bound_predicate(
                &bound_value,
                &p.x.typ,
            ) {
                out.push(LBinder::explicit(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str())), pred));
            }
        }
    }

    out
}


fn field_name(name: &str) -> String {
    if name.parse::<usize>().is_ok() {
        format!("val{}", name)
    } else {
        sanitize(name)
    }
}

#[cfg(test)]
#[path = "tests/to_lean_fn.rs"]
mod tests;
