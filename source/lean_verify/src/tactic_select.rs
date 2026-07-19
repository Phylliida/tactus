//! Deterministic-floor tactic selection (S1 of the squeeze-and-pin arc,
//! `DESIGN-transparent-automation.md`; measured basis:
//! `MEASUREMENT-brick1-rung-attribution.md`).
//!
//! When an obligation theorem's goal — hypotheses included, since
//! `emit_split` wraps them into the goal as binder types and
//! implications — lies entirely inside the LINEAR INTEGER ARITHMETIC
//! fragment, the emitter selects `omega` (or `tactus_peel <;> omega`
//! for ∀/let/→-wrapped goals) instead of the `tactus_auto` search
//! gate.
//!
//! Safety argument (why selection cannot lose passes): `omega` is a
//! DECISION PROCEDURE for the fragment — complete. Any in-fragment
//! goal that `tactus_auto` closed (through whichever rung) is
//! therefore closed by `omega` directly. Goals needing a broadcast
//! axiom or a spec-fn unfolding necessarily mention an out-of-fragment
//! head (the axiom's subject — `Seq.len`, a spec fn, …), so they can
//! never be misclassified into the fragment. The classification is
//! purely syntactic and total: unknown node kinds fall out of the
//! fragment, never into it.
//!
//! Guiding rule served (Danielle, 2026-07-11): every injected tactic
//! carries its own specification, readable at the site — `omega`'s
//! name IS its spec, and the fragment check is exactly that spec.
//!
//! v1 scope notes:
//! - `Bool` is OUT of the fragment (omega is Int/Nat only; Bool-valued
//!   equalities fall to `simp`-class reasoning). `True`/`False` goals
//!   are likewise left to the default closer.
//! - `ite` is OUT (omega does not split; that's the
//!   `(repeat split) <;> omega` shape — a candidate v2 selection).
//! - `Int.toNat` is IN (omega handles it natively; it appears in
//!   emitted usize-cast goals — both `e.toNat` field-proj and
//!   `Int.toNat e` application forms).
//! - Broadcast `have` prefixes stay attached even when omega is
//!   selected (harmless: omega ignores non-arithmetic hypotheses);
//!   trimming them is a v2 nicety.

use crate::lean_ast::{BinOp, Binder, Expr, ExprNode, UnOp};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Selection {
    /// Bare arithmetic goal: `omega`.
    Omega,
    /// Arithmetic goal behind leading ∀ / `let` / `→` wrappers:
    /// explicit intro/refine prefix + `omega` (B4 — no more
    /// `tactus_peel` macro; the emitter generates the structure).
    PeelOmega,
}

impl Selection {
    pub(crate) fn tactic_text(self, goal: &Expr) -> String {
        match self {
            Selection::Omega => "omega".to_string(),
            Selection::PeelOmega => render_peel(goal, "omega"),
        }
    }
}

/// Explicit structural peel (B4, `DESIGN-transparent-automation.md` §4):
/// the emitter BUILT every goal it closes, so it walks the goal tree and
/// emits the exact intro/refine sequence — `intro` per ∀ binder /
/// implication antecedent / goal-position `let` (with anonymous-
/// constructor patterns for ∧- and ×-typed hypotheses), then a single
/// `refine ⟨…⟩` mirroring the goal's conjunction tree, each conjunct
/// closed by a `by <leaf>` block. Replaces the recursive `tactus_peel`
/// prelude macro: no search, no macro expansion in artifacts, and each
/// conjunct gets its own tactic position so sourcemap spans point at
/// the SPECIFIC failing conjunct instead of a macro invocation.
///
/// `leaf` is the tactic text applied at each peeled leaf (e.g. `omega`,
/// or `first | rfl | decide | omega` for the derived closer's kernel
/// branch). A goal with no peelable structure renders as just `leaf`.
///
/// The sequence is `;`-joined on one line and steps are UNGUARDED by
/// design. Two earlier designs failed empirically (2026-07-17):
/// `try`-guards are unusable because `try` takes the following tactic
/// SEQUENCE as its argument (`try (intro _); first | …` no-ops the
/// whole chain), and newline-separated steps break the layout of
/// parenthesized `first`-alternatives (whose content must stay indented
/// past the paren's column). The correct guard is BRANCH ORDER: the
/// derived closer tries the bare kernel ladder first (`first | rfl |
/// decide | omega`), so goals a prefix already peeled/transformed close
/// there; this branch's unguarded steps only run on goals that actually
/// have the structure the statement says to peel (or fail loudly and
/// fall through to the CORE branch).
pub(crate) fn render_peel(goal: &Expr, leaf: &str) -> String {
    match &goal.node {
        ExprNode::SpanMark { inner, .. } => render_peel(inner, leaf),
        ExprNode::Forall { binders, body } => {
            let mut out: Vec<String> = binders
                .iter()
                .map(|b| format!("intro {}", conj_pattern(&b.ty)))
                .collect();
            out.push(render_peel(body, leaf));
            out.join("; ")
        }
        ExprNode::Let { name, body, .. } => {
            // A goal-position `let` must be ZETA-REDUCED, not merely
            // intro'd: `intro _` produces a context let-var that omega
            // treats as an OPAQUE atom (it never unfolds context let
            // bindings), so `0 ≤ tmp__1 * (i+1)` stays disconnected from
            // the `result ≤ …` hypotheses (factorial 154:18 failure).
            // `intro <name>; subst <name>` substitutes the value through
            // the goal — the kernel leaf (and omega's own arithmetic)
            // then see the real expression.
            format!(
                "intro {}; subst {}; {}",
                name.as_str(),
                name.as_str(),
                render_peel(body, leaf)
            )
        }
        ExprNode::BinOp { op: BinOp::Implies, lhs, rhs } => {
            format!("intro {}; {}", conj_pattern(lhs), render_peel(rhs, leaf))
        }
        ExprNode::BinOp { op: BinOp::And, .. } => {
            format!("refine {}", conj_term(goal, leaf))
        }
        _ => leaf.to_string(),
    }
}

/// Term-level mirror of a goal's conjunction tree: `A ∧ (B ∧ C)` becomes
/// `⟨by <peel A>, ⟨by <peel B>, by <peel C⟩⟩` — explicit nesting (the
/// anonymous-constructor flattening picks the right-nested reading
/// first, so left-nested trees must be mirrored, not flattened).
fn conj_term(goal: &Expr, leaf: &str) -> String {
    match &goal.node {
        ExprNode::SpanMark { inner, .. } => conj_term(inner, leaf),
        ExprNode::BinOp { op: BinOp::And, lhs, rhs } => {
            format!("⟨{}, {}⟩", conj_term(lhs, leaf), conj_term(rhs, leaf))
        }
        _ => format!("by {}", render_peel(goal, leaf)),
    }
}

/// Anonymous-constructor intro pattern mirroring a ∧/×-typed tree:
/// `(P ∧ Q) ∧ R` → `⟨⟨_, _⟩, _⟩`; plain `_` for other types.
fn conj_pattern(ty: &Expr) -> String {
    match &ty.node {
        ExprNode::SpanMark { inner, .. } => conj_pattern(inner),
        ExprNode::BinOp { op: BinOp::And | BinOp::Prod, lhs, rhs } => {
            format!("⟨{}, {}⟩", conj_pattern(lhs), conj_pattern(rhs))
        }
        _ => "_".to_string(),
    }
}

/// Derived default closer (S2c of the squeeze arc; decision:
/// `DESIGN-transparent-automation.md` §3.4; measured basis:
/// `MEASUREMENT-s2a-derivability.md`). Selected when `tactus_auto`
/// would run and `select_deterministic` finds no arithmetic-fragment
/// answer. The ONE derivation rule of the arc (rule budget: one —
/// Danielle, 2026-07-16):
///
///   kernel rungs (rfl / decide — definitional equalities, decidable
///   atoms), then the peeled kernel rungs (wrapped goals whose leaf is
///   kernel-closeable after intro — `tactus_peel` no-ops when there is
///   nothing to intro, so this branch is safe on flat goals), then the
///   fixed core normalizer with an omega tail.
///
/// Every branch is a decision procedure or a FIXED, site-invariant
/// rewrite set: no search, no ambient-scope reads, named lemmas that
/// break loudly on renames. The 43-lemma CORE set below is the union
/// of every squeezed `simp_all?` used-list in the Brick-1 T2 pool,
/// validated to close 389/397 of the full pool (the 8 residue are the
/// census's known clusters — inline-proof surface, §3.4). CORE alone
/// closes 268/280 of the T2 winners; the `<;> omega` tail takes the
/// 12 composed-rung theorems (`simp_all?` suggestions do not always
/// replay standalone — census §5.1). Name hygiene: `not_imp` is cited
/// as `Classical.not_imp` — bare `not_imp` is ambiguous against
/// `_root_.not_imp` once any Mathlib import is in scope (tutorial
/// chapters import `Mathlib.Tactic.Linarith`); every other bare name
/// in the list was probe-tested unambiguous in simp-argument position
/// in BOTH core-only and Mathlib contexts (2026-07-16).
/// 2026-07-16 extension (+4): `Int/Nat.mul_add, Int/Nat.add_mul` —
/// the old default-set `simp_all` distributed products into ring-normal
/// form before its omega rung; the fixed set must do the same or
/// loop-body obligations like `2 * result = i * (i+1) → 2 * (result +
/// (i+1)) = (i+1) * (i+2)` leave omega with irelatable opaque product
/// atoms (tutorial sum_iter regression, caught by the 10-chapter
/// battery). Also 47 lemmas, still site-invariant.
/// 2026-07-16 extension (+2): `Int.toNat_zero, Int.toNat_one` — the
/// default set reduced `Int.toNat 0/1` literals; without them,
/// base-case obligations (`Int.toNat r = fib (Int.toNat n)` under
/// `n = 0`) leave `↑(fib (Int.toNat 0))` opaque to omega (tutorial
/// fib_iter/fib_fast/pow_by_squaring regressions). 49 lemmas.
/// 2026-07-16 extension (+2): `Int/Nat.add_sub_cancel` — loop-body
/// index bookkeeping `(i + 1 - 1).toNat` must reduce to `i.toNat`
/// or spec-fn applications over it stay irelatable (tutorial
/// fib_iter 123-invariant). 51 lemmas.
///
/// CORE simp list (the fixed normalizer half of the derived closer —
/// the full derivation rule spec is in `render_peel`'s and
/// `derived_closer`'s docs; history: census union of 43 + four
/// probe-tested extensions to 51, MEASUREMENT-s2a §6.1).
pub(crate) const CORE_LEMMAS: &str = "Classical.not_forall, Decidable.not_not, Int.add_emod_left, Int.cast_ofNat_Int, Int.natCast_add, Int.neg_add_emod_self, Int.ofNat_eq_coe, Int.ofNat_zero_le, Int.sub_zero, Int.toNat_natCast_add_one, Int.zero_add, Int.zero_sub, Int.mul_add, Int.add_mul, Int.toNat_zero, Int.toNat_one, Int.add_sub_cancel, Nat.add_le_add_iff_right, Nat.add_left_cancel_iff, Nat.add_zero, Nat.le_add_left, Nat.le_add_right, Nat.le_refl, Nat.not_le, Nat.not_lt, Nat.reduceLeDiff, Nat.sub_le_iff_le_add, Nat.zero_add, Nat.zero_le, Nat.mul_add, Nat.add_mul, Nat.add_sub_cancel, and_imp, and_self, and_true, eq_iff_iff, forall_const, forall_eq, ge_iff_le, gt_iff_lt, iff_true, imp_false, imp_self, implies_true, not_and, not_exists, not_false_eq_true, Classical.not_imp, not_or, not_true_eq_false, true_and";

/// The fixed CORE normalizer rung, exactly the v2 text (the list is
/// spliced from `CORE_LEMMAS` so the structural rung below can reuse
/// it without a second copy). Behavior is pool-validated; the
/// structural rung is a separate, ADDITIVE branch — this one does not
/// change.
pub(crate) fn core_simp() -> String {
    format!("simp_all only [{}] <;> omega", CORE_LEMMAS)
}

/// Logic additions used ONLY by the structural rung's simp set (kept
/// out of `CORE_LEMMAS` so rung 3 stays byte-identical to its
/// pool-validated form): truth-value collapse for disjunctive
/// postconditions (`r = 0 ∨ r = x` ground-reduces one disjunct to
/// `True`, which omega cannot consume — simp must finish the
/// collapse) and ite collapse over reduced Prop discriminators
/// (`if True then a else b` after `is<Variant>` unfolds on a
/// constructor). Probe-tested on the e2e exec corpus (2026-07-17,
/// the 26-test squeeze-regression sweep).
pub(crate) const STRUCTURAL_EXTRA_LEMMAS: &str =
    "true_or, or_true, if_true, if_false, reduceCtorEq";

/// Marker text written where the DERIVED closer would go when the goal
/// isn't known yet — the `by(nonlinear_arith)` AssertQuery scope
/// composes its fallback ONCE per scope but obligations arrive
/// per-theorem. `emit_with_extras` substitutes `derived_closer(goal)`
/// for this token at emission. If it ever leaks into an artifact it
/// fails LOUD (unknown identifier) — substitution is total.
pub(crate) const DERIVED_MARKER: &str = "tactus_derived_marker__";

/// Derived default closer (S2c of the squeeze arc; decision:
/// `DESIGN-transparent-automation.md` §3.4; measured basis:
/// `MEASUREMENT-s2a-derivability.md`). Selected when `tactus_auto`
/// would run and `select_deterministic` finds no arithmetic-fragment
/// answer. The ONE derivation rule of the arc (rule budget: one —
/// Danielle, 2026-07-16):
///
///   kernel rungs (rfl / decide — definitional equalities, decidable
///   atoms), then the explicitly-peeled kernel rungs (B4: the emitter
///   walks the goal and generates the intro/refine prefix itself —
///   wrapped goals whose leaf is kernel-closeable after intro; the
///   prefix is empty on flat goals, making this branch a harmless
///   duplicate of the first), then the fixed core normalizer with an
///   omega tail, then the STRUCTURAL rung (`structural_rung` below):
///   named intros + `cases` on the goal's own datatype scrutinees +
///   `simp_all +zetaDelta` over CORE plus the goal-mentioned
///   generated datatype defs.
///
/// Every branch is a decision procedure, a generated structural prefix,
/// or a FIXED, site-invariant rewrite set — or, for the structural
/// rung, a set DERIVED deterministically from the goal text itself
/// (the goal's own scrutinees and the crate's own generated defs; no
/// ambient-scope reads, no search, unfold names break loudly on
/// renames). CORE is the 51-lemma set documented at CORE_LEMMAS
/// (validation: 389/397 of the full Brick-1 pool with only the 8
/// census-residue failures, covered by inline proofs — and 0
/// regressions at every extension step).
///
/// Failure semantics: a goal outside every branch fails LOUD at its
/// named obligation — that is the suggestion signal for an inline
/// proof, per §3.4. `tactus_auto` remains in the prelude for
/// discover-mode overrides; it no longer appears in default emission.
pub(crate) fn derived_closer(
    goal: &Expr,
    dts: &DtDefInventory,
    binders: &[Binder],
    user_prefix: bool,
    eliminators: &[String],
) -> String {
    // Which `rfl` the kernel ladder gets is DERIVED from the goal's
    // core shape (after peeling the ∀/let/→ spine):
    //
    // * Plain `Eq`/`Iff`/`Ne` core → bare `rfl`. One-step unfold
    //   lemmas of RECURSIVE spec fns on constructor args (tactus-core's
    //   u_* ladder: `wp_stm f (Assert o h) = Cons (close_e f o) Nil`)
    //   close ONLY by full-delta defeq — kernel iota handles the
    //   rec_1/PProd encoding that simp's equation generation cannot
    //   ("invalid projection"), so no simp arm can substitute.
    //
    // * Anything else (∧/∨/comparison cores) → `with_reducible rfl`.
    //   Full-delta rfl on an ∧-of-arithmetic goal with casts of stuck
    //   match applications recurses past maxRecDepth, and that
    //   exception is NOT recoverable by `first` — the whole chain
    //   aborts even though a later arm (omega) closes the goal
    //   (sum_vals, typed-renderer adversarial probes). Reducible rfl
    //   fails fast and catchably there, and non-equation goals never
    //   needed delta rfl.
    let rfl_form = if goal_core_is_equation(goal) { "rfl" } else { "with_reducible rfl" };
    let kernel = format!("first | {} | decide | omega", rfl_form);
    let rung = structural_rung(goal, dts, binders, user_prefix);
    // Equation-eliminator arms, LAST in the chain: for each broadcast
    // lemma whose conclusion is a non-Prop equation (derived from
    // signatures at emit time — see the emitter's `eliminators`
    // field), `apply` it against the goal in both orientations, each
    // leg closed by hypothesis or the rung's simp ladder. The whole
    // apply+legs is one backtrackable arm per orientation — `first`
    // does NOT re-enter a committed `(first | A | B) <;> C` when C
    // fails, so the orientation split must wrap the legs. Only
    // equation-core goals get the arms (apply against a non-equation
    // goal cannot unify anyway), and being last they run only where
    // every existing arm already failed.
    let elim_arms: String = if eliminators.is_empty() || !goal_core_is_equation(goal) {
        String::new()
    } else {
        let legs = format!("(first | assumption | ({}))", rung_tail(goal, dts, binders));
        eliminators
            .iter()
            .map(|e| {
                format!(
                    " | (apply {e} <;> {legs}) | ((apply Eq.symm; apply {e}) <;> {legs})",
                    e = e,
                    legs = legs,
                )
            })
            .collect()
    };
    format!(
        "first | {} | decide | omega | ({}) | ({}) | ({}){}",
        rfl_form,
        render_peel(goal, &kernel),
        core_simp(),
        rung,
        elim_arms
    )
}

/// Pass-1/2 scan shared by `structural_rung` and `rung_tail`.
/// Binder TYPES participate fully: hypothesis propositions live
/// there (extracted requires-hyps pre-N1; ALL hyps and let
/// equations after N1 hoisting), and datatype mentions often
/// appear only there (`c : test_crate.Choice` — the 2026-07-17
/// Cause-A gap). Scrutinee targets found in a binder type
/// reference theorem binders, which `cases` can name directly.
fn run_structural_scan<'a>(
    goal: &Expr,
    dts: &'a DtDefInventory,
    binders: &[Binder],
) -> StructuralScan<'a> {
    let mut scan = StructuralScan::new(dts);
    for b in binders {
        scan.collect_mentioned_types(&b.ty);
    }
    scan.collect_mentioned_types(goal);
    let env = std::collections::HashMap::new();
    for b in binders {
        scan.walk(&b.ty, &env);
    }
    scan.walk(goal, &env);
    scan
}

/// The `simp_all … <;> omega` tail from an already-sorted unfold
/// list plus the scan's injEq derivation. Shared by
/// `structural_rung` (full rung) and `rung_tail` (legs of the
/// equation-eliminator arms — no intros, no cases: leg goals have
/// their own spines and the repro-validated leg form is the bare
/// simp ladder).
fn simp_tail_from_unfolds(unfolds: &mut Vec<String>, scan: &StructuralScan) -> String {
    for t in &scan.mentioned_types {
        if let Some(vs) = scan.dts.variants.get(t) {
            for v in vs {
                unfolds.push(format!("{}.{}.injEq", t, v));
            }
        }
    }
    unfolds.sort();
    unfolds.dedup();
    let simp_list = if unfolds.is_empty() {
        format!("{}, {}", CORE_LEMMAS, STRUCTURAL_EXTRA_LEMMAS)
    } else {
        format!("{}, {}, {}", CORE_LEMMAS, STRUCTURAL_EXTRA_LEMMAS, unfolds.join(", "))
    };
    format!("simp_all +zetaDelta only [{}] <;> omega", simp_list)
}

/// Leg ladder for eliminator arms: the structural simp tail alone.
fn rung_tail(goal: &Expr, dts: &DtDefInventory, binders: &[Binder]) -> String {
    let scan = run_structural_scan(goal, dts, binders);
    let mut unfolds: Vec<String> = scan.unfolds.iter().cloned().collect();
    unfolds.extend(scan.mentioned_spec_fns.iter().cloned());
    simp_tail_from_unfolds(&mut unfolds, &scan)
}

/// True when the goal's core — after peeling the leading ∀-binder /
/// goal-let / implication spine — is a bare equation (`Eq`/`Iff`/`Ne`).
/// Decides which `rfl` the derived kernel ladder uses; see the caller.
fn goal_core_is_equation(goal: &Expr) -> bool {
    let mut cur = goal;
    loop {
        match &cur.node {
            ExprNode::SpanMark { inner, .. } => cur = inner,
            ExprNode::Forall { body, .. } => cur = body,
            ExprNode::Let { body, .. } => cur = body,
            ExprNode::BinOp { op: BinOp::Implies, rhs, .. } => cur = rhs,
            ExprNode::BinOp { op: BinOp::Eq | BinOp::Iff | BinOp::Ne, .. } => return true,
            _ => return false,
        }
    }
}

/// Name inventory of the `@[simp]` defs the datatype emission
/// generates alongside each inductive (discriminators `is<Variant>`,
/// accessors `<Variant>_<field>`, the `height` measure). Keyed by the
/// datatype's full Lean type name; values are the SHORT def names.
/// Built by `to_lean_fn::datatype_simp_def_inventory` (which mirrors
/// the emission naming in `multi_variant_accessor_defs` /
/// `datatype_height_cmd` — keep them in sync). Used by
/// `structural_rung` to derive per-goal unfold lists: `simp_all only`
/// excludes the `@[simp]` attribute set by design, so the defs a goal
/// actually mentions must be named explicitly.
#[derive(Debug, Default)]
pub(crate) struct DtDefInventory {
    pub by_type: std::collections::HashMap<String, std::collections::HashSet<String>>,
    /// Sanitized variant names per datatype (same keys as `by_type`).
    /// The structural rung derives `{Dt}.{Variant}.injEq` from these
    /// for every goal-mentioned datatype: N2's hoisted constructor
    /// equations meet `cases`-introduced constructor applications as
    /// equation-vs-equation goals, which need injectivity (and
    /// `reduceCtorEq` disjointness) to resolve under `simp_all only`.
    pub variants: std::collections::HashMap<String, Vec<String>>,
    /// Full Lean names of the crate's SPEC fns (defs the emitter
    /// generates). A goal-mentioned spec fn joins the structural
    /// rung's unfold list: N1 hoisting turns goal-position lets into
    /// hypothesis equations, losing the DEFINITIONAL transparency
    /// `rfl` used to exploit (`let r := {a := 0}; sview r = 0` closed
    /// by defeq; `(h : r = {a := 0}) ⊢ sview r = 0` needs `sview`
    /// unfolded by simp). Derived: only goal-mentioned names enter.
    pub spec_fns: std::collections::HashSet<String>,
}

/// The STRUCTURAL rung (2026-07-17, the squeeze-regression fix): the
/// last branch of the derived closer, for goals whose arithmetic is
/// gated behind the exec WP calculus's structure — goal-position lets
/// (which `omega` treats as opaque atoms and plain `simp_all` will
/// not substitute: `zetaDelta` is off by default), datatype
/// discriminator/accessor applications on abstract scrutinees (stuck
/// matches until a `cases` splits the scrutinee), and `height`
/// termination measures (equation lemmas fire only on constructor
/// applications, i.e. after the same `cases`).
///
/// Shape: `intro <goal-spine names>; intros; cases _tactus_scrut_i :
/// <scrutinee> <;> … <;> simp_all +zetaDelta only [CORE, extras,
/// <goal-mentioned generated defs>] <;> omega`.
///
/// Everything here is DERIVED from the goal text plus the crate's own
/// generated-def inventory — deterministic, replayable, no search:
/// * intro names come from the goal's binder spine (named, not `_`,
///   so scrutinee terms can reference them; Lean shadowing keeps
///   duplicates sound, and the trailing `intros` mops any remainder);
/// * scrutinees are the (let-substituted, span-stripped) bases of the
///   goal's discriminator/accessor projections and match scrutinees,
///   first-occurrence order, deduped, capped at 3 (a goal needing
///   more fails loud — inline-proof surface, §3.4);
/// * unfold names are the generated defs the goal mentions, resolved
///   against types the goal/binders actually name (so a short field
///   name can never pull in a def of an unmentioned datatype).
///
/// The rung is ADDITIVE: it runs only after rfl/decide/omega, the
/// peeled kernel rungs, and the pool-validated CORE rung have all
/// failed, so its reach cannot regress previously-closing goals.
pub(crate) fn structural_rung(
    goal: &Expr,
    dts: &DtDefInventory,
    binders: &[Binder],
    user_prefix: bool,
) -> String {
    let scan = run_structural_scan(goal, dts, binders);

    let mut steps: Vec<String> = Vec::new();
    // Named spine intros mirror the EMITTED goal. A user tactic
    // prefix (`proof { simp_all … }`) runs before this rung and may
    // reshape the goal arbitrarily (simp zeta-reduces goal lets,
    // closes trivial antecedents) — the emitted-shape names then
    // fail `introN` loudly. Under a prefix, use bare `intros` only:
    // cases targets are let-substituted at derivation (they
    // reference params/theorem binders, not spine names), so they
    // survive the prefix.
    let intro_names = spine_intro_names(goal);
    if !user_prefix && !intro_names.is_empty() {
        steps.push(format!("intro {}", intro_names.join(" ")));
    }
    steps.push("intros".to_string());
    let prefix = steps.join("; ");

    let mut unfolds: Vec<String> = scan.unfolds.iter().cloned().collect();
    // (constructor .injEq derivation lives in simp_tail_from_unfolds)
    unfolds.extend(scan.mentioned_spec_fns.iter().cloned());
    unfolds.sort();
    let tail = simp_tail_from_unfolds(&mut unfolds, &scan);

    let cases: Vec<String> = scan.targets.iter().take(3).enumerate()
        .map(|(i, t)| format!("cases _tactus_scrut_{} : {}", i, t))
        .collect();
    if cases.is_empty() {
        format!("{}; {}", prefix, tail)
    } else {
        format!("{}; {} <;> {}", prefix, cases.join(" <;> "), tail)
    }
}

/// Named intro tokens for the goal's leading binder spine (∀ binders,
/// goal-position lets, implication antecedents). Names mirror the
/// binders so `structural_rung`'s scrutinee terms can reference them
/// after intro; antecedents intro as `_` (hypotheses are consumed by
/// `simp_all`, never referenced by name). Stops at the first
/// non-spine node.
fn spine_intro_names(goal: &Expr) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = goal;
    loop {
        match &cur.node {
            ExprNode::SpanMark { inner, .. } => cur = inner,
            ExprNode::Forall { binders, body } => {
                for b in binders {
                    out.push(match &b.name {
                        Some(n) => n.as_str().to_string(),
                        None => "_".to_string(),
                    });
                }
                cur = body;
            }
            ExprNode::Let { name, body, .. } => {
                out.push(name.as_str().to_string());
                cur = body;
            }
            ExprNode::BinOp { op: BinOp::Implies, rhs, .. } => {
                out.push("_".to_string());
                cur = rhs;
            }
            _ => break,
        }
    }
    out
}

/// Goal walker backing `structural_rung`. Two passes: type-mention
/// collection (pass 1) so short accessor names resolve only against
/// datatypes the goal actually names, then the substituting walk
/// (pass 2) that gathers unfold names and cases targets.
struct StructuralScan<'a> {
    dts: &'a DtDefInventory,
    mentioned_types: std::collections::HashSet<String>,
    mentioned_spec_fns: std::collections::HashSet<String>,
    unfolds: std::collections::BTreeSet<String>,
    targets: Vec<String>,
    targets_seen: std::collections::HashSet<String>,
}

impl<'a> StructuralScan<'a> {
    fn new(dts: &'a DtDefInventory) -> Self {
        StructuralScan {
            dts,
            mentioned_types: Default::default(),
            mentioned_spec_fns: Default::default(),
            unfolds: Default::default(),
            targets: Vec::new(),
            targets_seen: Default::default(),
        }
    }

    /// Pass 1: every full name the goal mentions (`Var` nodes — type
    /// ascriptions, constructor heads, def applications) marks its
    /// dotted prefixes as mentioned types.
    fn collect_mentioned_types(&mut self, e: &Expr) {
        if let ExprNode::Var(n) = &e.node {
            let s = n.as_str();
            for (i, ch) in s.char_indices() {
                if ch == '.' && self.dts.by_type.contains_key(&s[..i]) {
                    self.mentioned_types.insert(s[..i].to_string());
                }
            }
            if self.dts.by_type.contains_key(s) {
                self.mentioned_types.insert(s.to_string());
            }
            if self.dts.spec_fns.contains(s) {
                self.mentioned_spec_fns.insert(s.to_string());
            }
        }
        e.for_each_child(&mut |c| self.collect_mentioned_types(c));
    }

    /// Full unfold names for a short accessor/discriminator name,
    /// resolved against mentioned types only.
    fn resolve_short(&self, short: &str) -> Vec<String> {
        let mut out = Vec::new();
        for t in &self.mentioned_types {
            if self.dts.by_type.get(t).map_or(false, |set| set.contains(short)) {
                out.push(format!("{}.{}", t, short));
            }
        }
        out
    }

    fn push_target(&mut self, e: &Expr, env: &std::collections::HashMap<String, Expr>) {
        let sub = subst_lets(e, env);
        let text = crate::lean_pp::pp_expr(&sub);
        // Guards: single-line, modest size (a monster term as a cases
        // target helps nobody — fail loud instead), not a literal.
        if text.contains('\n') || text.len() > 120 || text.is_empty() {
            return;
        }
        if matches!(sub.node, ExprNode::Lit(_) | ExprNode::LitBool(_)) {
            return;
        }
        if self.targets_seen.insert(text.clone()) {
            self.targets.push(text);
        }
    }

    fn walk(&mut self, e: &Expr, env: &std::collections::HashMap<String, Expr>) {
        match &e.node {
            ExprNode::SpanMark { inner, .. } => self.walk(inner, env),
            ExprNode::Let { name, value, body } => {
                self.walk(value, env);
                let mut env2 = env.clone();
                env2.insert(name.as_str().to_string(), subst_lets(value, env));
                self.walk(body, &env2);
            }
            ExprNode::Forall { binders, body }
            | ExprNode::Exists { binders, body }
            | ExprNode::Lambda { binders, body } => {
                let mut env2 = env.clone();
                for b in binders {
                    self.walk(&b.ty, env);
                    if let Some(n) = &b.name {
                        env2.remove(n.as_str());
                    }
                }
                self.walk(body, &env2);
            }
            ExprNode::FieldProj { expr, field } => {
                self.walk(expr, env);
                let resolved = self.resolve_short(field);
                if !resolved.is_empty() {
                    for name in resolved {
                        self.unfolds.insert(name);
                    }
                    self.push_target(expr, env);
                }
            }
            ExprNode::Match { scrutinee, arms } => {
                self.walk(scrutinee, env);
                self.push_target(scrutinee, env);
                for arm in arms {
                    self.walk(&arm.body, env);
                }
            }
            ExprNode::App { head, args } => {
                if let ExprNode::Var(n) = &head.node {
                    let s = n.as_str();
                    if let Some(dot) = s.rfind('.') {
                        let (t, short) = (&s[..dot], &s[dot + 1..]);
                        if self.dts.by_type.get(t).map_or(false, |set| set.contains(short)) {
                            self.unfolds.insert(s.to_string());
                        }
                    }
                }
                self.walk(head, env);
                for a in args {
                    self.walk(a, env);
                }
            }
            _ => e.for_each_child(&mut |c| self.walk(c, env)),
        }
    }
}

/// Substituting clone: goal-`let` bindings inlined (matching what
/// `+zetaDelta` will do in the rung's simp), `SpanMark` comments
/// stripped (they would inject `/- @rust … -/` into tactic text).
/// Binder shadowing removes env entries, so capture is respected.
fn subst_lets(e: &Expr, env: &std::collections::HashMap<String, Expr>) -> Expr {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => subst_lets(inner, env),
        ExprNode::Var(n) => match env.get(n.as_str()) {
            Some(v) => v.clone(),
            None => e.clone(),
        },
        ExprNode::Let { name, value, body } => {
            let mut env2 = env.clone();
            env2.insert(name.as_str().to_string(), subst_lets(value, env));
            subst_lets(body, &env2)
        }
        ExprNode::Forall { binders, body } => {
            let mut env2 = env.clone();
            let bs = binders.iter().map(|b| {
                let b2 = crate::lean_ast::Binder {
                    name: b.name.clone(),
                    ty: subst_lets(&b.ty, env),
                    kind: b.kind,
                };
                if let Some(n) = &b.name {
                    env2.remove(n.as_str());
                }
                b2
            }).collect();
            Expr::new(ExprNode::Forall { binders: bs, body: Box::new(subst_lets(body, &env2)) })
        }
        ExprNode::Exists { binders, body } => {
            let mut env2 = env.clone();
            let bs = binders.iter().map(|b| {
                let b2 = crate::lean_ast::Binder {
                    name: b.name.clone(),
                    ty: subst_lets(&b.ty, env),
                    kind: b.kind,
                };
                if let Some(n) = &b.name {
                    env2.remove(n.as_str());
                }
                b2
            }).collect();
            Expr::new(ExprNode::Exists { binders: bs, body: Box::new(subst_lets(body, &env2)) })
        }
        ExprNode::Lambda { binders, body } => {
            let mut env2 = env.clone();
            let bs = binders.iter().map(|b| {
                let b2 = crate::lean_ast::Binder {
                    name: b.name.clone(),
                    ty: subst_lets(&b.ty, env),
                    kind: b.kind,
                };
                if let Some(n) = &b.name {
                    env2.remove(n.as_str());
                }
                b2
            }).collect();
            Expr::new(ExprNode::Lambda { binders: bs, body: Box::new(subst_lets(body, &env2)) })
        }
        _ => Expr::new(crate::lean_ast::map_children(&e.node, |c| subst_lets(c, env))),
    }
}

/// Names that are known to be Int/Nat-valued (term layer) or
/// let-bound propositions (prop layer) in the current scope. A bare
/// `Var` is admitted as an integer TERM atom ONLY if it is in
/// `int_vars` — never merely because it "looks like a variable". This
/// is the load-bearing invariant: a global reference such as a
/// nullary spec fn (`test_crate.pair`, which renders as a bare `Var`,
/// not an `App`) is NOT a local integer, so `pair = pair` must fall
/// out of the arithmetic fragment rather than be handed to omega.
/// (Regression exposed by the bootstrap merge: the package-check path
/// emits that obligation as a `theorem := by <closer>` — which S1
/// classifies — whereas the islands path emitted it as a `Prop` def
/// that selection never saw. Being global-blind here fixes it for
/// both paths.)
#[derive(Default, Clone)]
struct Env {
    int_vars: std::collections::HashSet<String>,
    prop_vars: std::collections::HashSet<String>,
}

/// Classify a fully-wrapped obligation goal. `binders` are the
/// theorem's binders (fn params, requires-hypotheses — whose TYPES are
/// the hypothesis propositions — and any extras). Returns `None` when
/// the goal is not certainly in the fragment.
pub(crate) fn select_deterministic(goal: &Expr, binders: &[Binder]) -> Option<Selection> {
    let mut used = std::collections::HashSet::new();
    collect_var_names(goal, &mut used);

    // Seed the typing environment: every Int/Nat-typed binder is a
    // known integer term variable. (Built from ALL binders, not just
    // used ones — harmless, and a hypothesis over a param needs the
    // param present regardless of goal mentions.)
    let mut env = Env::default();
    for b in binders {
        if let Some(name) = &b.name {
            if frag_type(&b.ty) {
                env.int_vars.insert(name.as_str().to_string());
            }
        }
    }

    // N1 (let-hoisting): definitional-equation hypotheses `h : x = v`
    // CONSTRAIN their variable — when the goal mentions `x`, omega
    // needs the equation, so `v` must be in-fragment or the selection
    // is a completeness misfire (observed: `val = Int.ofNat 1` — the
    // classifier saw only Int-typed `val` in the goal, selected bare
    // omega, and omega treated the un-normalized `Int.ofNat` atom as
    // opaque). Chase mentions through equation RHSs to a fixpoint
    // (chained lets: `x = y + 1`, `y = z * 2`, …), rejecting on any
    // out-of-fragment equation over a mentioned variable.
    loop {
        let mut changed = false;
        for b in binders {
            let ExprNode::BinOp { op: BinOp::Eq, lhs, rhs } = &b.ty.node else {
                continue;
            };
            let ExprNode::Var(v) = &lhs.node else { continue };
            if !used.contains(v.as_str()) {
                continue;
            }
            if !frag_term(rhs, &env) {
                return None;
            }
            let before = used.len();
            collect_var_names(rhs, &mut used);
            if used.len() != before {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Every binder the goal mentions must itself be in-fragment: an
    // Int/Nat variable, or a hypothesis whose proposition is
    // in-fragment. Binders the goal never mentions (opaque receivers,
    // type params) are irrelevant.
    for b in binders {
        let Some(name) = &b.name else { continue };
        if !used.contains(name.as_str()) {
            continue;
        }
        if !frag_type(&b.ty) && !frag_hyp(&b.ty, &env) {
            return None;
        }
    }

    let mut wrapped = false;
    if frag_prop(goal, true, &mut wrapped, &mut env) {
        Some(if wrapped { Selection::PeelOmega } else { Selection::Omega })
    } else {
        None
    }
}

fn collect_var_names(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.node {
        ExprNode::Var(n) => {
            out.insert(n.as_str().to_string());
        }
        _ => e.for_each_child(|c| collect_var_names(c, out)),
    }
}

/// Is `ty` an arithmetic scalar type?
fn frag_type(ty: &Expr) -> bool {
    matches!(&ty.node, ExprNode::Var(n) if matches!(n.as_str(), "Int" | "Nat"))
}

/// Is `ty` an in-fragment hypothesis PROPOSITION (a requires-binder's
/// type)? Must be proposition-shaped at the top — a comparison,
/// connective, or negation — so bare opaque type names (`Tactus.Ref`,
/// type params, `Bool`) are rejected rather than sliding through the
/// prop walk. The inner check uses the current `env` so operands
/// resolve against the known integer variables (a hypothesis over an
/// unknown global is rejected).
fn frag_hyp(ty: &Expr, env: &Env) -> bool {
    let mut env = env.clone();
    let mut wrapped = false;
    match &ty.node {
        ExprNode::SpanMark { inner, .. } => frag_hyp(inner, &env),
        ExprNode::BinOp { op, .. } => matches!(
            op,
            BinOp::And | BinOp::Or | BinOp::Iff | BinOp::Implies
            | BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        ) && frag_prop(ty, false, &mut wrapped, &mut env),
        ExprNode::UnOp { op: UnOp::Not, .. } => {
            frag_prop(ty, false, &mut wrapped, &mut env)
        }
        _ => false,
    }
}

/// Two-layer fragment check — omega's actual domain:
/// * TERM layer: Int/Nat-valued — vars, literals, +,-,neg, *literal,
///   /literal, %literal, toNat atoms.
/// * PROP layer: comparisons over TERMS, Eq/Ne over TERMS (NOT over
///   props — propositional equality like `r = (x > 0)` is rfl/simp
///   territory, omega rejects it; the v1 bug this layering fixes),
///   connectives over props, ¬, and spine wrappers.
///
/// `let`-bound variables carry their layer: a var bound to a PROP
/// (`let r := x > 0; …`) is a prop atom — admissible as a conjunct
/// (peel's zeta-substitution turns it back into the comparison) but
/// NOT as an Eq operand.
///
/// `spine` is true while on the leading spine (∀ bodies, `let` bodies,
/// `→` right-hand sides) — positions `tactus_peel` can intro. Wrappers
/// are only admitted on the spine; `wrapped` records one was seen.
fn frag_prop(
    e: &Expr,
    spine: bool,
    wrapped: &mut bool,
    env: &mut Env,
) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_prop(inner, spine, wrapped, env),

        // A bare var in prop position must be a let-bound prop atom
        // (peel substitutes it back into its comparison). Term-typed
        // vars are not props; Bool params were already rejected by the
        // binder check (Bool is out of the fragment).
        ExprNode::Var(n) => env.prop_vars.contains(n.as_str()),
        ExprNode::LitBool(_) => false, // True/False goals: out (v1)

        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::And | BinOp::Or | BinOp::Iff => {
                frag_prop(lhs, false, wrapped, env)
                    && frag_prop(rhs, false, wrapped, env)
            }
            // `→` continues the spine on the right; the left is a
            // hypothesis peel will intro.
            BinOp::Implies => {
                if spine {
                    *wrapped = true;
                }
                frag_prop(lhs, false, wrapped, env)
                    && frag_prop(rhs, spine, wrapped, env)
            }
            // Comparisons and equality: TERM operands only.
            BinOp::Eq | BinOp::Ne
            | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                frag_term(lhs, env) && frag_term(rhs, env)
            }
            _ => false,
        },

        ExprNode::UnOp { op: UnOp::Not, arg } => {
            frag_prop(arg, false, wrapped, env)
        }

        // Wrappers: admitted on the spine only.
        ExprNode::Forall { binders, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            for b in binders {
                if frag_type(&b.ty) {
                    // Int/Nat quantified var — enters scope as a term.
                    if let Some(name) = &b.name {
                        env.int_vars.insert(name.as_str().to_string());
                    }
                } else if !frag_hyp(&b.ty, env) {
                    // Not an int var and not a hypothesis prop → out.
                    return false;
                }
            }
            frag_prop(body, true, wrapped, env)
        }
        ExprNode::Let { name, value, body } => {
            if !spine {
                return false;
            }
            *wrapped = true;
            if frag_term(value, env) {
                // Term-bound: the var is a known integer term.
                env.int_vars.insert(name.as_str().to_string());
            } else if frag_prop(value, false, &mut false, env) {
                env.prop_vars.insert(name.as_str().to_string());
            } else {
                return false;
            }
            frag_prop(body, true, wrapped, env)
        }

        _ => false,
    }
}

/// TERM layer: Int/Nat-valued expressions omega treats as linear
/// arithmetic atoms/terms.
fn frag_term(e: &Expr, env: &Env) -> bool {
    match &e.node {
        ExprNode::SpanMark { inner, .. } => frag_term(inner, env),
        ExprNode::TypeAnnot { expr, ty } => {
            frag_type(ty) && frag_term(expr, env)
        }
        // A bare Var is a term atom ONLY if it is a KNOWN integer local
        // (binder / ∀-Int-binder / term-let). Globals — including
        // nullary spec fns that render as bare `Var` (`test_crate.pair`)
        // — are NOT locals, so they fall out of the fragment. This is
        // the load-bearing conservatism: omega would treat an unknown
        // atom as a free variable and might close `pair = pair` by
        // chance, but `pair`'s VALUE (a Seq) makes that unsound in
        // general, and the goal wants rfl/simp, not omega.
        ExprNode::Var(n) => env.int_vars.contains(n.as_str()),
        ExprNode::Lit(_) => true,
        ExprNode::BinOp { op, lhs, rhs } => match op {
            BinOp::Add | BinOp::Sub => {
                frag_term(lhs, env) && frag_term(rhs, env)
            }
            // Linear only: multiplication by a literal.
            BinOp::Mul => {
                (is_lit(lhs) || is_lit(rhs))
                    && frag_term(lhs, env)
                    && frag_term(rhs, env)
            }
            // omega supports div/mod by integer literals.
            BinOp::Div | BinOp::Mod => is_lit(rhs) && frag_term(lhs, env),
            _ => false,
        },
        ExprNode::UnOp { op: UnOp::Neg, arg } => frag_term(arg, env),
        // omega-native cast atoms: `e.toNat` / `Int.toNat e`.
        ExprNode::FieldProj { expr, field } if field == "toNat" => {
            frag_term(expr, env)
        }
        ExprNode::App { head, args } => {
            matches!(&head.node,
                ExprNode::Var(n) if matches!(n.as_str(), "Int.toNat" | "Int.natAbs"))
                && args.len() == 1
                && frag_term(&args[0], env)
        }
        _ => false,
    }
}

fn is_lit(e: &Expr) -> bool {
    match &e.node {
        ExprNode::Lit(_) => true,
        ExprNode::UnOp { op: UnOp::Neg, arg } => is_lit(arg),
        ExprNode::TypeAnnot { expr, .. } => is_lit(expr),
        _ => false,
    }
}

#[cfg(test)]
#[path = "tests/tactic_select.rs"]
mod tests;
