# Fixing the `--lean-all-proofs` real-run bug families — plan

**Date:** 2026-07-09
**Status:** planned; no code changes yet.
**Scope:** companion to `DESIGN-lean-all-proofs.md` §10. That section measured the crate-wide
real Lean run on tactus-group-theory (229 verified / 24,817 errors; 214 of 1,338 codegen'd fns
pass) and found the error mass is ~5 translator bug families, not proof-power. This doc specs
the fix for each family, with edit sites, design choices, sequencing, and acceptance criteria.

---

## TL;DR

| # | Family | Errors | Fns | Fix shape | Size |
|---|---|---:|---:|---|---|
| B1a | namespace shadowing | 2,203 | 552 | `_root_.`-qualify emitted global refs | S |
| B1b | Lean keyword collision (`prefix`) | 182 | ~40 | complete `is_lean_keyword` list | XS |
| B2 | choose-body lowering `(P j) ∧ j` | 2,596 | 440 | fix `BndX::Choose` epsilon form; unify VIR path | M |
| B3 | termination decreasing facts | 2,131 | 841 | preamble ordering + seeded decreasing tactic | M |
| B4 | `Inhabited T` synthesis | 713 | 569 | prefer `[Nonempty]` + `Classical.ofNonempty` in generated defs | S |
| B5 | `Option::deref` std spec; Int projection edge | 38 | ~30 | add std_specs def; investigate projection | XS/P2 |

Order **B1b → B1a → B2 → B3 → B4 → B5**: parse errors block whole files; B1a/B2 corrupt
hypotheses and so contaminate every downstream measurement. After all land: full crate re-run —
the residual `auto-tactic failed` count (currently 5,666 goals / 1,024 fns, overcounted) is the
**honest closer-vs-Z3-idiom migration workload**, which decides everything after this doc.
Each fix lands with a minimal repro test in the tactus test suite.

---

## B1a. Namespace shadowing (2,203 errors / 552 fns)

**Mechanism.** Every emitted file wraps all decls in `namespace lib` (crate name; see
DESIGN-lean-all-proofs §1 for why it's `lib`). References are emitted *relative*
(`symbol.generator_index`). When a Verus local is named `symbol` — pervasive in
tactus-group-theory — Lean's resolver prefers the local binder and falls into dot-notation
field lookup on its type: `symbol.generator_index` → look up
`lib.symbol.Symbol.generator_index` → "Invalid field". Top offenders: `Symbol` (751),
`inverse_symbol` (732), `symbol_valid` (710).

**Fix.** Emit global constant references fully qualified from the root:
`_root_.lib.symbol.generator_index`. `_root_.` bypasses local binders and namespace nesting
entirely, so the fix is total — it covers collisions with any current or future module segment,
datatype name, or the `lib` root itself, with no collision-set computation.

- Edit sites: wherever global `Fun`/datatype/constructor paths render to Lean names —
  `lean_name.rs` (`LeanName` from path) and the `var_lit`/app-head emission in
  `to_lean_expr.rs` / `to_lean_sst_expr.rs`. Must apply ONLY to true globals (paths), never
  to local binders/lets (VarIdents) — the two already flow through distinct types, so this
  should be a rendering change on the path-derived side only.
- Constructor names in **match-pattern position** need the same treatment (Lean accepts
  qualified names in patterns).
- Declaration positions (def/axiom/instance names inside `namespace lib`) stay relative —
  only *references* change.

**Rejected alternative:** renaming colliding binders. Needs a collision set, changes hypothesis
names in diagnostics (worse debugging), and is not future-proof.

**Acceptance:** crate-wide grep for `Invalid field` leaves only the `Option.deref` family (B5);
britton.rs / abelianization.rs shadowed fns re-run without name-resolution errors.

---

## B1b. Lean keyword collisions (182 errors)

**Mechanism.** Verus locals named `prefix` (common in word-manipulation proofs) emit raw and
hit Lean's reserved token: `unexpected token 'prefix'; expected ...` — a parse error that kills
the whole theorem. `sanitize()` (`to_lean_type.rs:375`) already «»-quotes keywords, but
`is_lean_keyword` (`to_lean_type.rs:386`) is a ~30-word hand list missing `prefix`, `postfix`,
`infix`/`infixl`/`infixr`, `notation`, `macro`, `macro_rules`, `syntax`, `elab`, `attribute`,
`axiom`, `opaque`, `noncomputable`, `partial`, `unsafe`, `mutual`, `deriving`, `in`, `calc`,
`from`, `rec`, `this`, `set_option`, …

**Fix.** Extend `is_lean_keyword` to Lean 4's full reserved-token set (transcribe from the Lean
source; cite the upstream file in a comment). Keep the «»-quoting mechanism as-is.

**Also verify:** the failures were *parse* errors, so confirm every binder-name path routes
through `sanitize()` — in particular `LeanName::from_var_ident` (used at
`to_lean_sst_expr.rs:1261`) vs `vir_var_binders_to_ast`. If a path bypasses it, that's the real
bug and the list fix alone won't close it.

**Acceptance:** `pred_britton_via_tower` / `britton_via_tower` / `pred_homomorphism` parse
errors gone; a unit test with locals named `prefix`, `calc`, `rec` passes.

---

## B2. Choose-body lowering (2,596 errors / 440 fns)

**Bug site:** `to_lean_sst_expr.rs:1283–1292`. `ExpX::Bind(BndX::Choose(bs, _, cond), body)`
renders `Classical.epsilon (fun bs => cond ∧ body)` — its own comment documents the wrong
form. For `choose|j: int| P(j)` the body is `Var j : Int`, so the lambda body is `Prop ∧ Int`:
ill-typed, and it poisons both value positions and the WP hypothesis side (the malformed
`(P j) ∧ j` shows up inside hypotheses of downstream goals).

**Semantics to implement.** Verus's choose returns `body` evaluated at *some* binding
satisfying `cond` (unconstrained if none exists — matching `Classical.epsilon` totality):

- Single binder: `(fun x => body) (Classical.epsilon (fun x => cond))` — or the `let`-form
  `let x := Classical.epsilon (fun x => cond); body`, which reads better and matches the
  epsilon rendering already emitted correctly elsewhere in the same files.
- Multi-binder: standard skolemization by nested epsilons —
  `let x₁ := Classical.epsilon (fun x₁ => ∃ x₂ … xₙ, cond);`
  `let x₂ := Classical.epsilon (fun x₂ => ∃ x₃ … xₙ, cond);` … then `body`.
  (Corpus note: multi-binder choose is rare here — CLAUDE.md's "two-step choose" idiom exists
  precisely because tuple-choose behaves badly on the Z3 side too.)

**Unify the divergent VIR path.** `to_lean_expr.rs:596–609` (`ExprX::Choose`) *ignores* `body`
(`body: _`) and emits `epsilon (fun params => cond)` — correct only for the single-binder,
body-is-the-var case; silently wrong otherwise (latent: spec-fn bodies with compound choose).
Extract one shared lowering helper and use it from both paths.

**Hypothesis side.** Confirm how the WP layer introduces the witness fact
(`cond[ε/x]` justified by `∃x, cond` — `Classical.epsilon_spec`). The malformed conjunction
appeared in hypothesis positions, so the same expression rendering feeds both; one fix should
clear both. Validate on `lemma_count_gives_witness` (britton.rs:167), which exercises choose +
recursion + trigger annotation together.

**Acceptance:** zero `Application type mismatch … ∧ <var>` in a crate re-run; choose-using fns
either pass or fail only in the `auto-tactic failed` family (which is then a fair measurement).

---

## B3. Termination decreasing facts (2,131 errors / 841 fns)

**Goal shapes:** `seq.Seq.len (Seq.drop_first w) < seq.Seq.len w` (+ `drop_last` variant)
≈ 93% of goals; `alpha / m < alpha` (Nat division) the rest. Hits recursive *spec-fn preamble
defs* and — new under `--lean-all-proofs` — recursive **proof fns** (e.g.
`lemma_count_gives_witness`, `decreases w.len()`).

**Root cause is already documented** in the `#[verifier::tactus_lean_axiom_eq]` comment
(`to_lean_fn.rs:227–238`): the measure fact `len (subrange s 1 (len s)) < len s` is a broadcast
axiom emitted AFTER the def in the preamble layout, so `decreasing_by` can't use it. The
attribute is the manual escape hatch (value axiom + `eq_def`; sound because Verus proved
SpecTermination on the Z3 side) — but it is **not applicable to proof fns** (theorems can't be
axiomatized), so under `--lean-all-proofs` the layout fix is mandatory, not optional.

**Fix (R1 — recommended).**
1. **Preamble ordering:** emit the Seq measure/broadcast axioms (subrange/drop_first/drop_last
   length facts) *before* recursive defs in the preamble layout (`crate_defs.rs` /
   `generate.rs` dep-order). This is the load-bearing half.
2. **Seed the decreasing tactic:** the current spec-fn tactic is
   `all_goals (simp_all; omega)` (`to_lean_fn.rs:1136`); theorems get `decreasing_by: None`
   (`sst_to_lean.rs:1698`) → Lean's default `decreasing_tactic`, which knows neither fact.
   Emit for both:
   `all_goals (first | (apply Nat.div_lt_self <;> omega) | (simp_all [<seq len lemma names>]; omega))`
   — enumerated rungs, no open-ended simp set, per the transparent-automation policy
   (`DESIGN-transparent-automation.md`). The theorem side plumbs through the existing
   `lean_pp.rs:341–352` rendering; only the population site changes.

**Rejected (R2):** auto-degrading recursive spec fns to the `axiom_eq` encoding when
`decreasing_by` fails. Silently widens the axiom surface — keep `axiom_eq` manual and explicit.

**Acceptance:** termination family drops to a handful of genuinely exotic measures (<100
errors); **zero new axioms**; existing `axiom_eq` users unaffected.

---

## B4. `Inhabited T` synthesis (713 errors / 569 fns)

**Mechanism (to pin at impl time).** Failing fns have *no* type params — the requirement comes
from preamble defs that demand `[Inhabited V]`, e.g. the payload projector
`@[simp] noncomputable def option.Option.Some_val0 {V} [Inhabited V] …`, instantiated at types
whose Inhabited instance chain is broken — while everything else in the pipeline threads
`[Nonempty A]` (every broadcast axiom binder). First step: run one failing file
(`britton__lemma_t_free_step_is_base_step.lean`) through `lake env lean` with
`set_option diagnostics true` to pin the exact unsatisfied instance.

**Fix.** Generated defs that need a default value are all `noncomputable` already — switch
their requirement from `[Inhabited V]` to `[Nonempty V]` + `Classical.ofNonempty`. `Nonempty`
is strictly weaker and is what tactus already threads everywhere, so the gap closes uniformly.
Keep `deriving Inhabited` on concrete datatypes (harmless, used elsewhere); keep the
`instInhabited` axioms for external types (`vec.Vec`, `seq.Seq`) — or downgrade those to
`Nonempty` too if nothing else needs Inhabited, shrinking the axiom surface (bonus, evaluate
during impl).

**Acceptance:** family → 0 on britton-module re-run; no new axioms (`Classical.ofNonempty` is
core Lean).

---

## B5. Small families

- **`Option` `.deref` emission (28 errors) — REDIAGNOSED during implementation
  (2026-07-09):** not a missing std-spec def. The receiver of an inlined
  `&self` spec method (`Option::is_some` → `option is Some`) carries a
  `Decorate(Ref, …)` on its SST **claimed** typ; the IsVariant arm of
  `exp_to_typed` (`to_lean_sst_expr.rs` ~687) counts ref-decorations off that
  claim and emits `.deref` — but the **actual** rendered value (a spec-fn
  call) is unwrapped, so `.deref` lands on a bare `option.Option` and fails
  dot-notation lookup. Note the adjacent variant-field access
  (`.Some_val0`, via `field_proj_opr`) does NOT peel and works — the two
  arms disagree on claimed-vs-actual. Fix belongs in the typed-spine
  (P1/P2, DESIGN-typed-renderer.md): the Call arm should report the
  ACTUAL rendered typ, or the IsVariant arm should count off actual like
  the Field arm claims to. Small blast radius but touches shared
  machinery — its own focused arc, NOT a quick patch. S→M.
- **`Invalid projection … kl has type Int` (10 errors, prop_v.rs):** tuple projection rendered
  against an Int-typed value — likely a let-bound tuple element already substituted by the
  time projection renders. Investigate during B2 (adjacent machinery). P2.
- **Heartbeats timeouts (~26 goals / ~11 fns):** leave untouched; revisit only after the
  post-fix measurement (perf is currently noise, not signal).

---

## Sequencing, gates, and measurement

**Order:** B1b → B1a → B2 → B3 → B4 → B5. Parse errors (B1b) kill whole files; B1a/B2 corrupt
hypotheses, so every measurement taken before they land undercounts real progress.

**Per-fix loop:**
1. Fix in `tactus/source/lean_verify/` (+ `vir/` if needed); `vargo build --release`.
2. Minimal repro test in the tactus test suite (the corpus bugs are all reproducible in
   5-line fns: a local named `prefix`; a local named after a module; a `choose`; a
   `decreases w.len()` recursion; a generic Option projection).
3. Module-scoped re-run on tactus-group-theory (`--verify-module britton` covers B1a/B2/B4;
   `base_swap`/`m4_qpow` cover B3).
4. **Regression gates — these fixes touch shared rendering paths used by exec fns:** tactus
   tutorial gates and the committed (non-`--emit-lean`) tactus-group-theory exec gate must stay
   green. Per `reference_tgt_gate_baseline_errors`: compare error *locations*, not counts.

**Final measurement:** full-crate `--lean-all-proofs` run (from the crate dir, no
`TACTUS_LEAN_OUT`; ~90 min). Update §10's table in the parent doc. The residual
`auto-tactic failed` population is then an honest number, and drives the next decision:
how much of the corpus wants explicit tactic blocks (migration) vs. closer rungs
(automation policy — see `DESIGN-transparent-automation.md`) vs. staying on Z3 via
`#[verifier::z3]`.

**Explicitly out of scope here** (follow-on, per parent doc §7): `StmX::DeadEnd` lowering,
multi-element `seq![a, b]` literals, and any closer changes. Also the check.sh hygiene item
(drop the uncommitted `--emit-lean` from the default line) — one line, do it when the
experimentation settles.

---

## Key file/line references

| What | Location |
|---|---|
| Keyword list + `sanitize()` | `lean_verify/src/to_lean_type.rs:375, 386` |
| Choose (SST path, the bug) | `lean_verify/src/to_lean_sst_expr.rs:1283–1292` |
| Choose (VIR path, ignores body) | `lean_verify/src/to_lean_expr.rs:596–609` |
| Binder name rendering | `lean_verify/src/lean_name.rs` (`LeanName::from_var_ident`) |
| Spec-fn decreasing tactic | `lean_verify/src/to_lean_fn.rs:1136` |
| Theorem decreasing (None) | `lean_verify/src/sst_to_lean.rs:1698` |
| `termination_by`/`decreasing_by` rendering | `lean_verify/src/lean_pp.rs:303–352` |
| `axiom_eq` escape hatch + ordering note | `lean_verify/src/to_lean_fn.rs:227–238` |
| Inhabited instance emission | `lean_verify/src/lean_ast.rs:110–111, 246–254` |
| Namespace wrapper (`namespace lib`) | emitted file header; `lean_verify/src/generate.rs` |
| Real-run taxonomy | `DESIGN-lean-all-proofs.md` §10 |
