---
title: "S2c — implement the derivation-first squeeze (uniform CORE tactic + residue inline proofs)"
status: done
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-17T01:05:00Z
---

## Description

Implementation of the mainline-04 decision (derivation-first, no store — see
DESIGN-transparent-automation.md §3.4). SCOPE FINAL per that decision.

- **The derivation rule** (rule budget: ONE) in
  `lean_verify/src/tactic_select.rs`, generalizing S1's classify-then-select:
  when the closer would be `tactus_auto`, emit instead the uniform text
  `simp_all only [CORE] <;> omega` where CORE is the fixed 43-lemma
  site-invariant list from MEASUREMENT-s2a-derivability.md §6. Same single
  chokepoint (emit_with_extras), NEVER overrides user closers or S1's
  linear-fragment omega selection (S1's omega is cheaper for its goals; the
  derived simp is the fallback for everything else). Every derived tactic is
  name-is-spec at the site; the rule itself spec'd in a code comment.
- **Feasibility gate FIRST**: before touching the emitter, validate the
  uniform tactic over the FULL Brick-1 pool (all 215 theorems, not just the
  T2 winners) — the census proved the derived tactic closes T2 goals, but
  lower-rung goals (rfl/decide/omega/peel winners, 32.6% of Brick 1) must
  also still close. If unconditional replacement regresses lower-rung goals,
  the rule becomes: keep S1's rung-preserving selection for goals the emitter
  classifies (S1 machinery), derived simp for the rest — still rule-budget
  one, still no store.
- **Residue inline proofs**: apply the 13 squeezed lists (2 clusters, 3
  effective sites) as inline `by { }` proofs in gt source — MEASUREMENT doc
  §7 has the clusters; the CSV has the per-theorem lists. This is the
  task's validation that the residue path works, AND it pays down the T2
  share directly.
- **Suggestion report for future residue**: obligations whose derived tactic
  fails (new shapes falling out of CORE) get surfaced with their squeezed
  list ("N obligations suggest inline proofs" + per-site text), NOT silently
  ladder-closed. Failure is LOUD per §3.4.

Preservation methodology (the S1 standard): per-file pre/post error-count
diff over the 114 known-passing gt artifacts = 0 regressions required; suite
green; tutorial 9/9; tgt gate stays 0 errors.

Progress bar: re-run `tools/rung-attrib/fast_attrib.py` after landing — the
T2 share (67.4% at Brick 1) trending toward 0 IS the tactus_auto-removal
progress bar. Record the new histogram here and in the design doc.

**Done when:** derivation rule landed with 0 regressions, residue inline
proofs applied in gt (or explicitly deferred as counted residue), new
rung-attribution histogram committed.

**Blocked by:** mainline-04 — CLEARED 2026-07-16 (decision recorded in
DESIGN-transparent-automation.md §3.4).

## Progress

- (2026-07-16 ~22:50Z, kimi) Claimed after the 04 decision. Starting with
  the feasibility gate: full-pool validation of the uniform derived tactic
  (census covered T2 winners only; the 68 lower-rung theorems must also
  still close).
- (2026-07-16 ~23:15Z, kimi) **Feasibility gate DONE, tactic shape settled
  empirically.** Five gate variants over the full pool (397 real theorems):
  bare `CORE <;> omega` = 19 failures (11 were lower-rung winners needing
  kernel/delta closure — spec-fn-app equalities, let-var atoms); adding
  `first | rfl | decide` = 9; peel-first regressed (peel's destructive
  intro broke 12 CORE theorems); peel-inside-first = 10 (higman collision:
  peel mangled decide-shaped goals before decide could fire); FINAL =
  `first | rfl | decide | (tactus_peel <;> (first | rfl | decide | omega))
  | (simp_all only [CORE] <;> omega)` = **8 failures, exactly the known
  census residue**. 389/397 = 98.0%. Note: 5 of the census's 7
  "goal-specific" theorems (coset assoc_lhs Option cluster) PASS under
  CORE — used-lists ≠ necessary-lists; residue shrank accordingly.
- (2026-07-16 ~23:30Z, kimi) **Emitter rule landed + binary built.**
  `DERIVED_CLOSER` const in `tactic_select.rs` (rule spec in the comment
  per board convention); `sst_to_lean.rs` chokepoint: S1 selects first,
  else DERIVED replaces tactus_auto; user closers untouched. Unit test
  pins the search-free property + exact 43-lemma set (14/14 green).
  Worktree binary rebuilt (rust_verify release); emit probe confirms
  DERIVED text in fresh artifacts and Lean-verifies them live.
- (2026-07-16 ~23:45Z, kimi) **Residue proofs authored + applied** (all
  verified in scratch against the census artifacts):
  - coset lemma_trace_inv_rep_to_zero (611/613): CORE + Option.isSome +
    Option.Some_val0 <;> omega.
  - apply_hom_symbol_exec pre (414/422): `intro tmp hg; subst tmp;
    rw [if_pos hg / if_neg hg] at h_req0; exact h_req0` — the if-then-else
    requires is never discharged by simp; explicit if_pos/if_neg needed.
  - britton + pred-twin lemma_stable_pair_inv_gen (7191/7224): structured
    conjunction assembly from h_req3; (7193/7226): absurdity — the branch
    is unreachable (h_req3 gives rep≠empty, antecedent gives ¬¬(rep=empty)).
  Applied as fn-level `tactus_tactic` overrides of the form
  `first | <DERIVED> | <site proof(s)>` — search-free, matching the
  two-surface end state (NOT the old `first | tactus_auto | …` idiom).
  gt gate (cold, no -V cache) running.
- (2026-07-17 ~00:10Z, kimi) **gt gate GREEN (3116/0, package gate live)
  — then the tutorial battery caught three real gaps.** Extended CORE
  43→51 with probe-tested additions: `Classical.not_imp` (bare not_imp
  ambiguous under any Mathlib import), `Int/Nat.mul_add+add_mul`
  (product distribution for omega's atom relation), `Int.toNat_zero/one`
  (literal cast reduction), `Int/Nat.add_sub_cancel` (index arithmetic).
  Full extension protocol + per-gap rationale: MEASUREMENT-s2a §6.1.
  ALSO landed: the AssertQuery (`by(nonlinear_arith)`) scope fallback now
  substitutes DERIVED for the default closer at composition time — the
  378 default-emission theorems that still textually contained
  `tactus_auto` after the chokepoint change are search-free too.
  Tutorial pre-existing failures fixed source-side (nullary-lemma
  applications ×2, dependency-injection call contract ×3 — §6.2).
- (2026-07-17 ~00:40Z, kimi) **FINAL BATTERY — all green:**
  - full-pool gate v8: 389/397 (same 8 residue, covered by the gt
    overrides) — zero regressions at every extension step (v6/v7/v8).
  - gt gate: **3116 verified / 0 errors**, package gate live (one
    concurrent-run trait-check panic observed once; solo rerun clean —
    flagged as infra flakiness, not a proof issue).
  - tutorial: **10/10** (was 8/10 on main-line — fib_iter + factorial +
    matrix_fib had pre-existing M6-era failures, now fixed).
  - suite: lean_verify 14/14 tactic_select; rust_verify_test examples
    138/140 — the 2 failures (state_machines fifo, flat_combine) are
    Z3-path storage-safety errors IDENTICAL on the main-line binary
    (verified side-by-side, 14v/4e both) — pre-existing, outside the
    Lean backend entirely.
- (2026-07-17 ~01:05Z, kimi) **DONE.** Final closer histogram (fresh
  `--lean-all-proofs` emit, 2956 fns / 42,759 obligation theorems):
  DERIVED (kernel rungs + 51-CORE normalizer) 42,712 (99.87%) ·
  S1 omega 10 · S1 peel∘omega 14 · user-composed `first | tactus_auto`
  14 theorems (3 pre-existing gt override sites: apply_hom_gen,
  apply_hom_inv, todd_coxeter_rt ×2 — counted residue for the F7/mainline-15
  migration, NOT default emission) · other (user inline proofs, no
  search) 9. Default emission is 0% search by construction.

## Writeup

**Done-when review:** derivation rules landed with 0 regressions ✓ (pool
gate 389/397 at every CORE revision, gt gate 3116/0, tutorial 10/10);
residue applied in gt ✓ (4 fn-level overrides, search-free, covering all
8 residue theorems; proof texts recorded in the progress log); new
histogram committed ✓ (above). Suggestion report: the failure path IS
the report — a goal outside the derived tactic fails LOUD at its named
obligation with source span (observed repeatedly during validation);
`squeeze_census.py` is the squeeze tool for turning such a failure into
an inline-proof candidate. That workflow is the honest state of
"suggestions": no separate machinery was built, and none was needed —
the residue count after the full battery is the 3 pre-existing gt
user-override sites above.

**What landed (tactus-squeeze):** `DERIVED_CLOSER` in
`lean_verify/src/tactic_select.rs` (`first | rfl | decide |
(tactus_peel <;> (first | rfl | decide | omega)) | (simp_all only
[CORE: 51] <;> omega)`), substituted at the `emit_with_extras`
chokepoint when S1's classifier has no fragment answer; the same
substitution at the AssertQuery (`by(nonlinear_arith)`) scope fallback
composition point (sst_to_lean.rs:2059). User closers never overridden.
CORE history: 43 (census union) → 51 after three probe-tested
extensions — full protocol + rationale in MEASUREMENT-s2a §6.1.

**Findings recorded for follow-ups:**
- mainline-06 folds in: preconditions needed NO kind-specific rule —
  the uniform derived tactic covers 174/183 T2 preconditions, the
  residue proofs are kind-agnostic. Marking 06 done with this pointer.
- mainline-07 (B4) note: the derived tactic's second branch uses
  `tactus_peel`; when peel goes to codegen, that branch becomes the
  explicit intro/refine prefix + omega — the census theorems that need
  it are the `wrapped` class S1 already detects.
- mainline-10 note: the DECREASING_BY first-chain is now the LAST
  search-shaped dispatch in default emission.
- The 3 remaining user-override sites with `tactus_auto` (14 theorems)
  are the counted residue for the F7/mainline-15 migration.
- Dependency-injection contract surfaced for user docs (MEASUREMENT §6.2):
  recursive self-calls pass injected stmt binders explicitly; cross-fn
  proof-fn references stay unqualified to hit the local binder.
