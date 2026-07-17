# BUG: phantom error diagnostics from backtracked `first` arms (Mathlib-importing crates)

**Date:** 2026-07-17
**Found by:** the squeeze-regression sweep (e2e `test_self_assign_mul_overflow_bound`),
bisected to a minimal repro the same day.
**Status:** diagnosed to the trigger conditions; exact Mathlib mechanism not yet
pinned. Interim handling options below; the structural fix is the leaf-normal
emission arc (`DESIGN-leaf-normal-emission.md`), which removes `first`-chains
from the common path entirely.

## Symptom

A theorem whose derived closer is a `first`-chain can be **soundly proved by a
later arm** while the file still FAILS verification: an earlier, backtracked
arm's `omega` failure remains in the message log as an error-severity
diagnostic, and `lean_process::check_lean_file` fails the file on any
error-severity diagnostic (`has_error`), independent of proof success.

Observed on `test_self_assign_mul_overflow_bound`: the obligation theorem is
closed by the structural rung (last arm); `#print axioms` shows
`[propext, Classical.choice, Quot.sound]` — no `sorryAx` — yet the file
reports `omega could not prove the goal` at the *peel arm's* leaf position and
the e2e test fails.

## Trigger conditions (all required, empirically)

1. `import Mathlib.Tactic.Linarith` in scope (directly or transitively — the
   generated `TactusDefs_*`/`TactusStmts_*` modules import it whenever the
   source crate does, so one user-level Mathlib import poisons every per-fn
   file of the crate). **Without the import the same file is clean.**
2. A `first` arm containing the B4 peel's conjunction branch —
   `refine ⟨by <leaf>, by <leaf>⟩` and the tactic-land variant
   `refine ⟨?_, ?_⟩ <;> <leaf>` both trigger — whose leaf fails on the
   conjunct goals.
3. A later arm that closes the theorem (otherwise the file is legitimately
   red and the phantom only degrades the error message).

Ruled out by bisection: heartbeats (10× budget, same failure), the
anonymous-constructor intro pattern (`intro ⟨_, _⟩` vs `intro h` — both
fail), term-level `by` blocks specifically (the `⟨?_, ?_⟩ <;>` form fails
too), the TactusPrelude (clean alone), goal-position lets alone, big
literals alone. One error diagnostic is logged **per failing conjunct
goal** (two for a two-conjunct refine), which is itself evidence that the
failure is being logged-and-continued rather than thrown — core Lean's
`<;>` aborts at the first failing goal and `first`'s message-log rollback
discards it.

## Minimal repro

Self-contained except for Mathlib on `LEAN_PATH` (use
`lake env printenv LEAN_PATH` from `lean-project/`). Remove the import →
0 errors. Keep it → 2 phantom errors, theorem still proved:

```lean
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option autoImplicit false
theorem t (x i : Int) (_h_ctx_4 : x = 0) :
    let d := i;
    (let tmp__1 := x;
     0 ≤ i + 1 ∧ i + 1 < 18446744073709551616 →
       0 ≤ tmp__1 * (i + 1) ∧ tmp__1 * (i + 1) < 18446744073709551616) := by
  first
    | (intro _; intro _; intro ⟨_, _⟩; refine ⟨?_, ?_⟩ <;> omega)
    | (intro d tmp__1 _; intros;
       simp_all +zetaDelta only [true_and, and_true] <;> omega)

#print axioms t   -- [propext, Classical.choice, Quot.sound] — no sorryAx
```

(The `omega` failures here are the let-opaque-atom class: `tmp__1` is a
let-fvar whose value omega does not unfold, so the two product atoms never
unify. The second arm substitutes via `+zetaDelta` and closes.)

## Impact

* Any Mathlib-importing crate under `--lean-backend` whose goals fall through
  to the peel arm's conjunction branch and get rescued by a later arm:
  currently the e2e tests with `import Mathlib.Tactic.Linarith`
  (`test_self_assign_mul_overflow_bound`, typed-renderer probes) and
  potentially tutorial chapters (they import Linarith for `nlinarith`).
* The reported error is misdirected even when the failure is real: it points
  at the backtracked arm's leaf, not the arm that should have closed.

## Open question

Which Mathlib/Batteries component breaks the message-log rollback (candidate
suspects: a `<;>`/seq-focus override, an `omega` frontend extension, an error
-recovery elaborator). Pin this before choosing interim option (ii) below —
a dodge aimed at the wrong mechanism will not hold.

## Interim handling options (until leaf-normal emission lands)

i.   Drop the conjunction branch from `render_peel` (conj goals fall to the
     CORE/structural arms, which handle ∧ via `omega`/`simp_all` natively).
     Needs pool-gate revalidation (the branch exists for per-conjunct
     rfl/decide closure).
ii.  Keep the branch but prevent the leaf from logging (blocked on the open
     question above).
iii. Reorder arms (structural before peel) — dodges the common case at a
     per-theorem cost (the structural arm is heavier), and phantom errors
     still fire whenever the peel arm runs and fails.

The structural fix is not on this list: leaf-normal emission
(`DESIGN-leaf-normal-emission.md`) removes multi-arm search from the common
path, so there is no backtracked arm to log anything.
