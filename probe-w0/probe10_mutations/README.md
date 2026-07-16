# W2b mutation-kill suite (bootstrap-07)

The sensitivity half of W2b. A green bridge proves nothing unless a *mismatch*
is provably rejected (DESIGN §2.4.2). This suite hand-perturbs the live
`add_capped` cert (4 goals — the canonical straight-line + return-binding fn)
and proves each single edit flips the verdict `goals_eq = 1 → 0`.

## How it works

`gen.py` reads `bootstrap-fixture/out/lib/cert/add_capped.cert.lean`, copies its
three defs (`ctx` / `sst` / `goals`) VERBATIM, and emits `Mutations.lean` with:

- **baseline** `goals_eq (ref_wp ctx sst) goals = 1 := by decide` — the
  unperturbed bridge closes;
- **5 mutations**, each a single structural edit, asserting
  `goals_eq (ref_wp ctx <sst'|goals'>) … = 0 := by decide` — a *positive*,
  kernel-checked proof that the edit flipped the verdict to 0.

`run.sh` regenerates and elaborates the file. A single `lean` run with exit 0
means: baseline closes AND all 5 perturbations are provably killed. If any
mutation failed to flip (still `= 1`), its `= 0 := by decide` example errors.

The perturbations are STRUCTURAL transforms (balanced-paren surgery / pattern
swaps), independent of specific leaf-id *values*, so the suite survives a
fixture regen that renumbers leaves. `Mutations.lean` is committed as browsable
evidence but is fully regenerable from `gen.py`.

## The five mutations (spanning the task's named classes)

| id  | edit | why it must flip |
|-----|------|------------------|
| mut1 change-leaf-id | goal0's obligation `Leaf N → Leaf 999999` | refWp folds the real leaf; RHS now references a leaf refWp never emits |
| mut2 reorder-goals  | swap goal0 ↔ goal1 in the GoalList | `goals_eq` is order-sensitive; refWp emits goals in walk order |
| mut3 drop-binder    | goal0 loses its outermost `∀` | refWp's seed telescope still has that binder |
| mut4 swap-hyps      | goal0's outer two binders swapped | binder order in refWp's telescope is fixed by seed order |
| mut5 sst-retbind    | SST `RetBind.RetLet v → RetLet 999999` (LHS `ref_wp` input!) | refWp then folds `Let … 999999` in goal3's return-let → no longer matches production |

mut1–mut4 perturb the **production goals** (the RHS refWp is compared against);
mut5 perturbs the **SST input to `ref_wp`** (proving the LHS is load-bearing,
not just the comparison) — the exact negative control the finding-4 writeup used
(`RetLet 13 16 → 13 99`).

## Non-vacuity (the checker really discriminates)

Meta-checked once by hand: flipping the baseline `= 1 → = 0` errors (baseline
genuinely closes at 1), and flipping a mutation `= 0 → = 1` errors (the mutation
genuinely differs). So the `decide`s distinguish equal from unequal — the pass
is not vacuous.

## Reproduce

    LEAN=<lean-v4.25.0> bash probe-w0/probe10_mutations/run.sh
