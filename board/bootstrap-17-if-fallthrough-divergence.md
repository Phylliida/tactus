---
title: "bootstrap-16 follow-up — If-with-early-return fall-through (find_square goals 6–11)"
status: done
claimed_by: opus-b17
created: 2026-07-14T12:00:00Z
updated: 2026-07-14T15:00:00Z
---

## Description

bootstrap-16 landed the nested-loop (non-leading) telescope fix, which
closes find_square goals **0–5 and 12–16** by `decide`. The remaining
**goals 6–11 honest-fail** — they are exactly the goals downstream of the
inner loop's `if a * b == 36 { return a; }`, i.e. the "if-in-fall-through"
case DESIGN §2.4.1 explicitly excluded from the stage-A bridge-closes
subset. This task closes THAT gap (again, only if worth the scope).

**Two sub-gaps (both under the SST `StmData::If(c, nc, then, else)`):**

1. **Annotated branch hyps.** The SST If carries the BARE cond leaves
   (`c=36`, `nc=37`), but production's `Wp::Branch` (sst_to_lean:2112)
   pushes the ANNOTATED span_mark'd cond as each branch's hyp:
   `cond_marked` (`AssertKind::Hypothesis(BranchCondition)`) for the then-
   branch, `not(cond_marked)` for the else. In the find_square cert those
   are leaves **45** (`/- @rust:138:16 -/ a*b=36`) and **46** (`¬(…)`),
   used by goals 6 (then, `Imp 45`) and 7–11 (fall-through, `Imp 46`).
   Fix: the serializer must intern the annotated branch cond/¬cond leaves
   (via `oblig_leaf`/`neg_oblig_leaf` over the branch cond, kind
   `BranchCondition`), and the If node must carry them; refWp's If arm uses
   the annotated leaves for the branch hyps. SERIALIZER + refWp + regen.

2. **Continuation under ¬cond when the then-branch DIVERGES.** After
   `if C { return } rest`, production visits `rest` under `¬C` (the else
   path — the then-branch returned, so control only reaches `rest` when C
   was false). refWp's `frame_after(f, If) = f` (unchanged, §5.1 "join
   frames not merged") omits this `Imp 46`. Fix: when the then-branch
   diverges (its StmData ends in `Ret`) and the else is `Skip`,
   `frame_after` must return `f ++ FHyp(annotated ¬cond)`. Needs a
   "does this StmData end in Ret?" predicate in the spec (structural),
   plus the annotated ¬cond leaf from sub-gap 1.

**Careful / open questions:**
- The GENERAL if (both branches fall through) is genuinely harder —
  production CLONES `after` into both branches (`Wp::Branch` build), so the
  continuation is visited TWICE under c and ¬c. The flat StmData::If +
  separate-Seq-continuation model can't reproduce that without either
  cloning in the serializer or a join-merge in refWp. Scope THIS task to
  the DIVERGING-then case (what find_square needs); leave the two-way join
  as a further documented caveat.
- Changing the `If` node shape (adding annotated leaves) is an N2.1-style
  frozen-shape change → base-hash invalidation → full tactus-core re-verify
  + fixture regen. Batch with any other shape change.

## Approach sketch

- Add annotated `then_cond` / `else_cond` leaves to `StmData::If` (or a
  parallel pair), mirror `Assert`'s bare/annotated split.
- refWp `wp_stm` If arm: branch hyps use the annotated leaves.
- refWp `frame_after` If arm: `if ends_in_ret(then) && is_skip(else) {
  f ++ FHyp(else_cond_ann) } else { f }` (the two-way-join fallback stays
  `f`, honest-fail as today).
- Serializer: emit annotated branch cond leaves (kind `BranchCondition`).
- Validate: regen find_square, hand-run the per-goal bridge (see
  bootstrap-16 Progress for the `/tmp/b16-bridge` harness) — expect goals
  6–11 to close, giving a FULL find_square bridge.

## Progress
- (2026-07-14) Split out of bootstrap-16 after the nested-loop telescope
  fix landed. Root cause + leaf ids decoded from the on-disk find_square
  cert; the per-goal bridge harness (`/tmp/b16-bridge/BridgeFindSquare.lean`)
  pinpoints goals 6–11 as the ONLY remaining divergence.

- (2026-07-14, opus-b17) **Claimed. Code landed (serializer + refWp), NO
  StmData shape change — regen + validate pending.**

  **KEY SIMPLIFICATION vs the task's sketch: sub-gap 1 needs NO new If
  fields.** The `oblig_leaf` docstring notes the `AssertKind` never reaches
  the pp output — only `rust_loc` + `inner` do. So production's branch hyp
  `cond_marked = span_mark(loc, Hypothesis(BranchCondition), lower(cond))`
  interns to the SAME text as `oblig_leaf(cond) = span_mark(loc,
  Obligation(Plain), lower(cond))`, and `not(cond_marked)` matches
  `neg_oblig_leaf(cond)`. The BARE cond is never an obligation and used
  nowhere, so I just swapped the serializer's If arm from
  `exp_leaf`/`neg_leaf` → `oblig_leaf`/`neg_oblig_leaf` (existing `c`/`nc`
  slots now carry the ANNOTATED leaves). No frozen-shape change → no
  base-hash invalidation; only a fixture regen (the SST literal's cond ids
  change + full leaf-table renumber, same as finding-2/finding-3).
  Removed the now-dead `neg_leaf`.

  **Sub-gap 2 (frame_after divergence), tactus-core/lib.rs:**
  - New `is_skip(s) -> nat` and `diverges(s) -> nat` (structural, decide
    idiom): `diverges` = Ret/DeadEnd → 1; Seq → either half; If → both
    branches; else 0.
  - `frame_after`'s If arm: `if diverges(then)==1 && is_skip(else)==1 { f ++
    FHyp(nc) } else { f }`. The `nc` slot is now the annotated ¬cond, so the
    fall-through continuation gets `Imp <¬cond>` — matching production
    (which reaches `rest` only via the else path when the then-branch
    returns; its `after`-clone in the diverging then-branch yields no
    goals).
  - `wp_stm`'s If arm unchanged: `c`/`nc` are now annotated, so branch hyps
    are `Imp 45`/`Imp 46` automatically.
  - `StmData::If` docstring updated (leaves are ANNOTATED).

  **Hand-trace against the on-disk cert (pre-regen ids) confirms all 6:**
  goal 6 then-branch Ret → `… Imp 45(cond), Let 8 9, Leaf 7`; goals 7–11
  continuation under `frame_after = … ++ FHyp(46)` → `Imp 46, …` on the
  Assert/inv-reclose/decrease. Matches `cert_find_square_goals` 6–11 exactly.

  **No existing decide test regresses:** none walk an If through
  wp_stm/frame_after (`skeleton_kernel_computes`/`amended_shapes` only hit
  `stm_size`; `ref_wp_ret_return_binding` is Ret-only; the loop tests use
  `loop_*_frame`/`close` directly). Serializer `cargo check -p lean_verify`
  clean.

  **NEXT (mechanical): vargo release build the fork → re-emit find_square →
  verify tactus-core → regen the per-goal bridge harness from the FRESH cert
  (leaf ids renumber) → confirm goals 6–11 close by decide → add a permanent
  If-fallthrough mutation-kill decide test.**

- (2026-07-14, opus-b17) **DONE + VALIDATED END-TO-END. find_square now
  FULLY bridges — all 17 goals + the whole-list `goals_eq` close by
  `decide`.** vargo release build (vstd 1530/0) → tactus-core 42/0 →
  fixture re-emit 11/16 (unchanged) → fresh per-goal bridge (goals 0–16,
  incl. the previously-failing 6–11) + `goals_eq (ref_wp ctx sst) goals = 1`
  all pass, exit 0. Negative controls fire (flip `=1`→`=0` errors; mutate
  the SST If `nc` leaf 37→999 breaks exactly 6 checks = 5 fall-through goals
  + the whole-list bridge). Permanent `ref_wp_if_fallthrough_divergence`
  decide test baked in. Harness at `/tmp/b17-bridge/BridgeFindSquare.lean`.

## Writeup

**If-with-early-return fall-through — DONE + VALIDATED. find_square fully
bridges (17/17 goals + whole-list `goals_eq` by `decide`).**

### The two sub-gaps and how they closed

**Sub-gap 1 (annotated branch hyps) — NO StmData shape change needed.**
The task sketch anticipated adding annotated `then_cond`/`else_cond` fields
to `StmData::If` (an N2.1 frozen-shape change → base-hash invalidation). It
turned out unnecessary. The `oblig_leaf` docstring records that the
`AssertKind` never reaches the pp output — only `rust_loc` + `inner` do. So
production's branch hyp `cond_marked = span_mark(loc,
Hypothesis(BranchCondition), lower(cond))` interns to the SAME text as
`oblig_leaf(cond) = span_mark(loc, Obligation(Plain), lower(cond))`, and
`not(cond_marked)` matches `neg_oblig_leaf(cond)`. The BARE cond is never an
obligation and used nowhere, so I just swapped the serializer's If arm from
`exp_leaf`/`neg_leaf` → `oblig_leaf`/`neg_oblig_leaf` (existing `c`/`nc`
slots now carry the ANNOTATED leaves). refWp's `wp_stm` If arm was already
`FHyp(c)`/`FHyp(nc)` → the branch hyps became annotated automatically.
Removed the now-dead `neg_leaf`.

**Sub-gap 2 (continuation under ¬cond when then diverges) — refWp only.**
`frame_after`'s If arm was `f` (stage-A "join not merged", §5.1). Production
CLONES `after` into both branches; when the then-branch returns, its clone
yields no goals, so the post-if continuation's goals appear ONCE, under the
else path's `¬cond`. refWp reproduces this: `frame_after(f, If) = if
diverges(then) && is_skip(else) { f ++ FHyp(nc) } else { f }`. New
structural spec fns `is_skip(s) -> nat` and `diverges(s) -> nat`
(Ret/DeadEnd → 1; Seq → either half; If → both branches; else 0). `wp_stm`
If arm unchanged.

### Why it's sound (honest-fail, never silent-pass)

`goal_eq` is strict-structural (compares every id). A too-weak `diverges`
(or a non-Skip else) omits the `FHyp(nc)` and the continuation goals
honest-fail; a too-strong one adds a `¬cond` production never emitted and
they ALSO honest-fail. The `is_skip(else)` guard scopes this to the
diverging-then + trivial-else case (what find_square needs); the general
two-way if (both branches fall through, production clones `after` into both)
stays `frame_after = f` and honest-fails — the documented §2.4.1 caveat.

### Leaf-renumber note (the elegant part)

Regen kept the If node at `If 36 37`, but leaves 36/37 now hold the
ANNOTATED text (`/- @rust:…138:16 -/ a * b = 36` and its `¬`). Interning is
idempotent, so the goal side (which used to have separate annotated leaves
45/46) now references the same 36/37 — they collapsed. `stm_size` stayed 40
(the If structure is unchanged; only the leaf CONTENT differs).

### Validation

- tactus-core: **42 verified, 0 errors** (`diverges`/`is_skip`/`frame_after`
  fix + the new `ref_wp_if_fallthrough_divergence` decide test).
- find_square per-goal bridge (`/tmp/b17-bridge/BridgeFindSquare.lean`,
  LEAN_PATH = tactus-core/out/lib + prelude-e81fbf9a86375c12): `goal_count
  rw = 17`, ALL 17 `goal_eq` per-goal, AND `goals_eq rw
  cert_find_square_goals = 1` — all `by decide`, exit 0.
- Negative controls: flip whole-bridge `=1`→`=0` → `decide` errors; mutate
  SST If `nc` 37→999 → 6 checks break (the 5 fall-through goals + whole
  bridge). The fall-through `FHyp(nc)` is genuinely load-bearing.

### Assumptions / caveats

- **General two-way if not modeled** (both branches fall through; production
  visits `after` twice under c and ¬c). Stays `frame_after = f`,
  honest-fails. No fixture needs it yet; would need serializer cloning or a
  refWp join-merge — a further task if a corpus fn hits it.
- **`diverges` is conservative** (DeadEnd/Ret/Seq/If only). A branch that
  diverges via some other construct returns 0 → honest-fail, never
  silent-pass.
- Fixture `out/` is gitignored/regenerable; only `tactus-core/out` oleans +
  source are committed. Harness lives in `/tmp/b17-bridge` (as bootstrap-16's
  did).
