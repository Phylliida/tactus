---
title: "bootstrap-16 follow-up — If-with-early-return fall-through (find_square goals 6–11)"
status: todo
claimed_by:
created: 2026-07-14T12:00:00Z
updated: 2026-07-14T12:00:00Z
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

## Writeup
_when done_
