---
title: "finding-3 follow-up — nested-loop _h_ctx counter (find_square bridge)"
status: todo
claimed_by:
created: 2026-07-14T09:35:00Z
updated: 2026-07-14T09:35:00Z
---

## Description

finding-3 (bootstrap-15) landed the loop-binder serializer and closed the
single-loop `sum_to` bridge by `decide`. The NESTED-loop fixture
`find_square` (2 loops) honest-fails (`goals_eq`→0) — a documented stage-A
caveat, fail-loud not silent-pass. This task closes that gap (a stretch
goal, only if it's worth the scope).

**Root cause.** The serializer's `loop_stm`
(`source/lean_verify/src/sst_serialize.rs`) resets `hyp_counter = 0` per
loop when minting `_h_ctx_N` names. But production's
`OblCtx::split_leading_binders` (`sst_to_lean.rs:1510`) counts from 0 over
the FULL accumulated `obl.frames` at each obligation — and for an INNER
loop the OUTER loop's mod-var ∀-binders + their bound/invariant/cond hyps
are STILL in scope (pushed by the outer `push_mod_var_frames` and never
popped). So the inner loop's leading hyps get `_h_ctx_<outer_hyp_count + k>`
in production, while the serializer emits `_h_ctx_k`. The binder-NAME ids
diverge → `goal_eq` (which compares name ids) → `goals_eq` = 0.

Likely also needs: multi-level `decreases` support (currently rejected via
`loop-multilevel-decrease`) if any nested fixture uses a lex measure, and
the refWp spec side may need to model the accumulated-frame counter too
(check whether the spec `wp_stm` Loop telescope already threads outer
binders — it does via the recursive `frame_after`/`f`, but the `_h_ctx`
NAMES are baked into the SST literal by the serializer, so this is
primarily a serializer-side counter fix).

## Approach sketch

- Thread an INCOMING `hyp_counter` base into `loop_stm` (the count of
  leading hyp frames already in scope from enclosing loops), rather than
  resetting to 0. The outer loop, when recursing into `self.stm(body)` for
  a body that contains an inner loop, must know how many of its own
  binders/hyps precede — i.e. pass down `mod-vars-with-bounds + invs + cond`
  hyp count. Care: the counter is per-OBLIGATION in production
  (split_leading_binders runs at each emit), but for a well-nested loop the
  leading-frame structure is the same at every inner obligation, so a
  static "outer hyp depth" carried through the recursion should match.
- Validate: `goals_eq (ref_wp cert_find_square_ctx cert_find_square_sst)
  cert_find_square_goals = 1 := by decide` closes (LEAN_PATH =
  tactus-core/out/lib + prelude-cache); negative-control a leaf.
- Regen recipe + prelude/LEAN_PATH details: see bootstrap-15 Progress.

## Progress
- (2026-07-14) Split out of bootstrap-15 as a documented stretch caveat.

## Writeup
_when done_
