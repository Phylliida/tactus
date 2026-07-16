---
title: "W5-auth-3 — soundness proofs, Call/Ret/DeadEnd/Assign arms + frame-delta algebra (probe23 authored)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Author the probe23 (W5b) layer: extend the induction to
`{Assign, Call, Ret, DeadEnd}`, making the If fall-through live (Ret/DeadEnd
make divergence reachable, discharging the bootstrap-62 scaffold for these
arms).

Structure to mirror (probe23's design lifts):

- `frame_after f s = frame_append f (frameDelta s)` as a proof fn
  (`frame_after_eq_append`), + `frame_append_assoc` /
  `frame_append_fnil_right`.
- `holdsAll_close_each_e` (obligation-list safety, frame-agnostic — also the
  workhorse for Loop in bootstrap-64).
- `closeSem_ret_frame` (RetLet binds the return value).
- Note: refWp's Call is a **pass-through** over the serialized `post`
  FrameList (bootstrap-02b Option 1), so the Call arm here is frame algebra,
  not call semantics — the probe23 proof shape carries over directly.

**Done when:** tactus-core `--lean-all-proofs` 0 errors with the widened
induction covering `{Skip, Assume, Assert, Assign, Seq, If, Call, Ret,
DeadEnd}`; axiom closure clean; the If fall-through no longer scaffolded.

**Blocked by:** bootstrap-62.
