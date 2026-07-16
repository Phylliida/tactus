---
title: "W5-auth-3 — soundness proofs, Call/Ret/DeadEnd/Assign arms + frame-delta algebra (probe23 authored)"
status: done
claimed_by: fable-b63
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T21:30:00Z
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

## Progress

- (2026-07-16, fable-b63) Scope shifted per bootstrap-61's plan note: the
  frameDelta algebra of hand-Lean W5b is NOT needed in the authored version
  (the W5c frame-carrying formulation retired it before authoring began);
  this rung = the obligs bridge. Landed: `cso_nil_true` + `cso_cons_split`
  (both st-generic FrameList inductions; with defunctionalized continuations
  the hand-Lean closeSem congr/triv/mono/and helper zoo collapses into these
  two) + `holds_all_close_each_e` (the frame-agnostic Call/Ret/Loop-groups
  bridge, st-param). First-try green: **121 verified, 0 errors**.

## Writeup

The one new closer ingredient: `cso_cons_split`'s FBind arm needs
∀-distribution over ∧, so its closer carries `[and_assoc, forall_and]`.
Everything else is the probe33 idiom verbatim. `holds_all_close_each_e`
takes the frame as an OPAQUE argument — this is what lets bootstrap-64's
Loop arm never decompose the havoc'd mframe/endf (the W5c Opt-2 payoff).
