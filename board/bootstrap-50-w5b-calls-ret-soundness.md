---
title: "W5b — reference-WP soundness, Call + Ret arms (the exec call rule)"
status: done
claimed_by: opus-w5b-callret
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T23:55:00Z
---

## Description

W5 ladder rung (`DESIGN-W5-soundness.md` §4). Extend `ref_wp_sound` to the
`StmData::Call` and `StmData::Ret` arms:

- `Call { reqs, post }`: `wp_stm` closes each requires obligation
  (`close_each_e f reqs`) and `frame_after` appends the transcribed post-call
  frame `post` verbatim. The operational semantics must model the callee contract
  (requires must hold at the call; ensures may be assumed after) — the exec call
  rule that `DESIGN-emit-module` §4.4 explicitly leaves open. Cover both the
  ∀-path (`FBind(dest) FHyp(ret_bound) FHyp(ens)`) and the #128 ret-eq path
  (`FHyp(E_bound) FHyp(rest) FLet(dest, E)`) — see `StmData::Call` doc in lib.rs.
- `Ret(es, rb)`: `wp_stm` closes each ensures under `ret_frame f rb` (the
  return-value binding). Operationally, Ret is a normal-exit obligation.

**Blocked by:** bootstrap-49 (W5a — the close/frame machinery + oracle model).

## Progress

- (2026-07-14, opus-w5b-callret) Claimed. Read probe22 (W5a-1) + the emitted
  `lib` defs for `Call`/`Ret`/`ret_frame`/`frame_after`/`close_each_e`/
  `frame_append`. **Design decided:** the W5a-1 `addedHyp` (a single Prop
  threaded through `Seq`) cannot model `Call`'s `post` frame, which BINDS
  variables (∀-path `FBind(dest) FHyp(ens)`). So generalise the `Seq`
  continuation from `addedHyp a st → body st` to
  `closeSem (frameDelta a) st body`, where `frameDelta : StmData → FrameList`
  is the frame a statement appends. Consequences:
  - **Lemma B becomes a one-liner:** `frame_after f a = frame_append f
    (frameDelta a)` (new `frame_after_eq_append`, needs a new
    `frame_append_assoc` for the Seq arm) → then reuse probe22's
    `closeSem_append`. Retires probe22's recursive `closeSem_frame_after`
    (and `addedHyp` and `diverges_zero_of_inFragment`).
  - **Call/Ret** via a new `close_each_e` bridge:
    `holdsAll (close_each_e f l) st ↔ closeSem f st (obligsSafe l ·)`, where
    `obligsSafe l st = ∧ over deep obligations he(render_exp ·)`. `Ret`'s
    `ret_frame` handled by cases on `RetBind` + `closeSem_append`.
  - **If fall-through goes LIVE:** `frameDelta (If) = if diverges t = 1 ∧
    is_skip e = 1 then FHyp nc FNil else FNil` — no longer collapsed, because
    `Ret`/`DeadEnd` make `diverges = 1` reachable in-fragment. Non-vacuity
    witness: `if C { ret E } rest` forwards `¬C` into `rest`.
  - New `execSafe` arms: `Call reqs _ → obligsSafe reqs st`;
    `Ret es rb → obligsSafe es (retApply rb st)` (RetLet binds the return
    value); `DeadEnd b → execSafe b st`; `Assign → True` (folded into fragment).
  - Fragment extended to `{Skip,Assume,Assert,Assign,Seq,If,Call,Ret,DeadEnd}`.
  - Probe dir: `probe-w0/probe23_w5b_sem/`.
- (2026-07-14, opus-w5b-callret) **DONE — probe PASS.**
  `probe-w0/probe23_w5b_sem/` (`w5b_sem.lean` + `run.sh` + `REPORT.md`)
  elaborates against the REAL emitted `lib.*` — **rc=0, ~3.5s, zero warnings,
  axiom closure `[propext, Quot.sound]`.** All the machinery above went in as
  planned; the one empirical risk (does `execSafe`'s Seq arm — which recurses
  under `closeSem`'s lambda — pass `termination_by structural`?) **cleared on
  first compile.** Mechanical fixes only after that: `frameDelta` needed
  `noncomputable` (calls `lib.diverges`); `frame_append f FNil = f` needed a
  right-identity lemma (not `rfl`); example metavar-timing (`inFragment` proof
  wrapped in `by`). Four non-vacuity witnesses all bite (Call req; Ret RetLet
  return-bound state; live-If `frameDelta = FHyp nc FNil`; `if C {ret}(assert
  o)` needs `o` only under `hp nc`).

## Writeup

**W5b DONE (probe, `probe-w0/probe23_w5b_sem/`).** The reference WP is sound on
`{Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd}` over an arbitrary
frame telescope. rc=0, ~3.5s, axiom closure `[propext, Quot.sound]`. Full detail
in `probe-w0/probe23_w5b_sem/REPORT.md`.

- **What's proven / verified:** `wp_stm_sound : inFragment s → holdsAll (wp_stm
  f s) st → closeSem f st (execSafe s ·)` (main, arbitrary telescope, the full
  9-constructor fragment); `ref_wp_sound` over the genuine `lib.seed_frame`;
  four non-vacuity witnesses. All elaborate against the genuine emitted defs
  (`lib.wp_stm`/`frame_after`/`close_e`/`close_each_e`/`ret_frame`/
  `frame_append`/`goals_append`/`diverges`/`is_skip`).
- **The design lift (the crux):** Call's `post` frame BINDS variables (∀-path
  `FBind(dest) FHyp(ens)`, #128 ret-eq `FLet(dest, E)`), which W5a-1's
  single-`Prop` `addedHyp` can't model. So the `Seq` continuation became
  `closeSem (frameDelta a) st body` (the whole frame delta), and Lemma B became
  a corollary of the structural identity `frame_after f s = frame_append f
  (frameDelta s)` (`frame_after_eq_append`) + probe22's `closeSem_append`. This
  retires `addedHyp` and `diverges_zero_of_inFragment`; it reproduces W5a-1's
  single-FHyp threading exactly and covers `post` uniformly. Call/Ret close via
  a new `holdsAll_close_each_e` bridge (`obligsSafe`); Ret's `ret_frame` via
  `closeSem_ret_frame` (`RetLet` binds the return value into the state).
- **If fall-through is now LIVE.** With `Ret`/`DeadEnd` in-fragment, `diverges =
  1` is reachable, so `frameDelta (If) = if diverges t = 1 ∧ is_skip e = 1 then
  FHyp nc FNil else FNil` no longer collapses; `if C { ret } rest` forwards `¬C`
  into `rest` (witness F). The W5a-1 caveat is discharged.
- **Assumptions / honest partial:** (1) `execSafe` is DEFINED to mirror the
  reference's frame threading (reviewed non-circular, §2.2: obligation arms
  require the real obligation, witnesses prove it bites). (2) Soundness holds for
  ANY Call `post` frame — the W2b `decide` bridge separately validates the
  serializer's `post` against production. (3) Val-level, partial correctness
  (adequacy spine = W5f; Loop = W5c). (4) Still probe-first: authoring the model
  in tactus-core (loop closure) remains deferred (`DESIGN-W5-soundness.md` §4).
