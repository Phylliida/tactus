---
title: "W5b — reference-WP soundness, Call + Ret arms (the exec call rule)"
status: todo
claimed_by:
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T21:30:00Z
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

## Writeup
