---
title: "W5c — reference-WP soundness, Loop arm (init/maintain/decrease + havoc)"
status: todo
claimed_by:
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T21:30:00Z
---

## Description

W5 ladder rung (`DESIGN-W5-soundness.md` §4). Extend `ref_wp_sound` to
`StmData::Loop` — the WP loop rule, **where the structured bugs live**. The
`wp_stm` Loop arm emits init + body + maintain-reclose + decrease goals under the
`loop_maintain_frame` telescope (havoc modified locals via `havoc_lets`,
re-quantify + re-assert invariants/cond, snapshot decreases in a `_tactus_d_old`
let); `frame_after` uses `loop_use_frame` (havoc + ¬cond). The operational
semantics must model the loop as: invariant holds initially (init), is preserved
across an arbitrary iteration from a havoc'd state satisfying inv+cond (maintain),
the decreases measure strictly drops (decrease), and on exit inv+¬cond hold (use).

Partial correctness first; the decrease obligation is modeled but the
well-founded termination argument is its own family (master plan O6).

**Blocked by:** bootstrap-49 (W5a) + benefits from bootstrap-50 (W5b) for the
frame machinery. The hardest structured arm after W5d.

## Progress

## Writeup
