---
title: "N3b — goal-side serialization via Wp provenance marks (the one production touch)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Serialize the production goals as `GoalData`. This is the ONLY brick that edits
the production emitter — keep the diff small and reviewable in isolation.

Spec: `DESIGN-N3-serializer.md` §5.

- The Wp assembly marks the `lean_ast` LExpr nodes IT constructs (binder
  telescope, hypothesis arrows, let-bindings) with a provenance flag — one
  added field/mark on nodes created in the walker, nothing else changes.
- `goal_serialize` walks the theorem statement: marked node ⇒ structural
  `GoalData` constructor; unmarked subtree ⇒ leaf (interned in the N3a table).
- Rationale (record in the diff): shape-directed parsing is ambiguous at the
  spine tail (a hypothesis can itself be `a ==> b` or `∀`). Provenance is
  non-circular — refWp recomputes structure independently and the `decide`
  equality validates the claim; a mismark fails the bridge, never silent-passes.
- `GoalList` order = production theorem order; each goal preceded by a comment
  carrying the production theorem name (O4 pairing).

**Done when:** cert files carry both the SST literal (N3a) and the GoalData
literal + shared leaf table; the provenance diff touches only the walker's node
construction + `goal_serialize`; suite green with flag off.

**Blocked by:** bootstrap-02 (N3a).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
