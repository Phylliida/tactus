---
title: "W6b — land the frozen ExprData/TypData/render_exp mirror types in tactus-core (the one cache-churning edit)"
status: todo
claimed_by:
created: 2026-07-14T02:40:00Z
updated: 2026-07-14T02:40:00Z
---

## Description

Second rung of the W6 ladder (`bootstrap-11`; design `DESIGN-W6-stageB.md` §4/§5;
shape frozen by the W6a probe `bootstrap-20`).

Land the shapes the probe froze into the shared crate, as **one clean edit**
(datatype churn invalidates the whole crate's verus-cache once — batch it):

- Add `ExprData` + `TypData` (+ `CastKind`) inductives to `tactus-core/lib.rs`,
  mirroring `probe-w0/probe12_w6a_castleaf/probe12_w6a_castleaf.lean` verbatim
  (hybrid leaf: structural cast/binOp/app/fieldProj/spanMark + `atom(id)`
  terminal carrying its interned id).
- Add structural `expr_size` / `typ_size` measures +
  `#[verifier::structural_decreases]` throughout (kernel-compute discipline,
  same as the stage-A mirrors).
- Add the Tier-1 reference `render_exp` / `render_typ` spec fns implementing
  `needs_nat_coercion` at explicit-clip / arith-operand / call-arg sites (the
  probe's `render_exp`).
- **Decide the `GoalData::Leaf` migration.** §6 leans **additive** first: add a
  `LeafE(ExprData)` variant rather than changing `Leaf(u64)` → `Leaf(ExprData)`
  (smaller diff, reversible, avoids re-touching every stage-A cert + refWp arm).
- Verify the crate kernel-computes: in-crate `decide` guard analogous to
  `skeleton_kernel_computes` (so the deep leaves stay `decide`-reducible on the
  bridge, as the probe's `#print axioms` confirmed for the standalone shapes).

**Done when:** `tactus-core` verifies with the new types + `render_exp`, an
in-crate `decide` guard confirms kernel-computation, and the crate's e2e/gate is
green (verdict-neutral — the new types are additive, not yet wired into the
bridge; that's W6c/W6d).

**Blocked by:** nothing (W6a done — shape frozen).
**Blocks:** W6c (serializer raw-expr transcription + production LExpr→ExprData),
W6d (bridge deepened).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made._
