---
title: "W7 — defs-layer certificate (spec-fn bodies + datatype/height emission)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Extend the certificate pattern to the DEFINITIONS layer: serialize VIR spec-fn
bodies + datatype/height emission, recompute a reference definitional
translation, bridge. A wrong-but-consistent def translation is a model-drift
bug users cannot see — this closes the remaining half of trust-inventory row 4.

Spec: `DESIGN-bootstrap.md` §5 (W7 row) + §7 (beyond R2).

- Serialize spec-fn body VIR (the same discipline as the SST serializer, new
  input surface).
- Reference definitional translation authored in tactus-core; bridge the
  emitted spec-fn defs against it.
- Datatype + height-function emission similarly certified.

**Done when:** spec-world definitions are bridge-checked against the reference
translation for the fixture + a tgt slice; a perturbed def fails the bridge.

**Blocked by:** bootstrap-11 (W6 — reuse the stage-B expression machinery for
def bodies).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
