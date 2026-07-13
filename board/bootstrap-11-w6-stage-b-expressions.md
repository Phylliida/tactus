---
title: "W6 — stage B: deep expressions/types join the certificate"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Deepen the mirror-type leaves from opaque ids to full expression/type syntax +
denotation, so the bridge now covers RENDERING — the class stage A explicitly
did not (trust-inventory row 3, the highest-value silent-unsoundness class).

Spec: `DESIGN-bootstrap.md` §5 (W6 row); `VERIFICATION-PATH.md` ladder rung 4.

- `Sst`/leaf mirror types gain expression + type constructors; the serializer
  promotes leaves from interned text to mirrored data (extends N3's leaf table
  into structure).
- Bridge equality now compares rendered expressions structurally — this is
  where the four leaf-renderer bugs of 2026-07-11 (and the cast/coercion class
  in `DECISION-cast-rendering.md`) would finally be CAUGHT by the certificate.
- The census (N4) ranked table is the coverage roadmap for which expression
  constructors to mirror first.

**Done when:** expression/type rendering is bridge-checked for the fixture +
a tgt slice; the cast-rendering class specifically is covered; a deliberately
mis-rendered leaf fails the bridge (mutation-kill at expression level).

**Blocked by:** bootstrap-09 (W4 pattern proven) + bootstrap-05 (N4 roadmap).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
