---
title: "W4 — kernel bridge on by default in package mode"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Promote the stage-A certificate from opt-in to a standing part of the package
gate. After this, statement-STRUCTURE rendering leaves the TCB (trust-inventory
rows 2 and structurally 4).

Spec: `DESIGN-bootstrap.md` §5 (W4 row) + §2 table; `DESIGN-W2-refwp.md` §4.

- `--tactus-emit-cert` + bridge default-on under the package gate; the gate note
  gains one line: "N obligations bridge-checked against tactus-core".
- Bridge failure = verification error at the fn.
- Cache story: cert files + bridge oleans content-keyed like islands (a fn
  whose SST + goals are unchanged skips re-bridging). Needs W3's cost numbers
  to justify the default.

**Done when:** a normal `--lean-backend` package run bridge-checks every
serializable fn by default; cost is acceptable per W3's numbers; cache keeps
warm runs cheap; suite green.

**Blocked by:** bootstrap-08 (W3 — need divergences at zero and cost numbers
before defaulting on). R1 package layers already landed (M6).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
