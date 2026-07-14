---
title: "W6a — stage-B probe: deepen-then-diff mechanic on one cast-class expr (no shared-crate edit)"
status: todo
claimed_by:
created: 2026-07-14T00:35:00Z
updated: 2026-07-14T00:35:00Z
---

## Description

First rung of the W6 ladder (`bootstrap-11`; design in `DESIGN-W6-stageB.md`).
Validate the D2 deepen-then-diff mechanic end-to-end on ONE cast-class
expression with **zero risk to `tactus-core`** — a standalone Lean probe, in
the `probe-w0/` style.

Concretely, hand-write in a self-contained `.lean`:
- `ExprData` (hybrid leaf: `Cast`/`BinOp`/`App`/`FieldProj`/`SpanMark`-wrapper
  structural constructors + an `Atom (id : Nat)` terminal that carries its id)
  and a minimal `TypData` (`Int`/`Nat` is enough for the cast decision).
- A tiny reference `render_exp : RawExp → ExprData` that reimplements JUST the
  nat-arith operand `Clip{Nat}` decision (`needs_nat_coercion`) — see
  `DECISION-cast-rendering.md` "The fix that landed" and `DESIGN-W6-stageB.md`
  §3.1.
- Target expression: `sum_to`'s `Int.toNat r = lib.tri (Int.toNat n)` (or the
  simpler `(x as nat) * x` shape). Model the raw SST tree with type tags.
- Two `decide`s: (i) the CORRECT production-side `ExprData` equals
  `render_exp(raw)` → closes; (ii) a coercion-DROPPED production shape
  (`Atom r` where the reference has `Cast IntToNat (Atom r)`) → the `decide`
  equality is FALSE (mutation-kill at expression level).

**Done when:** the probe file `decide`s both directions (correct closes, dropped
fails) and is committed under `probe-w0/` with a short REPORT note. This freezes
the `ExprData`/`render_exp` shape that W6b then lands in `tactus-core`.

**Blocked by:** nothing (design is settled — `DESIGN-W6-stageB.md`).
**Blocks:** W6b (the shared-crate mirror-type + reference-renderer edit).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made._
