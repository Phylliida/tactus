---
title: "W5f v2 — widen the adequacy-spine leaf denotation to the W7 body fragment (Ite/Match/AppN/Forall/Exists) via a Defs-layer SymEnv"
status: todo
claimed_by:
created: 2026-07-15T06:45:00Z
updated: 2026-07-15T06:45:00Z
---

## Description

Follow-on from bootstrap-54 (W5f v1, probe27). The v1 leaf denotation
`edenote`/`eval` (`probe-w0/probe27_w5f_spine/w5f_sem.lean`) covers the
**arithmetic/logical obligation fragment** (atoms, int/bool literals, arith,
comparisons, logical connectives, Int↔Nat casts, unary apps, field projections,
goal-side let, span-marks) — exactly what `probe4_denote` P4 + the fixture
obligation goals use. The **W7 body constructors** (`ExprData.Ite`, `.Match`,
`.AppN`, `.Forall`, `.Exists`) are stubbed to sort-error sentinels (`0` in `eval`,
`True` in `edenote`).

Those nodes live in spec-fn **bodies** (`render_def` / the `Defs` layer, `W7`),
not in the stage-A obligation goals. Deepening `edenote` to them needs a
**Defs-layer `SymEnv`**: `E.fn` (currently a bare `Int → Int → Int` unary oracle)
must be grounded in the emitted `render_def` bodies so that `App`/`AppN` of a spec
fn denotes its actual definition, and `Match`/`Ite`/quantifiers get real meaning.

"Done" looks like: `edenote`/`eval` total on the full `ExprData` vocabulary with
faithful denotations for the W7 nodes, plus at least one `rfl`-bridge over a real
`render_exp` output that contains a body node (e.g. a `match`-bodied spec fn like
`tri`), all closing over `[propext, Quot.sound]` — no `sorryAx`, no
`Classical.choice`. Extends probe27; new probe28.

## Design notes (starting points)

- The `SymEnv.fn` field is unary in v1. Multi-arg `AppN` needs an n-ary
  application story; the cleanest is to ground `E` in the emitted `DefData`
  (`render_def` output) and denote `App`/`AppN` by look-up-then-substitute, OR by
  an uninterpreted-but-consistent function table keyed by fn id (SymEnv literal).
  The P5 prototype (`probe4_denote` / master plan §11 P5) grounds fn symbols in a
  generated per-crate match-literal — mirror that.
- `Match`/`Ite` need the value/prop sort split resolved (O9): a `match` scrutinee
  is a value (`eval`), each arm body is value-or-prop depending on the goal sort.
  v1's two-function `eval`/`edenote` split already models this; extend both.
- Quantifiers (`Forall`/`Exists`) in a body denote genuine `∀`/`∃` — the same
  binder-embedding story as the goal-level All arm (`toProp_all_embed`); reuse it.
- Interaction: this is really the **Defs-layer denotation** the master plan §4.3
  and W7 (`bootstrap-12`/`DESIGN-W7-defslayer.md`) foreshadow. Check whether v2
  should co-locate with the W7 defs-certificate machinery rather than the W5f
  spine — the fn-symbol grounding is shared.

## Progress

## Writeup
