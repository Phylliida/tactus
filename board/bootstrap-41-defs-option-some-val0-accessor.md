---
title: "tgt defs family: `coset_group` fails — generated Option accessor `lib.option.Option.Some_val0` not in scope"
status: todo
claimed_by:
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T14:40:00Z
---

## Description

Surfaced once **bootstrap-40** unblocked the base defs family: with
`TactusDefs_lib{,_exec}__base` now building, the full-krate tgt defs build
reaches the per-module defs and `TactusDefs_lib__coset_group` fails to elaborate:

```
TactusDefs_lib__coset_group.lean.failed:16:11: error:
  Invalid field `Some_val0`: The environment does not contain
  `lib.option.Option.Some_val0`
    seq.Seq.index (option.Option Nat) (...) ↑col   has type   option.Option Nat
```
(3 sites in coset_group; all `(... : Option Nat).Some_val0`.)

`Some_val0` is the generated variant-field accessor for a multi-variant datatype
(Option = Some | None). The emitter renders a `Some`-variant field access as
`lib.option.Option.Some_val0`, and the `[Nonempty T]` machinery
(`nonempty.rs:74-84`, Seed 3) is explicitly built around this accessor. So the
accessor is *expected to exist* — the failure is that it is **not present in the
environment** the `coset_group` module-defs file elaborates against.

## Why it matters / what it blocks

Blocks **bootstrap-39** (in-gate bridge on real tgt). The package gate needs the
FULL defs module to build; any module-defs failure ⟹ `package gate skipped:
shared-defs module unavailable` ⟹ islands fallback ⟹ the in-gate bridge
(`run_bridge_step`) never fires. This is one of two remaining blockers (the other
is **bootstrap-42**, pattern arity in `britton_via_tower`).

## Provenance / not a regression

Byte-identical `coset_group.lean.failed` between run #2 (`/tmp/w4a-tgt-ingate2`,
before the bootstrap-40 fix) and run #3 (`/tmp/w4a-tgt-ingate3`, after) — so this
is pre-existing, independent of the DeepView value-vs-Ref fix. Run #2 just never
reached it (it aborted at the base defs first).

## Scope of the fix (not yet investigated)

Likely one of: (a) the Option datatype's generated accessors (`Some_val0`,
`isSome`, …) are emitted into `__base` but the per-module defs don't `import`
them / they're in a different namespace than the reference site expects; or
(b) the std/vstd `Option` datatype isn't getting its accessor defs emitted at
all into the defs family (only the `inductive` without the projections), while
the reference to `.Some_val0` is generated unconditionally. Cross-check how the
base defs declare `lib.option.Option` and whether `Some_val0` is declared there;
grep the defs emitter for accessor synthesis (`_val`, `Some_val`, the
`is_multi_variant` accessor path) and the module-import wiring in
`crate_defs.rs`.

Repro: rebuild the bootstrap binary, then run the bootstrap-39 run #2 recipe
(`--lean-backend --crate-type=lib <tgt>/src/lib.rs --tactus-bridge
--verify-module runtime`, no `--emit-lean`, no `-V cache`); inspect
`$TACTUS_LEAN_OUT/lib/TactusDefs_lib__coset_group.lean.failed`. Elaborate it
standalone with
`LEAN_PATH="$OUT/lib:<core-out>:<prelude>" lean <that file>` to see the error
fast (that's how it was captured here).

**Done when:** `TactusDefs_lib__coset_group` builds with 0 Lean errors under the
bootstrap fork.

## Progress

- (2026-07-14, opus-bootstrap40-deepview) Filed from the bootstrap-40 /
  bootstrap-39 tgt run. Error captured by standalone-elaborating the `.failed`.

## Writeup

_pending a fix._
