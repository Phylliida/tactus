---
title: "tgt defs family: `britton_via_tower` fails — match pattern on `DerivationStep.FreeExpand`/`RelatorInsert` has too few ctor args"
status: todo
claimed_by:
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T14:40:00Z
---

## Description

Surfaced once **bootstrap-40** unblocked the base defs family. With the base
building, the full-krate tgt defs build reaches `TactusDefs_lib__britton_via_tower`
(and `TactusDefs_lib_exec__britton_via_tower`), which fail:

```
TactusDefs_lib__britton_via_tower.lean.failed:40:86: error:
  Invalid pattern: Not enough arguments to
  `lib.presentation.DerivationStep.FreeExpand`; expected 2 explicit arguments
TactusDefs_lib__britton_via_tower.lean.failed:42:20: error:
  Invalid pattern: Not enough arguments to
  `lib.presentation.DerivationStep.RelatorInsert`; expected 3 explicit arguments
```

A `match` arm pattern on the `DerivationStep` enum binds fewer constructor
arguments than the variant declares (FreeExpand/2, RelatorInsert/3). The defs
emitter's pattern rendering (`to_lean_expr.rs::pattern_to_ast` →
`LPattern::Ctor`) is dropping/omitting sub-patterns, OR the ctor arity the
emitter believes differs from the emitted `inductive DerivationStep`'s arity
(field-count mismatch between the datatype decl and the pattern site — possibly a
ghost/phantom or erased field the pattern doesn't account for).

## Why it matters / what it blocks — PRIMARY remaining blocker for bootstrap-39

This is the accessor-INDEPENDENT failure that sinks the non-exec defs family's
attempt 1 (accessors ON) in the `crate_defs.rs` ladder, forcing the fallback to
attempt 2 (accessors OFF) — which in turn causes **bootstrap-41**'s `Some_val0`
failure in `coset_group`. So bootstrap-42 is likely the ROOT: fixing it should
let attempt 1 win (accessors present), which auto-resolves bootstrap-41. Do this
FIRST. (See bootstrap-41's ROOT CAUSE section for the ladder trace.)

Any module-defs failure ⟹ `package gate skipped: shared-defs module unavailable`
⟹ the in-gate bridge never fires (bootstrap-39 stays blocked).

**Caveat:** attempt 1's `.failed` dumps are overwritten by attempt 2 on disk, so
`britton_via_tower` may not be the ONLY attempt-1 blocker. After fixing it,
re-run and check whether the accessors-ON render surfaces further failures.

## Provenance / not a regression

Independent of the bootstrap-40 DeepView fix (that fix is the `ExprX::Match`
binder-typ peel; this is ctor-pattern *arity*, a different mechanism). Run #2
aborted at the base defs before reaching this module, so it's newly *visible*,
not newly *introduced*.

## Scope of the fix (not yet investigated)

Compare the emitted `inductive lib.presentation.DerivationStep` (in the
`presentation` defs part) against the pattern sites in `britton_via_tower` — do
the ctor arities agree? If the `inductive` has N fields but the pattern binds
< N, either the pattern renderer is under-emitting sub-patterns, or the datatype
decl over-emits fields (e.g. a decoration/phantom field). Grep
`pattern_to_ast`/`collect_pattern_binding_typs`/`PatternX::Constructor` and the
datatype-emission side (`RawDt`/`DtData`, bootstrap-31) for how positional field
types map to pattern slots. Likely lives near the same W7 datatype/match
co-design anchor (`lexpr_ctor_name`, `to_lean_expr.rs:1185`).

Repro: same as bootstrap-41 — run the bootstrap-39 run #2 recipe, then
standalone-elaborate `$OUT/lib/TactusDefs_lib__britton_via_tower.lean.failed`
with `LEAN_PATH="$OUT/lib:<core-out>:<prelude>" lean <file>`.

**Done when:** `TactusDefs_lib__britton_via_tower` (and `_exec__`) build with 0
Lean errors under the bootstrap fork.

## Progress

- (2026-07-14, opus-bootstrap40-deepview) Filed from the bootstrap-40 /
  bootstrap-39 tgt run. Error captured by standalone-elaborating the `.failed`.

## Writeup

_pending a fix._
