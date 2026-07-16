---
title: "tgt defs family: `britton_via_tower` fails — match pattern on `DerivationStep.FreeExpand`/`RelatorInsert` has too few ctor args"
status: done
claimed_by: opus-bootstrap42-arity
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T20:55:00Z
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

- (2026-07-14, opus-bootstrap42-arity) **FIXED & CONFIRMED.** The prior instance
  (opus-bootstrap40-deepview) had already *written* the fix but died (API
  overload) before verifying it — it sat uncommitted in the working tree, and it
  actually WORKS. Re-confirmed end-to-end this turn:
  - The offending patterns are `britton_via_tower.rs:1853-1864`:
    `DerivationStep::FreeExpand { position, .. }` (binds 1 of 2 fields),
    `RelatorInsert { position, .. }` / `{ relator_index, .. }` (1 of 3). Rust
    lets `{ field, .. }` elide fields; Lean requires ALL ctor fields positionally.
  - Fix = `to_lean_expr.rs::pattern_to_ast` now looks up the datatype's DECLARED
    field names via `expr_shared::ctor_field_names` (new), reorders the bound
    sub-patterns to declaration order, and fills omitted fields with `_`. The
    ctor-field table (`CTOR_FIELD_TYPS`, installed by
    `generate::install_datatype_field_bounds`) already covers ALL datatypes/all
    variants with raw field names, so `DerivationStep` is present.
  - Rebuilt the bootstrap binary (fork vargo, `vargo build --release`; cargo
    reported the lean_verify crate already fresh — the 13:28 binary had the fix
    compiled in). Verified against run #4 artifacts (`/tmp/w4a-tgt-ingate4`, a
    post-fix cold gate run the dead instance launched at 13:31): both
    `TactusDefs_lib__britton_via_tower` and `TactusDefs_lib_exec__britton_via_tower`
    (and `pred_britton_via_tower`) now emit `.olean` + `.manifest` with NO
    `.lean.failed` — i.e. they elaborate with 0 Lean errors. (ingate3, the
    pre-fix run at 13:08, had `britton_via_tower.lean.failed`; the only source
    delta between the two binaries is this pattern fix ⟹ clean causal chain.)

## Writeup

**Root cause.** Rust struct-variant match patterns may bind a subset of a
variant's fields and elide the rest with `..` (`DerivationStep::FreeExpand {
position, .. }`), or list fields out of declaration order. VIR's
`PatternX::Constructor(dt, variant, pats)` then carries only the *present* named
binders, in source order. The old `pattern_to_ast` emitted one Lean positional
arg per present binder — so a `{ position, .. }` on a 2-field variant rendered
`FreeExpand position` (1 arg), and Lean rejected it: "Not enough arguments to
`lib.presentation.DerivationStep.FreeExpand`; expected 2 explicit arguments".

**Fix (production emitter side, `to_lean_expr.rs::pattern_to_ast`).** For a
`Dt::Path` constructor pattern, look up the variant's declared field names
(`expr_shared::ctor_field_names(path, variant)`, reading the ambient
`CTOR_FIELD_TYPS` table), build a name→subpattern map from the bound binders,
then emit exactly one Lean arg per DECLARED field in declaration order —
`pattern_to_ast(subpat)` where a field is bound, `LPattern::Wildcard` where
omitted. Unknown datatypes (cross-crate opaque / not in the table) fall back to
the prior iterate-in-source-order behavior (no regression). New helper
`ctor_field_names` in `expr_shared.rs` is the field-name sibling of the existing
`ctor_field_typ` (both read the same table).

**Scope / faithfulness note.** This is a pure pattern-*rendering* fix on the
PRODUCTION (defs-family) side. It does not touch the REFERENCE transcriber
(`sst_serialize::raw_vir_exp`); the reference already fails-loud on constructs it
can't handle (`rawvir-arm-pat`), so the bridge's differential guarantee is
unaffected. Tuple patterns and 1-tuple flattening are untouched.

**Done-criterion met:** `TactusDefs_lib__britton_via_tower` and
`TactusDefs_lib_exec__britton_via_tower` build with 0 Lean errors under the
bootstrap fork.

**Consequence for the chain (IMPORTANT for the next instance).** Fixing this did
NOT make the full defs family build, and did NOT auto-resolve bootstrap-41 — as
the card's own caveat warned ("britton may not be the ONLY attempt-1 blocker;
attempt-1 dumps are overwritten by attempt-2 on disk"). With britton building,
run #4's full-krate defs build now surfaces TWO more failures that britton was
masking:
  1. **`word_numbering`** — a NEW, distinct blocker: `failed to prove
     termination` in the emitted `decreasing_by` for `numbers_word`/`w_c`
     (recursive spec fns). `omega` can't extract `alpha>0 ∧ m>1` from a
     termination hypothesis wrapped in a `dite`/`ite` over `Prop`
     (`¬if x : alpha = 0 then True else m ≤ 1`). Accessor-INDEPENDENT (fails in
     both ladder attempts and in the exec family). Filed as
     **bootstrap-44**. This is now the PRIMARY defs-family blocker.
  2. **`coset_group`** (bootstrap-41) — still 3× `Some_val0`, STILL a fallback
     artifact: word_numbering now sinks the non-exec ladder's attempt-1, so it
     falls back to attempt-2 (accessors OFF) exactly as britton used to cause.
     Blocked behind bootstrap-44 now.
