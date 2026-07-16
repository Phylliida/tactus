---
title: "W7c — datatype transcription (RawDt/DtData: name + ctors + positional field types, the Box→TyBox subtlety)"
status: done
claimed_by: opus-w7c-dt
created: 2026-07-15T05:00:00Z
updated: 2026-07-15T05:40:00Z
---

## Description

Transcribe the `inductive` datatype decl on both sides so a full `RawDt`/`DtData`
(name + ctors, each ctor = name + positional field TYPES) can be assembled and
`decide`d against `dt_eq`. The W7b vocab (`RawDt`/`DtData`/`CtorList`/`TypList`
+ `render_dt`/`dt_eq`) is ALREADY landed in `tactus-core`, so this is PURE
serializer work — NO `tactus-core` edit, no cache churn. This is the last
fixture-covering piece before W7d bridges the `Tree` datatype.

- **Reference** `raw_vir_dt(name: &Dt, typ_params, variants)` (VIR
  `DatatypeX` surface) — name via `lean_name(path)`, per-variant ctor name via
  `sanitize(&v.name)`, positional field types via a new `dt_field_typ_data`.
- **Production** `ldt_to_dtdata(&lean_ast::Datatype)` — name/ctor verbatim
  (`text_leaf`), field types via a new `ldt_field_typdata`.

**THE BOX SUBTLETY (W7a §7 Q4 — the one real technical hurdle):** a datatype
FIELD keeps its `Box` (`Node(Box<Tree>, Box<Tree>)`, the recursion goes through
the box), so the value-position `typ_data`'s SMT-wrapper peel (which drops `Box`)
is WRONG here. Production agrees — it renders the field via `typ_to_expr`, which
maps `Box<T>` to `Tactus.Box T` (kept). So the field-type transcriber maps
`Decorate(Box) → TyBox(pointee id)` (distinct from `TyRef` — Box≠Ref; W7a §7 Q4
verdict), and the production recognizer inverts `Tactus.Box T` back to the same
`TyBox` id.

**Done when:** both transcribers land, unit tests pin each side on the `Tree`
shape (incl. the Box→TyBox pin), `cargo test -p lean_verify` lib suite grows
green, verdict-neutral (dead code / no emit-path wire, no `tactus-core` edit).

**Blocked by:** `bootstrap-27` (W7b vocab, DONE). **Blocks:** W7d (datatype
emission + `dt_eq` bridge — the `Tree` milestone).

## Progress

- (2026-07-15, opus-w7c-dt) CLAIMED. Reconnaissance: confirmed the W7b vocab is
  landed (`tactus-core/lib.rs:432-464` CtorList/TypList/DtData/RawDt, `991`
  `render_dt`, `1268` `dt_eq`), and read the ground-truth emitted `Tree`
  (`bootstrap-fixture/out/lib/TactusDefs_lib_exec__base.lean:22`:
  `inductive lib.Tree | Leaf (val0 : Int) | Node (val0 : Tactus.Box lib.Tree)
  (val1 : Tactus.Box lib.Tree)`). Traced the two production builders
  (`to_lean_fn.rs:1008` datatype `Variant { name: sanitize(&v.name), fields:
  typ_to_expr(&f.a.0) }`; `to_lean_type.rs:174` `Box → applied("Tactus.Box",
  [typ_to_expr(inner)])`) so cross-side id agreement is by construction.

- (2026-07-15, opus-w7c-dt) **LANDED — both transcriber sides + the two
  field-type helpers + 5 tests, lib suite 354→359/0, verdict-neutral.**
  - **Reference `raw_vir_dt`** (`sst_serialize.rs`, after `raw_vir_def`):
    decomposed args `(name: &Dt, typ_params, variants)` (avoids building the
    ~13-field `DatatypeX` in the test; W7d passes `&dt.x.name`,
    `&dt.x.typ_params`, `&dt.x.variants`). Poly gate `rawvir-dt-poly` (like
    `raw_vir_def` — `(A : Type)` params have no `TypData` mirror), tuple gate
    `rawvir-dt-tuple`, single-variant-struct gate `rawvir-dt-struct` (mirrors
    production's `is_single_variant_struct = len==1 && name==short_name` →
    `structure`, a different transcription). Forward interning (name=0, ctors in
    decl order); `CtorList`/`TypList` folded reversed (boxed tails).
  - **`dt_field_typ_data`** (reference field-type helper): `Decorate(Box) →
    TyBox(typ_leaf(inner))`; everything else delegates to the shared `typ_data`
    (Int/Bool/Nat/named/`&T`). The Box case is the W7a §7 Q4 mechanic — keeps the
    box where `typ_data` would peel it.
  - **Production `ldt_to_dtdata`** (after `ldef_to_defdata`): `lean_ast::Datatype`
    → `DtData`. Only multi-variant `Inductive`/`IndexedInductive` (they share the
    ctor-list shape); single-variant `Structure` fails loud `ed-dt-struct`
    (reference gates it symmetrically). Name/ctor via `text_leaf`, fields via
    `ldt_field_typdata`.
  - **`ldt_field_typdata`** (production field-type recognizer): `App(Var
    "Tactus.Box", [inner]) → TyBox(intern(pp(inner)))`, else delegate to
    `ldt_to_typdata`. Agrees with the reference `dt_field_typ_data`'s
    `typ_leaf(inner)` because production's field `Expr` IS `typ_to_expr(vir)`
    (the same `ltyp_to_typdata`↔`typ_data` inversion the quantifier/def-header
    binder types already use).
  - **Cross-side id agreement by construction:** datatype name —
    `lean_name(path)` = production's `Datatype.name`; ctor name — `sanitize(&v.name)`
    = production's `Variant.name` (built as `sanitize(&v.name)`); field types —
    positional, same `.iter()` order, `TyBox`/`TyNamed`/`TyInt` ids off the shared
    `self.leaves` table. NICE COINCIDENCE the tests pin: because the datatype name
    interns `lib.Tree` FIRST, the `Box<Tree>` field's `TyBox` pointee reuses that
    id (0) on BOTH sides — the two independent unit tests both emit `TyBox 0`.
  - **Tests (5 new, lib suite 354→359/0):** `raw_vir_dt_tree` (ref, full `Tree`
    shape — name=0, Leaf=1 [TyInt], Node=2 [TyBox 0, TyBox 0], reversed folds,
    the Box→TyBox pin), `raw_vir_dt_poly_fails`, `raw_vir_dt_struct_fails`,
    `ldt_to_dtdata_tree` (prod twin — byte-identical structure to the ref test,
    incl. `Tactus.Box lib.Tree`→`TyBox 0` recognition), `ldt_to_dtdata_structure_fails`.
    Helpers `mk_dt_path`/`tdatatype`/`tbox`/`tu64`/`mk_variant` added.
  - **Verdict-neutral:** all four new fns `#[allow(dead_code)]`, never on the emit
    path; no `tactus-core` edit → `golden_add_capped_cert` + whole lib suite
    byte-identical at 359/0. Activates only at the W7d datatype entry point.

## Writeup

**Done (fixture-complete for the `Tree` datatype).** The `inductive` decl now
transcribes on both sides, so W7d can assemble a full `RawDt`/`DtData` and
`decide` `dt_eq` on the fixture `Tree`. Together with the already-landed def
header + Ite/Match body transcribers, the fixture-covering DEFINITIONS surface
(spec-fn defs + datatypes) is now complete on both sides for the monomorphic
fixture.

**How it works.** Pure serializer work — `RawDt`/`DtData`/`CtorList`/`TypList` +
`render_dt`/`dt_eq` were landed by W7b (`tactus-core/lib.rs:432-464,991,1268`), so
**no `tactus-core` edit / no cache churn**. Four new methods in `sst_serialize.rs`:
- `raw_vir_dt(name, typ_params, variants)` (reference, VIR `DatatypeX`) —
  `lean_name(path)` name, `sanitize(&v.name)` per-ctor, `dt_field_typ_data` per
  positional field → `RawDt.mk` text.
- `dt_field_typ_data(typ)` — the Box-keeping field-type map (`Box<T>`→`TyBox`,
  else `typ_data`).
- `ldt_to_dtdata(datatype)` (production, `lean_ast::Datatype`) — verbatim
  name/ctor + `ldt_field_typdata` per field → `DtData.mk` text.
- `ldt_field_typdata(ty)` — recognizes `Tactus.Box T`→`TyBox`, else `ltyp_to_typdata`.

**The Box subtlety, resolved (W7a §7 Q4).** A datatype field keeps its `Box`; the
recursion in `Node(Box<Tree>, Box<Tree>)` goes through it, so peeling (as the
value-position `typ_data` does for SMT wrappers) would erase the field kind. Both
sides map `Box<T>`→`TyBox(pointee)` (NOT `TyRef` — Box≠Ref), and production's
`typ_to_expr`-rendered `Tactus.Box T` recognizes back to the same `TyBox` id. The
`raw_vir_dt_tree`/`ldt_to_dtdata_tree` tests pin exactly this (`TyBox 0` for both
`Node` fields, distinct from what a peel would give).

**Assumptions / deferred (honest scope).**
- **Polymorphic datatypes fail loud** (`rawvir-dt-poly`): production prepends
  `(A : Type)` params `TypData` can't mirror (same `TypData::TySort` gap as
  `raw_vir_def`); the fixture `Tree` is monomorphic. The reference is the gate.
- **Single-variant structs fail loud** (`rawvir-dt-struct`/`ed-dt-struct`):
  production emits a `structure` (ctor = type name, no variant list), a genuinely
  different transcription. `Point` is gated; `Tree` (multi-variant `inductive`)
  certifies. A follow-up card could add the struct transcription if a tgt slice
  needs it.
- **`Rc<T>`/`Arc<T>` fields** would delegate to `typ_data`, which PEELS them while
  production keeps `Tactus.Rc T` — a peel-vs-keep mismatch that SPURIOUSLY fails
  the bridge (uncertifiable, never wrongly passes). None in the fixture. Same
  documented-gap class as the `usize`/`char`→Nat gap.
- **Verdict-neutrality** rests on the dead-code + no-`tactus-core`-edit argument
  (all four fns unreferenced by `serialize()`), evidenced by the byte-identical
  golden suite. A full probe9 e2e rebuild is unnecessary for a dead-code addition
  (same reasoning as every prior W7c arm).

**Remaining W7c:** multi-arg **AppN** (deferred — the ONLY remaining W7c piece
needing the cache-churning `RawList` per-arg-`TypData` edit; tgt-slice-only —
fixture calls are single-arg). Then **W7d** wires the def + datatype entry points
+ the e2e `def_eq`/`dt_eq` bridges (the real cross-side validation — where
`lean_name`/`sanitize`/`typ_to_expr` fidelity against REAL compiler output gets
exercised, beyond these hand-built structural unit pins).
