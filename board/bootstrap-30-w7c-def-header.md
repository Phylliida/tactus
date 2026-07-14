---
title: "W7c — def-header transcription (RawDef/DefData: name + typed value params + ret)"
status: done
claimed_by: opus-w7c-defhdr
created: 2026-07-15T00:00:00Z
updated: 2026-07-15T04:30:00Z
---

## Description

Transcribe the def **header** (name + typed value params + ret type) on both
sides so a full `RawDef`/`DefData` (header + the already-landed body) can be
assembled. The W7b vocab (`DefData`/`RawDef`/`ParamList` + `render_def`/`def_eq`)
is ALREADY landed in `tactus-core`, so this is PURE serializer work — NO
`tactus-core` edit, no cache churn.

- **Reference** `raw_vir_def` (VIR surface) — name via `call_fun_id`, value
  params right-folded into `ParamList` (id via `binder_id`, type via `typ_data`),
  ret via `typ_data`, body via `raw_vir_exp`.
- **Production** `ldef_to_defdata` (`lean_ast::Def` surface) — name via
  `text_leaf(def.name)`, params from `def.binders` (id via `text_leaf(binder.name)`,
  type via `ltyp_to_typdata(binder.ty)`), ret via `ltyp_to_typdata(ret_ty)`, body
  via `lexpr_to_exprdata`.

**Why this instead of AppN (the fork the last instance flagged):** multi-arg
AppN is the ONLY remaining W7c piece that needs the cache-churning `RawList`
per-arg-`TypData` edit to `tactus-core`, and it is tgt-slice-only (the fixture's
calls are all single-arg, so W7d can bridge the fixture without it). The
def-header needs no `tactus-core` edit and directly unblocks a concrete W7d
milestone: `def_eq` on `tri` (monomorphic, single `nat` param, `Ite` body — does
not even reference the `Tree` datatype). So header-first is lower-risk and
higher-value; AppN + datatype stay deferred/batched.

**Poly gate (tgt-slice deferral, like AppN):** production's `Def.binders`
PREPENDS type-param (`{A : Type}`) + trait-bound binders before the value params
(`fn_binders_without_bound_hyps`), but `TypData` has no universe/`Type` variant
to mirror a `{A : Type}` binder. So the reference `raw_vir_def` fails loud on
non-empty `typ_params` (`rawvir-def-poly`); the fixture defs are monomorphic so
the gate never trips. Disambiguating polymorphic headers needs a
`TypData::TySort` addition — a batched `tactus-core` turn (own card).

**Done when:** both transcribers land, unit tests pin each side on a `tri`-shaped
header, `cargo test -p lean_verify` lib suite grows green, verdict-neutral
(dead code / no emit-path wire, no `tactus-core` edit).

**Blocked by:** `bootstrap-27` (W7b vocab, DONE) + `bootstrap-28`/`bootstrap-29`
body transcribers (DONE for the fixture set). **Blocks:** W7d (def emission +
`def_eq` bridge — the `tri` milestone).

## Progress
- (2026-07-15, opus-w7c-defhdr) CLAIMED. Reconnaissance complete: confirmed the
  W7b vocab (`DefData`/`RawDef`/`ParamList`/`render_def`/`def_eq`) is fully landed
  (`tactus-core/lib.rs:418-451,985`, in-crate `defs_mirror_kernel_computes` test
  pins `def_eq`), name-id agreement holds by construction
  (`call_fun_id` = `LeanName::from_path(path)` = production's `def.name =
  lean_name(path)`), and value-param TYPE agreement is the SAME
  `typ_data`↔`ltyp_to_typdata` inversion the quantifier binder types already use
  (`param_binder_typ(non-mut)` IS `typ_to_expr`).

- (2026-07-15, opus-w7c-defhdr) **LANDED — both transcriber sides + 3 tests,
  lib suite 351→354/0, verdict-neutral.** Chose the def-header over the flagged
  AppN precisely because AppN is the sole remaining W7c piece needing the
  cache-churning `RawList` per-arg-`TypData` edit AND is tgt-slice-only (fixture
  calls are single-arg), whereas the header needs no `tactus-core` edit and
  unblocks the concrete W7d `tri` `def_eq` milestone.
  - **Reference `raw_vir_def`** (`sst_serialize.rs`, after `pattern_binder_id`):
    decomposed args `(name, typ_params, params, ret, body)` — chosen over `&f:
    FunctionX` so the test doesn't build the 33-field struct; W7d passes
    `&f.name`, `&f.typ_params`, `&f.params`, `&f.ret.x.typ`, body. Poly gate
    (`!typ_params.is_empty()` → `rawvir-def-poly`) + `&mut`-param gate
    (`rawvir-def-mutparam`). Forward interning (name=0, params in decl order),
    `ParamList` formatted reversed via `box_` (the boxed self-recursive tail).
  - **Production `ldef_to_defdata`** (after `ltyp_to_typdata`): `lean_ast::Def`
    → `DefData` — `text_leaf(def.name)`, `def.binders` → `ParamList`
    (`ltyp_to_typdata(binder.ty)`), `ltyp_to_typdata(ret_ty)`,
    `lexpr_to_exprdata(body)`. Anonymous binder → `ed-def-noname`.
  - **Tests:** `raw_vir_def_tri_header` (ref, `tri`-shaped: name=0, `(n:TyNat)`,
    ret TyNat, `Var 1` body), `raw_vir_def_poly_fails` (the gate),
    `ldef_to_defdata_tri_header` (prod twin: `DefData.mk 0 … Atom 1`). Helpers
    `tnat`/`mk_fun`/`mk_params` added.
  - **Verdict-neutral:** both fns `#[allow(dead_code)]`, never on the emit path,
    no `tactus-core` edit → `golden_add_capped_cert` + whole lib suite
    byte-identical at 354/0. Activates only at the W7d def entry point.

## Writeup

**Done (fixture-complete for monomorphic defs).** The def **header** now
transcribes on both sides, so W7d can assemble a full `RawDef`/`DefData` (header
+ the already-landed body transcribers) and `decide` `def_eq` — starting with the
monomorphic `tri` (single `nat` param, `Ite` body, no `Tree` reference), a clean
first W7d milestone independent of the datatype layer.

**How it works.** `RawDef`/`DefData`/`ParamList` + `render_def`/`def_eq` were
already landed by W7b (`tactus-core/lib.rs:418-451,985-987`), so this is pure
serializer work with **no `tactus-core` edit / no cache churn**. Two new methods
in `sst_serialize.rs`:
- `raw_vir_def(name, typ_params, params, ret, body)` (reference, VIR surface) —
  `call_fun_id` for the name, `binder_id`+`typ_data` per value param folded into
  a `ParamList`, `typ_data` for ret, `raw_vir_exp` for the body → `RawDef.mk`
  text.
- `ldef_to_defdata(def)` (production, `lean_ast::Def` surface) —
  `text_leaf(def.name)`, `def.binders` → `ParamList` via `ltyp_to_typdata`,
  `ltyp_to_typdata(ret_ty)`, `lexpr_to_exprdata(body)` → `DefData.mk` text.

**Cross-side id agreement is by construction** (validated cross-side at the W7d
bridge, pinned per-side here): name — `call_fun_id` interns
`LeanName::from_path(path)` which delegates to `lean_name(path)` = production's
`def.name`; binder ids — `binder_id` = `from_var_ident` = production's binder
name; param/ret types — production's binder `ty`/`ret_ty` are `typ_to_expr(vir)`,
which `ltyp_to_typdata` inverts to the same `TypData` the reference `typ_data`
emits (the exact inversion the quantifier binder types already rely on).

**Assumptions / deferred (honest scope).**
- **Polymorphic defs fail loud** (`rawvir-def-poly`): production's `Def.binders`
  prepends `{A : Type}` + trait-bound binders that `TypData` has no universe
  variant to mirror. The reference is the gate (W7d bridges only when both sides
  succeed), so a poly def's extra production params are never observed.
  Disambiguating needs a `TypData::TySort` addition — a batched `tactus-core`
  turn (worth a follow-up card alongside the AppN `RawList` edit).
- **`&mut` value params fail loud** (`rawvir-def-mutparam`): spec fns are pure so
  none occur; deferred rather than risk the `typ_data`/`param_binder_typ`
  mut-wrap agreement.
- **`usize`/`char` param types** inherit the documented `ltyp_to_typdata`
  Nat-collapse gap (spurious-fail, never unsound). `nat`/`int`/`bool`/named-
  datatype params certify — the fixture case.
- **Verdict-neutrality** rests on the dead-code + no-`tactus-core`-edit argument
  (both fns unreferenced by `serialize()`), evidenced by the byte-identical
  golden suite. A full probe9 e2e rebuild is unnecessary for a dead-code
  addition (same reasoning as the earlier W7c arms).

**Remaining W7c:** multi-arg **AppN** (deferred — needs the cache-churning
`RawList` per-arg-`TypData` edit; tgt-slice-only) and the **datatype**
(`RawDt`/`DtData`) transcription (no `tactus-core` edit, fixture `Tree`; has a
real Box→`TyBox` field-type subtlety since datatype fields keep `Tactus.Box`
where the cast layer peels it — a genuine next increment). Then **W7d** wires the
def entry point + the e2e `def_eq` bridge (the real cross-side validation).
