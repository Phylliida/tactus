---
title: "W7d — wire def/datatype emission + bridge decide def_eq/dt_eq on the fixture"
status: in_progress
claimed_by: opus-w7d
created: 2026-07-15T07:00:00Z
updated: 2026-07-15T12:00:00Z
---

## Description

Wire the two W7c transcriber pairs into def/datatype emission and produce the
real cross-side bridge:

- production emits a `DefData`/`DtData` mirror alongside each `@[reducible] def`
  / `inductive` (via `ldef_to_defdata` / `ldt_to_dtdata`),
- reference emits `RawDef`/`RawDt` transcribed straight from VIR (via
  `raw_vir_def` / `raw_vir_dt`) → `render_def`/`render_dt`,
- bridge `decide`s `def_eq(render_def raw, defdata) = 1` per def and
  `dt_eq(render_dt raw, dtdata) = 1` per datatype.

Spec: `DESIGN-W7-defslayer.md` §6 (W7d row). This is the real cross-side
validation of everything W7a…c built — where `lean_name`/`sanitize`/
`typ_to_expr` fidelity against REAL compiler output gets exercised, beyond the
hand-built structural unit pins.

**Done when:** the fixture defs (`tri`) + datatype (`Tree`) bridge-check
against the reference translation; a perturbed def/datatype fails the bridge.

**Blocked by:** `bootstrap-28`…`31` (W7c transcribers, all landed).
**Blocks:** W7e (mutation-kill hardening — but a mutation-kill smoke lands here
to prove non-vacuity).

## Progress

- (2026-07-15, opus-w7d) **CLAIMED.** Reconnaissance of the full bridge path
  (grounded in code, not the design doc):
  - **Bridge mechanism (from probe9/run.sh):** `emit_cert` writes per-fn
    `<fn>.cert.lean` literals; the probe appends
    `example : lib.goals_eq (lib.ref_wp …) … = 1 := by decide` and elaborates it
    against `tactus-core/out/lib`. The W7d analog is a `.cert.lean` carrying
    `cert_<def>_raw : lib.RawDef` + `cert_<def>_defdata : lib.DefData` and the
    line `example : lib.def_eq (lib.render_def cert_<def>_raw) cert_<def>_defdata
    = 1 := by decide` (mutatis mutandis for `dt_eq`).
  - **The four transcribers are landed + unit-pinned** (`sst_serialize.rs`:
    `raw_vir_def` 1158 / `raw_vir_dt` 1264 / `ldef_to_defdata` 1694 /
    `ldt_to_dtdata` 1759). Their EXACT output strings are pinned in
    `sst_serialize_tests.rs` (`raw_vir_def_tri_header` 938, `ldef_to_defdata_tri_header`
    976, `raw_vir_dt_tree` 1074, `ldt_to_dtdata_tree` 1137).
  - **tactus-core bridge fns** (`tactus-core/lib.rs`): `render_def` 985
    (`DefData { name, params, ret, body: render_exp(d.body) }`), `def_eq` 1261
    (name ∧ `param_list_eq` ∧ `typ_eq` ret ∧ `expr_eq` body), `render_dt` 991
    (identity on name+ctors), `dt_eq` 1268 (name ∧ `ctor_list_eq`). All emitted
    to `TactusDefs_lib_exec__root` (reachable via `import TactusDefs_lib_exec`).

- (2026-07-15, opus-w7d) **FIRST INCREMENT LANDED — e2e `def_eq`/`dt_eq` bridge
  probe on the REAL transcriber output (`probe-w0/probe16_w7d_defbridge/`), the
  def-layer analog of probe9. rc=0, ~1.25s.** See that probe's REPORT for the
  full verdict matrix (6 positives close by decide+rfl; 5 mutation negatives
  reject; meta-check confirms non-vacuity). This proves W7d's core claim WITHOUT
  a vargo rebuild: the actual serializer text format (the exact strings the unit
  tests `assert_eq!` — real `raw_vir_def`/`ldef_to_defdata`/`raw_vir_dt`/
  `ldt_to_dtdata`/`raw_exp`-Ite/`lexpr`-Ite output) elaborates and closes
  `def_eq`/`dt_eq` against the LANDED tactus-core `render_def`/`render_dt`, and
  perturbations flip it to 0.
  - **Coverage:** `tri` header+trivial-body (`def_eq`), an **Ite-bodied def**
    (`def_eq`, exercising `render_exp`'s branch path end-to-end — all-`TyInt`
    branches ⇒ no `Int.toNat` inserted), and the **full `Tree` datatype**
    (`dt_eq`, real emitted shape incl. the Box→`TyBox` W7a §7 Q4 subtlety).
  - **Kills (non-vacuity):** body-atom, ret-type, Ite branch-swap, ctor-id, and
    **the Box-peel kill** (`Node` field `TyNamed 0` vs kept `TyBox 0` — exactly
    the mistranslation the Box subtlety guards against).
  - **Honest scope:** the `tri` def is the header+trivial-body pin and `raw_g`
    has a synthetic header; a single fully-real `tri` (real header + real Ite
    body from ONE Serializer run) + the live emit path arrive with the
    generate.rs wire (needs the release rebuild). Transcribers are still
    `#[allow(dead_code)]`; this probe consumes their pinned output.

- (2026-07-15, opus-w7d-2) **SECOND INCREMENT LANDED — the `render_def_cert` /
  `render_dt_cert` assembler + `emit_def_cert` / `emit_dt_cert` public entry
  points, in `sst_serialize.rs` (the `render_cert`/`emit_cert` analog for the
  defs layer). Pure Rust, 5 new unit tests, full `lean_verify` suite 364/0 — NO
  vargo rebuild needed.**
  - **`serialize_def` / `serialize_dt`** (`sst_serialize.rs`) drive BOTH
    transcribers on ONE shared `Serializer`, so the reference's forward-interned
    leaf ids are reused by the production side (reference walk runs FIRST + gates
    — a poly/mut-param def fails loud via `?` before production runs, so no
    half-cert). Returns the `(raw, defdata)` / `(raw, dtdata)` text pair.
  - **`render_def_cert` / `render_dt_cert`** assemble the `.defcert.lean` /
    `.dtcert.lean` file text: `import TactusDefs_lib_exec` + `maxRecDepth 8000` +
    vocab-hash/honest-scope header + the two literals + the bridge
    `example : lib.def_eq (lib.render_def cert_…_raw) cert_…_defdata = 1 := by
    decide` (mutatis mutandis `dt_eq`). Distinct `.defcert`/`.dtcert` suffixes so
    they never collide with the obligation cert's `.cert.lean`.
  - **`emit_def_cert` / `emit_dt_cert`** (pub, flag-gated, fail-loud + census)
    are the generate.rs entry points, taking the VIR side DECOMPOSED (the
    `raw_vir_def`/`raw_vir_dt` arg shape) so the wire unpacks the
    `FunctionX`/`DatatypeX` at the call site and the assembler stays
    unit-testable with the lightweight VIR builders.
  - **Tests** (`sst_serialize_tests.rs`): `serialize_def_tri_shared_serializer`
    + `serialize_dt_tree_shared_serializer` assert the shared serializer
    reproduces the EXACT probe16-proven `(raw, defdata)`/`(raw, dtdata)` pairs
    (byte-identical to the `raw_vir_*`/`l*_to_*data` unit pins);
    `serialize_def_poly_gates_on_reference` pins the reference-first short
    circuit; `render_def_cert_bridge_shape` + `render_dt_cert_bridge_shape` pin
    that the assembler embeds the literals verbatim and emits the exact
    `decide` bridge line probe16 proved closes. So: (serialize ⇒ probe16
    literals) ∧ (render ⇒ probe16 bridge line) composes to a validated cert
    WITHOUT a Lean rebuild.
  - **Remaining (the live wire) split out to `bootstrap-33-w7d-generate-wire`.**

## Writeup

_partial — see Progress + the probe REPORT. Two of three pieces landed:_
- _✅ the bridge probe (probe16, first increment) — `def_eq`/`dt_eq` close on
  real transcriber output, kills non-vacuous._
- _✅ the `render_def_cert`/`render_dt_cert` + `emit_def_cert`/`emit_dt_cert`
  assembler (second increment) — pure Rust, 5 unit tests, suite 364/0._
- _⬜ the generate.rs production wire (call `emit_def_cert` at the
  `spec_fn_to_ast` sites + `emit_dt_cert` at datatype emission, behind the
  cert-emit flag, decomposing the `FunctionX`/`DatatypeX`) — needs the vargo
  release rebuild to validate the full-Ite-body `tri` def end-to-end. Tracked in
  **`bootstrap-33-w7d-generate-wire`**._
