---
title: "W7d wire — live emit path: call emit_def_cert/emit_dt_cert from generate.rs"
status: todo
claimed_by:
created: 2026-07-15T12:00:00Z
updated: 2026-07-15T12:00:00Z
---

## Description

The last remaining piece of W7d (bootstrap-32): wire the landed defs-layer
certificate assembler into the production emit path so real crate runs write
`.defcert.lean` / `.dtcert.lean` files, then validate the fixture (`tri` def +
`Tree` datatype) bridges end-to-end against tactus-core.

The assembler is done and unit-pinned (bootstrap-32, second increment):

- `sst_serialize::emit_def_cert(crate_name, name, typ_params, params, ret, body,
  def)` — pub, flag-gated (`cert_emit_enabled()`), fail-loud + census. Drives
  `serialize_def` (both transcribers on one shared `Serializer`) → writes
  `{crate}/cert/{leaf}.defcert.lean` via `render_def_cert`. The VIR side is
  passed DECOMPOSED (exactly the `raw_vir_def` arg shape).
- `sst_serialize::emit_dt_cert(crate_name, name, typ_params, variants, dt)` — the
  datatype twin (`raw_vir_dt` arg shape) → `{leaf}.dtcert.lean`.

## What to wire

1. **Def site.** `generate.rs` calls `to_lean_fn::spec_fn_to_ast(&augmented,
   ectx)` at ~1325 (Single) and ~1363 (Mutual). At each, the VIR `FunctionX`
   (`augmented` / `f`) and the emitted `Command::Def` are both in hand. After the
   `Command::Def` is produced, call `emit_def_cert` with the FunctionX unpacked:
   - `name` = `&f.x.name`
   - `typ_params` = `&f.x.typ_params`
   - `params` = `&f.x.params`  (VALUE params — verify vs. `raw_vir_def`'s expectation)
   - `ret` = `&f.x.ret.x.typ`
   - `body` = the spec-fn body `vir::ast::Expr` (`f.x.body.as_ref()` — spec fns
     have `Some(body)`; a bodyless/uninterpreted fn has `None` → skip, don't
     cert).
   - `def` = the `Def` inside the emitted `Command::Def(def)`.
   Confirm the decomposition matches what the unit tests feed (the
   `raw_vir_def_tri_header` inputs) — especially the params list (VIR may carry a
   leading `self`/dummy the transcriber doesn't expect; `raw_vir_def` already
   fails loud on `is_mut`, but double-check the monomorphic spec-fn shape).

2. **Datatype site.** `generate.rs` ~1014-1022 emits datatypes via
   `to_lean_fn::datatype_group_to_cmds(&group, …)`. The VIR `DatatypeX` and the
   emitted `Command::Datatype(dt)` are both available around there. Call
   `emit_dt_cert(crate_name, &Dt::Path(dtx.x.name…), &dtx.x.typ_params,
   &dtx.x.variants, dt)`. (The reference gates poly/tuple/struct datatypes; only
   the multi-variant `inductive` fixture `Tree` bridges.)

3. **Flag gate.** Both entry points already early-return when
   `!cert_emit_enabled()`, so unconditional call sites are fine — the flag keeps
   the default path byte-identical. (Same discipline as `emit_cert` at ~3746 /
   ~4059.)

## Done when

- A crate run with the cert-emit flag on writes `tri.defcert.lean` +
  `lib__Tree.dtcert.lean` (or whatever the fixture crate names them).
- Those files ELABORATE + `decide`-close against `tactus-core/out/lib` (the
  probe16 runner harness, but pointed at the LIVE-emitted files rather than the
  unit-test literals) — the fully-real `tri` (real header + real Ite body from
  ONE Serializer run), closing the honest-scope gap probe16 left open.
- A perturbed def/datatype still fails the bridge (the mutation-kill smoke, now
  on the live path).

## Notes / gotchas

- **Needs a vargo release rebuild** to validate (the emit path only runs inside a
  real `verus` invocation). Fork vargo must be on PATH (see memory
  `reference_tactus_bootstrap_vargo_path`); bare vargo bails "sources changed".
  Hold the turn open for the long e2e suite (memory
  `reference_bootstrap_hold_turn_for_long_suites`).
- The transcribers (`raw_vir_def`/`raw_vir_dt`/`ldef_to_defdata`/`ldt_to_dtdata`
  + `dt_field_typ_data`/`ldt_field_typdata`) still carry `#[allow(dead_code)]`.
  Once this wire lands they are reachable via the pub `emit_*` fns; the allows
  can be dropped (cosmetic — warnings are not denied in this crate).
- The `.defcert`/`.dtcert` files are written to the SAME `{crate}/cert/` dir as
  the obligation `.cert.lean`; if a package-check step globs `cert/*.cert.lean`
  it will NOT pick these up (distinct suffix) — decide whether the def/dt certs
  should join the elaborated set or stay probe-only for now.

## Progress

_unclaimed._

## Writeup

_todo._
