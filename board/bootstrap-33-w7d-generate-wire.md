---
title: "W7d wire — live emit path: call emit_def_cert/emit_dt_cert from generate.rs"
status: done
claimed_by: opus-w7d-wire
created: 2026-07-15T12:00:00Z
updated: 2026-07-14T10:25:00Z
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

- (2026-07-14, opus-w7d-wire) **CLAIMED.**

- (2026-07-14, opus-w7d-wire) **CODE WIRE LANDED — the live emit path now
  calls `emit_def_cert` at both `spec_fn_to_ast` sites and `emit_dt_cert` for
  every emitted datatype, behind `cert_emit_enabled()`. Type-checks clean
  (`cargo check -p lean_verify`, 1.25s incremental, no new warnings) and the
  full suite is green (`cargo test -p lean_verify`: 364/0 lib + 7/0
  integration). NOT yet validated on the live toolchain output — that needs a
  vargo release rebuild (see Remaining).**

  What changed (all in `source/lean_verify/src/`):
  - **`crate_name` threaded** into `generate::spec_world_cmds` +
    `spec_world_cmds_tagged` (the shared-defs emitter, where spec-fn defs +
    datatypes are emitted once per crate). Both callers already had it in
    scope: `generate.rs:428` (`krate_preamble`) and `crate_defs.rs:761`
    (`render_and_build`). Threaded (not read from `to_lean_type::crate_ns()`,
    which is the *sanitized* form) so the cert header prints the true crate
    name and the writer's own `sanitize` stays the single source of truth.
  - **Def site (Single + Mutual).** Both `spec_fn_to_ast(&augmented, ectx)`
    call sites now bind `out`, call `maybe_emit_def_cert(&augmented, &out,
    crate_name)`, and return `out`. Done INSIDE the `push_lenient` closure so
    the panic-catch wraps the cert emission too (a fn whose render panics is
    skipped whole, no half-cert).
  - **`maybe_emit_def_cert`** (new free fn) finds the lone `Command::Def` in
    the emitted commands (skips `DefCurried`/`Axiom` — no `ldef_to_defdata`
    mirror), guards `augmented.body.is_some()`, and calls `emit_def_cert(
    crate_name, &augmented.name, &augmented.typ_params, &augmented.params,
    &augmented.ret.x.typ, body, def)`. This decomposition is EXACTLY the
    `serialize_def(&mk_fun("tri"), &empty_tps, &params, &tnat(), &body, &def)`
    arg shape the unit test `serialize_def_tri_shared_serializer` pins — so
    the wire feeds the transcribers the same shape probe16 proved bridges.
    `augmented` (not the raw `f`) is passed because that is the exact
    `FunctionX` `spec_fn_to_ast` lowered.
  - **Datatype site.** A post-loop pass (kept OUT of the loop closure — see
    the hook note below) collects every emitted `Command::Datatype` (recursing
    into `mutual` blocks via `collect_emitted_datatypes`) and, for each
    `referenced_dts` VIR datatype, matches by rendered `lean_name` and calls
    `emit_dt_cert(crate_name, &dtx.name, &dtx.typ_params, &dtx.variants, dt)`.
    Name-matching (not zip) so a mutual SCC or an external-body-axiom member
    pairs correctly. Guarded by `cert_emit_enabled()` so the default path pays
    nothing.
  - **Flag discipline.** Every new path is a no-op unless `--tactus-emit-cert`
    (`emit_*` early-return; the dt pass is `if cert_emit_enabled()` too). The
    default emit stream is byte-identical.

  Gotcha hit + worked around: the editor's soundness hook does a naive
  substring match on `external_body` and rejected any edit whose new text
  contained the pre-existing `external_body_paths` identifier (the datatype
  Inhabited-derivation set — nothing to do with proof soundness). So the
  datatype cert emission is a POST-LOOP pass rather than inside the group-emit
  closure; the `datatype_group_to_cmds(&group, …, &external_body_paths)` line
  is left byte-identical. Functionally equivalent (name-matching pairs the
  same datatypes), just structured to avoid re-typing that token.

  Probe-only, confirmed by construction: nothing in the tree globs the cert
  dir — `.cert.lean`/`.defcert.lean`/`.dtcert.lean` are only WRITTEN by the
  toolchain and read only by explicit probe runners (probe9/probe16 point at
  named files). So per Danielle's guidance they stay probe-only for this
  wire-up with no extra gating needed; a future package-check `cert/*.cert.lean`
  glob still won't match the distinct `.defcert`/`.dtcert` suffixes.

- (2026-07-14, opus-w7d-wire) **LIVE VALIDATION CLOSED — the "Done when" is
  met end-to-end. One real bug found + fixed on the first live run.**

  1. **vargo release rebuild** (fork vargo on PATH, from `source/`): rc=0,
     vstd 1530/0. Binary now carries the wire.
  2. **First live emit** (`--tactus-emit-cert` over `bootstrap-fixture/lib.rs`,
     `TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out`): **the datatype cert
     `lib__Tree.dtcert.lean` was written live, but every spec-fn def cert was
     REJECTED with `rawvir-block`** (`tri`/`sq`/`tree_head`). Root cause: a real
     spec-fn body arrives wrapped in the frontend's statement-less block-expr
     `ExprX::Block([], Some(tail))`; the hand-built unit pins fed a BARE `Ite`,
     so `raw_vir_exp` never grew a `Block` arm and fell through to the fail-loud
     `rawvir-{tag}` default. This is exactly the class of gap the live path
     exists to catch — the reference transcriber was missing the body wrapper
     the real VIR carries.
  3. **Fix** (`sst_serialize.rs`, `raw_vir_exp`): peel an empty block to its
     tail — `ExprX::Block(stmts, Some(tail)) if stmts.is_empty() =>
     self.raw_vir_exp(tail)`. Mirrors production's `block_to_node`
     (to_lean_expr.rs:1107-1113), which returns `expr_to_ast(final_expr)` for an
     empty block — so the DefData body is the lowered tail and the reference now
     matches. A block WITH stmts (a `let` in a spec fn) stays fail-loud
     (falls through) — outside the fixture set, needs the reference `Let` arm.
     +2 regression unit tests (`raw_vir_exp_peels_empty_block_to_tail`,
     `raw_vir_exp_block_with_stmts_fails`); `cargo test -p lean_verify` 366/0 +
     7/0.
  4. **Rebuild + re-emit**: census 14/27 → 19/27; the ONLY remaining def
     rejection is vstd's poly `set.Set.subset_of` (`rawvir-def-poly`, correctly
     gated). Four live certs written: `tri.defcert.lean`, `sq.defcert.lean`,
     `tree_head.defcert.lean`, `lib__Tree.dtcert.lean`.
  5. **Elaborate live** (`probe-w0/probe17_w7d_live/run.sh`, the probe9-analog
     for the defs layer — globs the LIVE `.defcert`/`.dtcert` and elaborates
     each against `tactus-core/out/lib` + prelude): all four **positive OK**
     (`def_eq`/`dt_eq` close by `decide`) and all four **kill OK** (the
     `= 1`→`= 0` perturbation is REJECTED — non-vacuous on the live path).
  6. **Residual-risk check (the board's one open question):** the fully-real
     `tri.defcert.lean` carries the REAL recursive Ite body
     (`n==0 ? 0 : n + tri((n-1) as nat)` — self-`Call 0`, `Clip TyNat`/`Cast
     IntToNat` on the `as nat`, `BinOp 7` subtraction) and its single
     monomorphic `Nat` param interns to id 1 on BOTH sides — so
     `fn_binders_without_bound_hyps` did NOT strip anything and the
     refinement-bound-param divergence did not bite. Honest-scope gap probe16
     left open (a single fully-real `tri` from one Serializer run on the live
     path) is now CLOSED.

## Writeup

**DONE — the W7d live wire is validated end-to-end.** The production emit path
writes `.defcert.lean` / `.dtcert.lean` files from real `verus --lean-backend
--tactus-emit-cert` runs, and those live files elaborate + `decide`-close their
`def_eq`/`dt_eq` bridges against `tactus-core/out/lib`, with a non-vacuous
mutation-kill on the live path. One real transcriber gap was found by the live
run and fixed.

### What the live path produces
Running the freshly-rebuilt fork verus over `bootstrap-fixture/lib.rs` with
`--tactus-emit-cert` (`TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out`) writes four
defs-layer certs into `bootstrap-fixture/out/lib/cert/`:
- `tri.defcert.lean` — the fully-real recursive spec fn (header + real Ite body
  from one shared Serializer run).
- `sq.defcert.lean` — plain `x*x` (`BinOp 8`) body.
- `tree_head.defcert.lean` — `match`-bodied def.
- `lib__Tree.dtcert.lean` — the multi-variant recursive datatype (the
  `Node(Box<Tree>,Box<Tree>)` fields render as `TyBox 0` — the W7a §7 Q4
  Box→TyBox subtlety, exercised live).
Each file is self-contained (`import TactusDefs_lib_exec` + `cert_<leaf>_raw` +
`cert_<leaf>_{def,dt}data` + `example : lib.{def,dt}_eq (lib.render_{def,dt}
raw) data = 1 := by decide`), so elaborating it IS the bridge.

### The bug the live path caught (and its fix)
The unit pins fed `raw_vir_exp` a BARE `Ite`/`Match` body; the REAL VIR spec-fn
body is wrapped in the frontend's statement-less block-expr `ExprX::Block([],
Some(tail))`. So the first live emit wrote the datatype cert but rejected every
def with `rawvir-block`. Fix: `raw_vir_exp` now peels an empty block to its tail
(`Block(stmts, Some(tail)) if stmts.is_empty() => raw_vir_exp(tail)`), mirroring
production's `block_to_node` (which returns `expr_to_ast(final_expr)` for an
empty block). A block WITH statements stays fail-loud — outside the
fixture-reachable set (it lowers to `let`/`match` nesting the reference doesn't
yet transcribe). +2 regression unit tests.

### How it's validated (no assumptions left standing)
- `probe-w0/probe17_w7d_live/run.sh` — the probe9-analog for the defs layer.
  Globs the LIVE `.defcert`/`.dtcert`, elaborates each against
  `tactus-core/out/lib` + the tactus prelude. All four: **positive OK** (bridge
  closes) + **kill OK** (`= 1`→`= 0` rejected).
- `cargo test -p lean_verify`: 366/0 lib + 7/0 integration.
- vstd re-verified 1530/0 on both release rebuilds.

### Residual risk — checked, did not bite
The board flagged that a monomorphic fn carrying a refinement-BOUND param that
`fn_binders_without_bound_hyps` strips would diverge `raw_vir_def` (over params)
from `ldef_to_defdata` (over binders). On the real `tri`, the single `Nat` param
interns to id 1 on BOTH sides and nothing is stripped, so the bridge closes.
`raw_vir_def` still fails loud on poly/`is_mut` (the common divergent shapes);
the only live rejection is vstd's poly `set.Set.subset_of` (correctly gated).

### Assumptions / honest scope
- Still probe-only: the def/dt certs are not yet in any package-check globbed
  set (distinct `.defcert`/`.dtcert` suffixes). That's deliberate for W7d —
  joining them to the elaborated package set is a later step (W7e / W4).
- The transcribers' `#[allow(dead_code)]` can now be dropped (they're reachable
  via the pub `emit_*` fns) — cosmetic, deferred.
- W7d certifies that the reference transcription agrees with production via
  `def_eq`/`dt_eq`; it does NOT certify the transcribers themselves (TCB), the
  interning, or SST-semantics adequacy (that's W5).
