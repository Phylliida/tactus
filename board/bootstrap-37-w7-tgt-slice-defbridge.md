---
title: "W7 — tgt-slice def_eq/dt_eq bridge (formally close W7's last rung)"
status: done
claimed_by: opus-w7-tgtslice
created: 2026-07-14T11:40:00Z
updated: 2026-07-14T12:05:00Z
---

## Description

The single remaining rung of the W7 umbrella (`bootstrap-12`): bridge a REAL
tgt-slice def, not just the `bootstrap-fixture` family. Everything the fixture
forces (Ite/Match/BinOp/Field/single+multi-arg Call, the `Tree` datatype) is
green; the defs-layer transcription + live bridge + content-kill are done. This
card runs the def/dt cert emit path over a slice of `tactus-group-theory` and
confirms every EMITTED `.defcert`/`.dtcert` closes its `def_eq`/`dt_eq` bridge
against `tactus-core/out/lib` — or produces an HONEST census rejection (a
scope-gate the reference transcriber fails loud on, not a silent divergence).

This is the W3-on-tgt payoff for the DEFS layer: the differential gate's
bug-finding value comes from running it over corpus code the fixture never
exercised. A closing bridge over real tgt spec fns/datatypes is what lets us
declare `bootstrap-12` done; an unexplained divergence is a real transcriber bug
to triage (like W3's RetBind-value deref gap, bootstrap-08).

**Slice chosen:** `symbol` (`src/symbol.rs`, 80 lines) — the foundational tgt
module. One datatype (`Symbol` enum) + 4 `open spec fn`s (`inverse_symbol`
[Match], `is_inverse_pair` [Call+BinOp], `generator_index` [Match+Field],
`symbol_valid` [Call+BinOp]) exercising the core W7 vocab on real corpus.

**Done when:**
- a real `verus --lean-backend --tactus-emit-cert` run over the tgt slice writes
  `.defcert`/`.dtcert` files for the slice's spec fns + datatype;
- every emitted cert closes its `def_eq`/`dt_eq` bridge by `decide` (the probe17
  runner pointed at the tgt cert dir), OR is a triaged honest census rejection;
- a per-file mutation-kill stays non-vacuous;
- census table recorded (certified / rejected-with-bucket), like bootstrap-08.

## Progress

- (2026-07-14, opus-w7-tgtslice) **CLAIMED.** Confirmed the fork verus binary
  (`source/target-verus/release/verus`, md5-identical to `tactus/source/...`
  that tgt's check.sh uses) carries the W7 def-cert wire (bootstrap-33/34/36).
  Slice = `symbol`. Plan: emit certs with `--verify-module symbol`
  `--tactus-emit-cert`, point the probe17 runner at the tgt cert dir, record the
  census + kills.

- (2026-07-14, opus-w7-tgtslice) **EMIT + BRIDGE RUN — the gate FOUND A REAL
  DIVERGENCE on corpus (the W3-style payoff).** `--verify-module symbol` emitted
  the WHOLE referenced def cone, not just symbol: **135 certs** (129 defs + 6
  datatypes across ~40 tgt modules), plus ~688 honest fail-loud rejections in
  clean named buckets (`rawvir-ctor` 128, `rawvir-closure` 71, `rawvir-block`
  140, `rawvir-def-poly` 12, `rawvir-dt-struct` 22, …). Census table in
  `probe-w0/probe20_w7_tgtslice/REPORT.md`. The bridge (`run.sh`, 135 certs,
  positive+kill each) closed **134/135**; the one FAIL is a genuine bug:
  - **`lib__runtime__RuntimeSymbol.dtcert.lean`**: `dt_eq(render_dt raw) dtdata
    = 1` is FALSE. `RuntimeSymbol { Gen(usize), Inv(usize) }`. Ground truth = the
    emitted Lean decl `inductive … | Gen (val0 : Nat) | Inv (val0 : Nat)`
    (`out/lib/TactusDefs_lib_exec__base.lean:242`). So `usize` fields lower to
    Lean **`Nat`** → production reads `TyNat` (correct). The **reference**
    `raw_vir_dt`→`dt_field_typ_data`→`typ_data` maps VIR `usize` (`IntRange::Int(_)`
    catch-all) → `TyInt` (WRONG). Reference-transcriber faithfulness gap, mirror
    side of W3's serializer gap (bootstrap-08).
  - **Root cause pinned:** `sst_serialize.rs:588 typ_data` only special-cased
    `IntRange::Nat`→TyNat, sending `usize`/`char`→TyInt. But `to_lean_type.rs:
    92-110` (the actual emission) lowers `Nat | USize | Char → "Nat"` and
    `Int | I(_) | ISize | U(_) → "Int"` (note: fixed-width `u8..u64` DO go to
    Int; only `usize`/`char`/`nat` go to Nat — a `usize` const-generic elision
    quirk, documented there). The reference `typ_data` did not mirror this.
  - **Why no earlier cert caught it:** the fixture datatypes (`Tree`) + W7e's
    synthetic mutations never used a `usize`-typed field; every passing tgt cert
    happens to have no compared-position `usize`/`char` (else it'd already
    diverge — production never emits `TyInt` for `usize`). So this is an ORGANIC
    corpus find, exactly the teeth the local model asked for — no synthetic
    injection needed.
  - **Fix (Rust-only, `sst_serialize.rs:588`):** widen the `typ_data` int-range
    arm to `IntRange::Nat | USize | Char → TyNat`, mirroring `to_lean_type`
    exactly. Provably safe for the 134 passing (they have no compared usize/char;
    production already produces TyNat there, so nothing that passes relies on the
    old TyInt). `cargo check -p lean_verify` clean; release rebuild + re-emit +
    re-bridge IN PROGRESS to confirm 135/135 + no probe9/13/14/17 regression.

- (2026-07-14, opus-w7-tgtslice) **DONE — fix validated, 135/135 close.** Fork
  vargo (`tactus-bootstrap/tools/vargo/…`, NOT the upstream on PATH which bails
  "sources changed") `build --release`: lean_verify recompiled 20.36s, vstd
  1530/0. Re-emit: the `RuntimeSymbol` cert now renders `TyNat` on BOTH sides;
  direct elaborate → positive OK + kill non-vacuous. Full `run.sh`:
  **`W7 TGT-SLICE DEF-BRIDGE OK ✓` — 135/135 positive + 135/135 kill.** No
  regression: fixture re-emit `23 verified/0 errors`, probe17 8/8 OK/OK, probe9
  16/16 close-ok. Report: `probe-w0/probe20_w7_tgtslice/REPORT.md`.

## Writeup

**DONE — the W7 defs-layer differential gate runs over real corpus, FOUND a
genuine reference-transcriber faithfulness bug (organic, on the first run over
tgt), the bug was root-caused + fixed, and the fixed gate closes 135/135 on the
tgt slice with non-vacuous kills and zero fixture regression.** This closes the
last rung of the W7 umbrella (`bootstrap-12`).

### What was run
`--verify-module symbol --tactus-emit-cert` over `tactus-group-theory/src/lib.rs`
with the fork verus binary carrying the W7 def-cert wire. Emitting only needs the
*symbol* module verified, but the shared spec-world defs emitter lowers the
**whole referenced def cone**, so the cert pass covered **135 emitted certs**
(129 spec-fn defs + 6 datatypes across ~40 tgt modules) plus **~688 honest
fail-loud rejections** in clean named buckets. `run.sh` is the probe17 runner
pointed at the tgt cert dir; `emit.sh` reproduces the emit. Full census +
buckets in `REPORT.md`.

### The bug the gate found (the payoff)
`lib__runtime__RuntimeSymbol.dtcert` — `RuntimeSymbol { Gen(usize), Inv(usize) }`
— had `dt_eq(render_dt raw) dtdata = 1` reduce to **false**. Triage (ground truth
= the emitted `inductive … | Gen (val0 : Nat)` in `TactusDefs_lib_exec__base.lean`):
- **production** (`ldt_field_typdata`) reads the emitted `Nat` → `TyNat`. Faithful.
- **reference** (`raw_vir_dt` → `dt_field_typ_data` → `typ_data`) mapped VIR
  `usize` → `TyInt`. WRONG. `typ_data` (`sst_serialize.rs:588`) only special-cased
  `IntRange::Nat`, so `usize`/`char` fell into the `Int(_)` catch-all.
- Real emission rule (`to_lean_type.rs:92-110`): `Nat | USize | Char → "Nat"`;
  `Int | I(_) | ISize | U(_) → "Int"` — note fixed-width `u8..u64` DO go to Int;
  only `usize`/`char`/`nat` → Nat (a documented `usize`-const-generic-elision
  quirk). The reference did not mirror this.
This is the mirror-side sibling of W3's serializer deref gap (bootstrap-08): a
transcriber that doesn't faithfully model the actual lowering, invisible until a
differential bridge over corpus code exercises it. Neither the fixture nor W7e's
synthetic mutations used a `usize` field, so it took real corpus to surface.

### The fix
`sst_serialize.rs:588` `typ_data`: widen the int-range arm to
`IntRange::Nat | USize | Char → TyNat`, mirroring `to_lean_type` exactly. Rust-only
(no tactus-core edit, no olean re-emit). Provably safe for the 134 previously-
passing certs: production never emits `TyInt` for `usize`/`char`, so any passing
cert with a compared-position `usize`/`char` would have ALREADY diverged — none
did, so the change can only close the one open divergence, not break a closed one.

### Validation
- Fork-vargo `build --release`: lean_verify 20.36s, vstd 1530/0.
- tgt bridge (`run.sh`): **135/135 positive OK + 135/135 kill non-vacuous** — the
  `RuntimeSymbol` cert now renders `TyNat` both sides and closes.
- No regression: fixture re-emit `23 verified/0 errors`; probe17 (fixture def
  bridge) 8/8 OK/OK; probe9 (obligation refWp bridge) 16/16 close-ok (incl.
  `max_u64`, a `u64` fn → `Int` on both sides, confirming the fix touched only
  `usize`/`char`).

### Assumptions / honest scope
1. Slice = the `symbol`-module referenced cone (135 certs). Not the entire crate
   (every module's cone); a different entry module would emit a different (over-
   lapping) cone. The 6 datatypes + 129 defs here already span the core W7 vocab
   (Match / Ite / BinOp / Field / single+multi-arg Call / multi-variant inductive).
2. The gate certifies the two transcriptions AGREE (Friction-class). It does not
   certify that `usize → Nat` faithfully MODELS a bounded Rust int (that upper-
   bound-erasure is a known W5 soundness concern, documented at
   `to_lean_type.rs:104-108`); W7 only makes the reference agree with what
   production actually emits.
3. The fork verus binary I rebuilt is `tactus-bootstrap/source/…`; tgt's
   `check.sh` uses `tactus/source/…` (a separate tree, still on the OLD
   serializer). Landing this fix into the tactus tree is a trivial follow-on
   (same one-line edit); noted so a future instance doesn't assume the tgt
   check.sh binary already has it.

   **CORRECTION (2026-07-14, opus-w4): assumption #3 above is a PHANTOM — there
   is NOTHING to port.** The `sst_serialize.rs` reference-transcriber is a
   bootstrap-ONLY file; it does not exist in `tactus/source` at all (grepped:
   no `sst_serialize`, no `struct Serializer`, no `fn typ_data`, no
   `TypData.TyNat/TyInt`, no cert-emission machinery under
   `tactus/source/lean_verify/src/`). The bug was purely in the reference
   transcriber, which only runs in the bootstrap differential gate. The
   PRODUCTION emitter that `check.sh`'s tactus binary actually uses,
   `to_lean_type.rs`, is **byte-identical** between the two trees (`diff` clean)
   and ALREADY had the correct `Nat | USize | Char → "Nat"` mapping
   (`to_lean_type.rs:96-109`). So `check.sh` verifying tgt crates was never
   affected by this bug and needs no change. "still on the OLD serializer" was a
   wrong guess — the tactus tree has no reference serializer to be old about.
4. `-V cache` warms verification results only; cert EMISSION is uncached and
   re-ran fresh (out dir cleared before re-emit).
