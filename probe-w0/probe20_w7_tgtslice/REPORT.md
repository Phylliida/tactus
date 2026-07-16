# W7 tgt-slice defs-layer bridge — results (bootstrap-37)

The W7 defs-layer differential gate run over **real corpus** code
(`tactus-group-theory`), not the hand-authored `bootstrap-fixture` family. This
is the defs-layer analog of W3 (bootstrap-08, the obligation-layer tgt run): the
bug-finding payoff of the certificate pattern comes from pointing it at code the
fixture never exercised.

## How it was run

- **Emit** (`emit.sh`): the fork verus binary (md5-identical to the one tgt's
  `check.sh` uses, carrying the W7 def-cert wire from bootstrap-33/34/36) run
  over `tactus-group-theory/src/lib.rs` with
  `--lean-backend --emit-lean --lean-all-proofs --tactus-emit-cert
  --verify-module symbol`. Although only module `symbol` is *verified*, the
  shared spec-world defs emitter lowers the **whole referenced def cone**
  (tgt + vstd), so the cert pass covers far more than one module — every spec fn
  and datatype the slice transitively references.
- **Bridge** (`run.sh`): the probe17 runner pointed at the tgt cert dir. Each
  emitted `.defcert`/`.dtcert` is self-contained (`import TactusDefs_lib_exec` +
  `cert_<leaf>_raw` + `cert_<leaf>_{def,dt}data` +
  `example : lib.{def,dt}_eq (lib.render_{def,dt} raw) data = 1 := by decide`),
  so elaborating it against `tactus-core/out/lib` IS the bridge. Per file:
  `positive` (elaborates rc=0) + `kill` (flip `= 1`→`= 0`; `decide` must reject).

## Census — emitted (bridge subjects) vs honest fail-loud rejections

The reference VIR transcriber (`raw_vir_exp`/`raw_vir_def`/`raw_vir_dt`) is
**fail-loud**: any construct outside the W7 in-scope vocabulary emits **no cert**
(a named `rawvir-*` reason), so it is a scope gate, NOT a bridge subject. Only the
constructs the fixture proved (Match / Ite / BinOp / Field / single+multi-arg
Call / multi-variant inductive datatype) produce a cert.

| | emitted (bridge subject) | fail-loud rejected (scope gate) |
|---|---|---|
| **spec-fn defs** | **129** | 664 |
| **datatypes** | **6** | 24 |

### def-cert rejection buckets (all named, all no-cert)

| reason | count | meaning |
|---|---|---|
| `rawvir-block` | 140 | body is a `let`-bearing block (needs reference `Let` arm) |
| `rawvir-ctor` | 128 | body builds a datatype constructor (`Symbol::Gen(i)` class) |
| `rawvir-readplace-nonlocal` | 75 | reads a non-local place (field/global) |
| `rawvir-closure` | 71 | lambda/closure body (deferred by design §5) |
| `typ-specfn` | 54 | higher-order: spec-fn type in a param/ret |
| `rawvir-unary-nonclip` | 40 | non-`Clip` unary op |
| `rawvir-call-arity` | 39 | 0-arg / unhandled-arity call |
| `rawvir-multi` | 37 | multiple deferred constructs |
| `rawvir-arrayliteral` | 20 | array/seq literal |
| `rawvir-withtriggers` | 16 | `with_triggers` quantifier |
| `rawvir-def-poly` | 12 | polymorphic spec fn (vstd `Seq`/`Set`) |
| `rawvir-choose` | 10 | `choose` expression |
| `rawvir-place` | 7 | place expression |
| `rawvir-arm-pat` | 6 | match arm with a non-trivial pattern |
| `rawvir-call-nonfun` | 4 | call target not a plain fn |
| `rawvir-field-pat` | 2 | field pattern |
| `rawvir-binaryopr` | 2 | unhandled binary opcode |
| `rawvir-unaryopr` | 1 | unhandled unary opcode |

### dt-cert rejection buckets

| reason | count | meaning |
|---|---|---|
| `rawvir-dt-struct` | 22 | single-variant record datatype (reference gates to multi-variant `inductive`) |
| `rawvir-dt-poly` | 2 | polymorphic datatype (`Option`, `Set`) |

The `symbol` module itself: 3/4 spec fns certified (`generator_index` [Match],
`is_inverse_pair` [Call+BinOp], `symbol_valid` [Call+BinOp]); `inverse_symbol`
correctly rejected `rawvir-ctor` (its Match arms build `Symbol::Gen(i)`/`Inv(i)`
— a datatype-ctor application in expression position, outside W7 scope). The
`Symbol` enum datatype certified (`lib__symbol__Symbol.dtcert.lean`).

## Bridge result

**First run (buggy reference): 134/135 closed; 1 real divergence found.**

| | positive (closes) | kill (non-vacuous) |
|---|---|---|
| 134 certs | OK | OK |
| `lib__runtime__RuntimeSymbol.dtcert` | **FAIL** | (the `= 0` flip is the TRUE one → kill reads "VACUOUS", same root) |

The single failure is a genuine **reference-transcriber faithfulness gap** —
the W3-style bug-finding payoff, on the mirror (reference) side:

- `RuntimeSymbol { Gen(usize), Inv(usize) }`. The emitter lowers a `usize` field
  to Lean `Nat` (ground truth: `out/lib/TactusDefs_lib_exec__base.lean:242` —
  `inductive … | Gen (val0 : Nat) | Inv (val0 : Nat)`).
- **production** `ldt_field_typdata` reads that emitted `Nat` → `TyNat` ✓ (faithful).
- **reference** `raw_vir_dt` → `dt_field_typ_data` → `typ_data` mapped VIR `usize`
  → `TyInt` ✗. `typ_data` (`sst_serialize.rs:588`) only special-cased
  `IntRange::Nat`; `usize`/`char` fell into the `Int(_)` catch-all → `TyInt`.
- But `to_lean_type.rs:92-110` (the real emission rule) lowers
  `Nat | USize | Char → "Nat"` and `Int | I(_) | ISize | U(_) → "Int"` — note
  fixed-width `u8..u64` DO go to `Int`; only `usize`/`char`/`nat` → `Nat`
  (a documented `usize`-const-generic elision quirk). The reference did not
  mirror this.

**Why the fixture/W7e never caught it:** no fixture datatype nor W7e synthetic
mutation used a `usize` field. Every *passing* tgt cert has no compared-position
`usize`/`char` (production never emits `TyInt` for them, so any such cert would
already diverge). So this is an **organic corpus find** — the differential gate
discriminating on real code, no synthetic injection required. It directly answers
the "is the gate toothless on this slice?" concern: it is not.

**Fix** (`sst_serialize.rs:588`, Rust-only): widen the `typ_data` int-range arm
to `IntRange::Nat | USize | Char → TyNat`, mirroring `to_lean_type` exactly. Safe
for the 134 passing (they carry no compared `usize`/`char`; production already
produces `TyNat` there).

**Second run (fixed reference): 135/135 closed, all kills non-vacuous.** After
the `typ_data` fix + `vargo build --release` (fork vargo, vstd 1530/0) + re-emit,
the re-emitted `RuntimeSymbol` cert renders both sides `TyNat` and the bridge
closes; `run.sh` reports `W7 TGT-SLICE DEF-BRIDGE OK ✓` over all 135 certs
(129 defs + 6 datatypes: `Dir`, `PredDerivationStep`, `DerivationStep`,
`RuntimeSymbol`, `Symbol`, `ScanResult`), every one positive-OK + kill-OK.

**No regression** on the fixture: re-emit (`23 verified, 0 errors`), probe17
(fixture def bridge) 8/8 OK/OK, probe9 (obligation refWp bridge) 16/16 close-ok
(incl. `max_u64`, a `u64` fn — confirms fixed-width unsigned still maps to `Int`
on both sides, i.e. the fix touched ONLY `usize`/`char`). The change is in the
Rust serializer (TCB), not tactus-core, so the tactus-core render-logic probes
(probe13/14) are structurally unaffected.

## Acceptance (bootstrap-37 "done when") — MET

- real tgt emit writes `.defcert`/`.dtcert` for the slice cone — **✓** (135 certs).
- every emitted cert closes OR is a triaged honest rejection — **✓** (135/135
  close after the fix; ~688 rejections all named `rawvir-*`/`typ-specfn` scope
  gates; the one organic divergence was root-caused + fixed, not papered over).
- per-file mutation-kill non-vacuous — **✓** (135/135 kill-OK).
- census table recorded — **✓** (above).

## Acceptance (bootstrap-37 "done when")

- real tgt emit writes `.defcert`/`.dtcert` for the slice cone — **✓** (135 certs
  across ~40 tgt modules + the `Symbol`/`Dir`/`ScanResult`/… datatypes).
- every emitted cert closes its bridge OR is a triaged honest rejection —
  _(pending full run)_; all rejections are named `rawvir-*`/`typ-specfn` scope
  gates (no silent divergence).
- per-file mutation-kill non-vacuous — _(pending)_.
- census table recorded — **✓** (above).
