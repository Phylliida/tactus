# probe16 — W7d defs-layer bridge (board bootstrap-32)

**Verdict: OK ✓** (rc=0, ~1.25s). Every `example` elaborated as classified;
the non-vacuity meta-check confirms `decide` is testing real (in)equality.

## What this probe proves

The def-layer analog of probe9's obligation bridge. Where probe15 (W7a) hand-wrote
the defs-layer vocabulary in a standalone file, **probe16 imports the REAL emitted
tactus-core** (`TactusDefs_lib_exec`, carrying the LANDED `render_def`/`def_eq`/
`render_dt`/`dt_eq`) and feeds it the **exact strings the W7c transcribers emit** —
copied verbatim from the serializer unit tests. So it validates end-to-end that:

1. the actual serializer TEXT FORMAT elaborates against the real emitted Lean, and
2. `def_eq`/`dt_eq` **close** (`= 1`) on real transcriber output, and
3. the bridge is **non-vacuous** — a perturbed production side flips it to `0`.

All without a `vargo` release rebuild (the strings are the unit-test-pinned
transcriber output; the rebuild is only needed to wire the *live* emit path).

## Verdict matrix

| # | bridge | pair | tactic | expect | got |
|---|--------|------|--------|--------|-----|
| 1 | `def_eq (render_def raw_tri) defdata_tri` | `tri` header + trivial `Var n` body | decide | 1 | ✓ |
| 2 | (same) | | rfl | 1 | ✓ |
| 3 | `def_eq (render_def raw_g) defdata_g` | Ite-bodied def | decide | 1 | ✓ |
| 4 | (same) | | rfl | 1 | ✓ |
| 5 | `dt_eq (render_dt raw_tree) dtdata_tree` | `Tree` datatype (FULL fidelity) | decide | 1 | ✓ |
| 6 | (same) | | rfl | 1 | ✓ |
| 7 | `def_eq … defdata_tri_bad_body` | body atom mutated (`Atom 2`≠`Atom 1`) | decide | 0 | ✓ |
| 8 | `def_eq … defdata_tri_bad_ret` | ret type mutated (`TyInt`≠`TyNat`) | decide | 0 | ✓ |
| 9 | `def_eq … defdata_g_swapped` | Ite then/else atoms swapped | decide | 0 | ✓ |
| 10 | `dt_eq … dtdata_tree_peeled` | **W7a §7 Q4 kill** — `Node` field peeled `TyNamed 0` vs kept `TyBox 0` | decide | 0 | ✓ |
| 11 | `dt_eq … dtdata_tree_bad_ctor` | ctor id mutated (`Leaf`=9≠1) | decide | 0 | ✓ |
| meta | `def_eq (render_def raw_tri) defdata_tri = 0` | correct pair | decide | **fail** | ✓ (rc≠0) |

## Provenance of the literals (why this is "real" transcriber output)

Every positive-side string is copied verbatim from a serializer unit test — the
tests `assert_eq!` the transcriber output against exactly these strings:

- `raw_tri` / `defdata_tri` ← `raw_vir_def_tri_header` / `ldef_to_defdata_tri_header`
  (`sst_serialize_tests.rs`): name `lib::tri`=0, param `n`=1 : `TyNat`, ret `TyNat`,
  body `RawExp.Var 1 TyNat` (ref) / `ExprData.Atom 1` (prod).
- `raw_g` / `defdata_g` body ← `raw_exp_ite_body` / `lexpr_to_exprdata_ite_body`
  (interning c=0/t=1/e=2). The header (name=3, `ParamList.Nil`, ret `TyInt`) is
  synthetic — the point is the BODY: `render_exp(Ite TyInt …)` reproduces the
  production `ExprData.Ite` (all branches `TyInt` ⇒ `needs_nat_coercion` is 0, so
  no `Int.toNat` is inserted). The `RawExp.Ite` vocab is surface-agnostic (SST
  `raw_exp` and VIR `raw_vir_exp` emit the same shape).
- `raw_tree` / `dtdata_tree` ← `raw_vir_dt_tree` / `ldt_to_dtdata_tree`: the FULL
  emitted `Tree` shape — name `lib.Tree`=0, `Leaf`=1 [`TyInt`], `Node`=2
  [`TyBox 0`, `TyBox 0`], with the Box KEPT (not peeled). This is the real
  datatype fidelity, no simplification.

## Honest scope / what this does NOT yet cover

- **The `tri` def is the header + trivial-body pin**, not the full `if`-bodied
  `tri`. The Ite-bodied case (`raw_g`/`defdata_g`) covers a non-trivial body but
  with a synthetic header. A single fully-real `tri` (real header + real Ite
  body from one Serializer run) arrives with the generate.rs emit wire, which
  needs the release rebuild.
- **No live emit path yet.** The transcribers are still `#[allow(dead_code)]`;
  this probe consumes their pinned output, it does not exercise `emit_cert`.
  Wiring `emit_def_cert` at the `spec_fn_to_ast` / datatype call sites (behind
  the cert-emit flag) is the remaining W7d work (board bootstrap-32 Writeup).
- **Monomorphic only** — polymorphic defs/datatypes fail loud on the reference
  side (`rawvir-def-poly` / `rawvir-dt-poly`), so they never reach the bridge.

## Reproduce

```
probe-w0/probe16_w7d_defbridge/run.sh
```
(`LEAN=<lean>` / `TACTUS_PRELUDE=<dir>` to override; needs `tactus-core/out/lib`
oleans present, same as probe9.)
