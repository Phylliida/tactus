# W2b bridge acceptance — fixture-scale results (bootstrap-07)

`run.sh` builds, per fixture cert `<fn>.cert.lean`, the bridge

    example : lib.goals_eq (lib.ref_wp cert_<fn>_ctx cert_<fn>_sst)
                           cert_<fn>_goals = 1 := by decide   (and := by rfl)

and elaborates it against tactus-core's emitted defs (which carry `ref_wp` /
`goals_eq` + the mirror types). The cert files are gitignored/regenerable; the
runner consumes whatever is on disk. Regen recipe: board/bootstrap-15 Progress.

## Result (2026-07-14, post-b17 certs; lean v4.25.0, prelude-e81fbf9a86375c12)

| fn          | verdict     | decide | rfl  | class       |
|-------------|-------------|-------:|-----:|-------------|
| add_capped  | close-ok    | 1.36s  | 1.39s| CLOSE       |
| double_exec | close-ok    | 1.17s  | 1.22s| CLOSE       |
| find_square | close-ok    | 1.99s  | 2.10s| CLOSE (17 goals, nested loop + if-fallthrough) |
| head_exec   | hfail-ok    | 1.15s  | 1.19s| HONEST-FAIL |
| id_generic  | close-ok    | 1.20s  | 1.20s| CLOSE       |
| max_u64     | hfail-ok    | 1.31s  | 1.18s| HONEST-FAIL |
| mk_point    | close-ok    | 1.13s  | 1.22s| CLOSE       |
| scope_shape | close-ok    | 1.23s  | 1.18s| CLOSE       |
| sum_to      | close-ok    | 1.70s  | 1.66s| CLOSE (12 goals, single loop) |
| swap_pair   | close-ok    | 1.23s  | 1.20s| CLOSE       |
| tri_one     | close-ok    | 1.23s  | 1.14s| CLOSE       |

**9 CLOSE (by both `decide` and `rfl`), 2 documented HONEST-FAIL. Runner exit 0
("ALL BRIDGES BEHAVE AS CLASSIFIED").**

Timing: ~1.1–2.1 s/fn wall-clock (whole `lean` process incl. import), far below
the P2 600-stm ≈ 2.8 s baseline. `find_square` (17 goals, the nested-loop +
if-fallthrough stress fn) is the slowest at ~2.0 s. `decide` and `rfl` are
within noise of each other. (Most of the ~1.1 s floor is olean import, not the
`decide` itself.)

## The two HONEST-FAILs are SOUND, not regressions

Stage A does not certify leaf rendering (DESIGN §2.5). Both honest-fails are
leaf-content divergences where the strict `goals_eq` correctly does NOT
silent-pass. A honest-fail that suddenly *closed* would mean refWp went lax or a
serializer caveat was silently "fixed" — the runner treats that as a FAILURE too
(class HONEST-FAIL expects the `= 1` bridge to NOT elaborate).

- **max_u64** — branch-in-leaf (DESIGN §2.4.1). The frontend lifts the
  fall-through `if x<y {y} else {x}` INTO the ensures leaf
  (`x<y → let r := (let m := y); …`) before the SST snapshot; refWp folds the
  raw per-ensures leaves. refWp ≠ production by leaf text. Known since W2a.

- **head_exec** — ref-param deref (NEW, found by this runner). Ensures
  `r == tree_head(*t)` on `t: &Tree`. The serializer's `oblig_leaf` (empty
  RenderCtx) renders `*t` as bare `t` → SST ens leaf 3
  `⟦…r = tree_head t⟧`. Production's postcondition renders `t.deref` → goal
  leaf 6 `⟦…r = tree_head t.deref⟧`. Pinpoint-proved that the obligation leaf
  (3 vs 6) is the **sole** divergence: `goals_eq refWp (goals with leaf 6→3) = 1`.
  Same span, different text. This is the reference-param sibling of finding-4's
  documented "empty-RenderCtx does not replicate a coercion/subst" caveat →
  a serializer faithfulness gap, spun out as its own card (see board) and logged
  in DESIGN §5 triage. Not a refWp bug; not a production bug.

## Reproduce

    LEAN=<lean-v4.25.0> bash probe-w0/probe9_bridge/run.sh

Auto-locates the cert dir, tactus-core/out/lib, and the prelude cache
(`TACTUS_PRELUDE` to override). Needs the post-findings certs on disk
(`--tactus-emit-cert` regen) and tactus-core's `out/lib` oleans current.
