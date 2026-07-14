# W2b bridge acceptance — fixture-scale results (bootstrap-07)

`run.sh` builds, per fixture cert `<fn>.cert.lean`, the bridge

    example : lib.goals_eq (lib.ref_wp cert_<fn>_ctx cert_<fn>_sst)
                           cert_<fn>_goals = 1 := by decide   (and := by rfl)

and elaborates it against tactus-core's emitted defs (which carry `ref_wp` /
`goals_eq` + the mirror types). The cert files are gitignored/regenerable; the
runner consumes whatever is on disk. Regen recipe: board/bootstrap-15 Progress.

## Result (2026-07-14, post-bootstrap-02b Call-arm certs; lean v4.25.0, prelude-e81fbf9a86375c12)

Census 13/16 (3 `call-generic` rejections: vec_read/vec_push7/fill_zeros). The
Call arm (bootstrap-02b) now emits `quad_exec` + `double_exec` + `count_down`;
`head_exec` was fixed (bootstrap-18) and now CLOSES.

| fn          | verdict     | decide | rfl  | class       |
|-------------|-------------|-------:|-----:|-------------|
| add_capped  | close-ok    | 1.31s  | 1.35s| CLOSE       |
| count_down  | hfail-ok    | 1.28s  | 1.22s| HONEST-FAIL (two-way If-join, §2.4.1) |
| double_exec | close-ok    | 1.32s  | 1.25s| CLOSE       |
| find_square | close-ok    | 2.03s  | 1.99s| CLOSE (17 goals, nested loop + if-fallthrough) |
| head_exec   | close-ok    | 1.17s  | 1.22s| CLOSE (bootstrap-18: ref-param deref) |
| id_generic  | close-ok    | 1.17s  | 1.24s| CLOSE       |
| max_u64     | hfail-ok    | 1.24s  | 1.30s| HONEST-FAIL |
| mk_point    | close-ok    | 1.19s  | 1.29s| CLOSE       |
| quad_exec   | close-ok    | 1.33s  | 1.27s| CLOSE (the Call-arm fixture target) |
| scope_shape | close-ok    | 1.15s  | 1.28s| CLOSE       |
| sum_to      | close-ok    | 1.71s  | 1.75s| CLOSE (12 goals, single loop) |
| swap_pair   | close-ok    | 1.21s  | 1.22s| CLOSE       |
| tri_one     | close-ok    | 1.21s  | 1.22s| CLOSE       |

**11 CLOSE (by both `decide` and `rfl`), 2 documented HONEST-FAIL (13 certs).
Runner exit 0 ("ALL BRIDGES BEHAVE AS CLASSIFIED").**

Timing: ~1.1–2.1 s/fn wall-clock (whole `lean` process incl. import), far below
the P2 600-stm ≈ 2.8 s baseline. `find_square` (17 goals, the nested-loop +
if-fallthrough stress fn) is the slowest at ~2.0 s. `decide` and `rfl` are
within noise of each other. (Most of the ~1.1 s floor is olean import, not the
`decide` itself.)

## The two HONEST-FAILs are SOUND, not regressions

Both honest-fails are divergences where the strict `goals_eq` correctly does NOT
silent-pass. A honest-fail that suddenly *closed* would mean refWp went lax or a
serializer caveat was silently "fixed" — the runner treats that as a FAILURE too
(class HONEST-FAIL expects the `= 1` bridge to NOT elaborate).

- **max_u64** — branch-in-leaf (DESIGN §2.4.1, leaf rendering not certified §2.5).
  The frontend lifts the fall-through `if x<y {y} else {x}` INTO the ensures leaf
  (`x<y → let r := (let m := y); …`) before the SST snapshot; refWp folds the
  raw per-ensures leaves. refWp ≠ production by leaf text. Known since W2a.

- **count_down** — two-way If-join not merged (DESIGN §2.4.1; NEW, surfaced by
  bootstrap-02b making count_down emittable). `if n==0 {0} else {recurse}` —
  BOTH branches fall through to a common `Ret`. `frame_after(f, If)` returns the
  pre-If frame `f` (the merge special case needs `diverges(then) && is_skip(else)`,
  which only fires for the early-return fall-through of bootstrap-17), so the
  common Ret closes under the bare pre-If frame — missing each branch's local
  `tmp__3` binding. refWp emits **3** goals; production **4**. Pinpoint-proved
  (by `decide`): rw goal 0 = prod assert, rw goal 1 = prod termination (so the
  goals AROUND the recursive Call match production exactly — the **Call arm is
  faithful**), and rw goal 2 = the bare-frame Ret postcond, matching neither
  branch's production postcond; production's then-branch postcond is missing
  entirely. This is a control-flow-modeling gap in refWp, NOT a Call-arm or leaf
  bug. Follow-up: **board/bootstrap-19** (model the two-way If-join).

**Now-fixed (was honest-fail):** `head_exec` — the ref-param deref
(`r == tree_head(*t)` on `t: &Tree`) was a serializer `oblig_leaf` empty-ctx gap;
bootstrap-18 routed the obligation leaves through the binder-aware `render_ctx()`
so `*t → t.deref` matches production. It now CLOSES (removed from the honest-fail
set; the runner would flag it as a reclassify-required regression if it silently
went back to failing).

## Reproduce

    LEAN=<lean-v4.25.0> bash probe-w0/probe9_bridge/run.sh

Auto-locates the cert dir, tactus-core/out/lib, and the prelude cache
(`TACTUS_PRELUDE` to override). Needs the post-findings certs on disk
(`--tactus-emit-cert` regen) and tactus-core's `out/lib` oleans current.
