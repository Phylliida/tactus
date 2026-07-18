---
title: "persistent Lean driver: snapshot-branching per-fn checks (DESIGN-lean-driver.md built)"
status: in-review
claimed_by: claude (e2e-speed branch)
created: 2026-07-18T00:00:00Z
updated: 2026-07-18T00:00:00Z
---

## What landed (commits ecfce75, 83ad023, 4947a86)

DESIGN-lean-driver.md, built as designed with one addition (the
`wide_search` snapshot) and one honest correction (the routing floor).

- `lean_verify/driver/TactusDriver.lean` — persistent driver, JSON
  lines on stdin/stdout (`snapshot` / `check` / `exit`). A snapshot is
  an `importModules (loadExts := true)` env (~1s); each check
  elaborates a file's post-header commands against a fresh
  `Command.mkState` branch (~ms-to-real-proof-time) and `writeModule`s
  an ordinary olean on success. Validated standalone against real
  emitted trees before any Rust (probes/drive_requests.py,
  drive_fail.py): verdict parity both directions, mini-Link
  (#print axioms) identical against driver-built vs CLI-built oleans.
- `driver_client.rs` — global client pool; minimal-covering snapshot
  selection (stmt oleans must record base imports, not wide's
  self-including set); any fault disables routing for the run and
  falls back to process-per-file. `TACTUS_DRIVER=0` opt-out;
  `TACTUS_DRIVER_MIN_JOBS` (default 6) routing floor.
- `prime_lean_driver` (generate.rs) + verifier.rs hook — before the
  worker pool: run package EMISSION for every job (stashed in
  PRIME_OUTCOMES; re-emitting in workers would corrupt M5e changed
  flags), build stmt oleans workers-parallel through the drivers,
  establish `wide` and `wide_search` (= wide + TactusSearch)
  snapshots, return a largest-pkg-first claim order for the pool.

## Gates (all on the branch @ merge of main ab8e7cd)

- e2e suite: 550/1 — identical failure set to branch baseline
  (test_exec_vec_field_index_clone; fixed on newer main). Zero
  regressions with driver default-on.
- tactus-core: 141/0 every run, package gate + Link discharge green on
  driver-produced oleans; emission hash 3/3 identical
  (fbc2aff3be1c4df3, same as pre-driver — the driver changes no bytes).
- Diagnostics parity: failing-tree probe → identical verdict counts
  AND identical error lines, driver vs CLI.

## Honest performance accounting → DEFAULT = OPT-IN

- tactus-core cold (8 threads, --lean-all-proofs): wall 85s → 82s.
  All 94 pkg checks route in-driver (was 94 × ~2s processes);
  verus-side CPU 3m54s → 28s user. The wall is real elaboration: ONE
  obligation (wp_stm_sound case 53) takes 48s alone — see probe-wp53/
  — plus the defs ladder and an ~11s gate tail.
- gt, FAIR pair (same binary, warm Z3, cold lean): driver ON 2m25 vs
  OFF 1m59 — ON is +26s WALL while saving ~3min CPU. gt's snapshots
  import the 107-part defs closure (heavy), and its per-fn lean mass
  is too small to amortize. (Also: ON verified 24 fns vs OFF 14 on
  identical state — unexplained counting difference, investigate
  before any default-on.)
- Small crates: the driver's fixed cost loses below ~6 lean fns
  (TACTUS_DRIVER_MIN_JOBS floor).

Verdict: on today's crates the driver is a CPU optimization, not a
wall one — earlier arcs (slim prelude, per-fn parallelism, M5e,
parallel defs below) already ate the process overhead it targets.
**Default flipped to opt-in (`TACTUS_DRIVER=1`)**; wall-bound daily
gates keep the process path; CPU-bound contexts (low-core boxes where
CPU IS wall, thermal/shared machines) opt in. Leaf-normal emission
(N3/N4) shrinking per-check goals will shift the economics — re-measure
then.

## Bonus landed: parallel defs-part builds (unconditional win)

gt's ACTUAL lean phase was 107 defs-family part builds running FULLY
SERIAL (95s, max concurrency 1) — per-fn checks were never the cost.
crate_defs now builds parts level-parallel over the dependency DAG
(serial decision pass keeps M5e breaking/superset semantics
byte-identical; manifests write only after successful builds — a fresh
manifest over a stale olean would let consumers skip re-elaboration;
build dirs are per-module so a failing part can't delete siblings'
workspace). Measured: 107 builds 95s → 26s at 8-way; gt wall
3m38 → 2m54 same-state, and the win applies in BOTH driver modes.
`TACTUS_DEFS_BUILD_JOBS` overrides the worker count.

## Measurement hygiene note

The `-V cache` Z3 cache misses ~everything across a BINARY REBUILD
(observed repeatedly: same crate, same rustc/Z3, rebuild between runs
→ 0 cached). The documented invalidation list (Z3/solver/rustc) is
incomplete. Time A/B pairs on ONE binary only.

## probe-wp53 (tactus-core's true lean bottleneck)

One theorem = the whole module cost: 38KB let-laden WP statement;
`cases s` fans ~10 arms; each re-runs zetaDelta simp_all over the full
context (~4-5s/arm). Measured dead ends: no-zetaDelta (fails, slower),
omega-first (no change), pre-cases zeta pass (fails). Fix = statement
shape (N3/N4 leaf-normal emission); the probe is that arc's benchmark.

## Known v1 limits (follow-on candidates)

- Defs-ladder builds stay CLI (13s serial on tactus-core's critical
  path; driver could take them with a prelude-only snapshot phase).
- One driver pool per process, cleared per crate prime — fine for CLI
  runs and the mcp server's serial checks; concurrent multi-crate
  checking in one process would thrash the pool.
- Driver boot re-elaborates the script each spawn (~1.5s); could be
  precompiled into the prelude cache.
- Islands and check_lean_file consumers don't route (headers won't
  match snapshots — automatic, correct, just unaccelerated).
