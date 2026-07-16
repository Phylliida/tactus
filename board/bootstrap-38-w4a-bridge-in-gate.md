---
title: "W4a — run the kernel bridge INSIDE the package gate (opt-in --tactus-bridge)"
status: done
claimed_by: opus-w4a
created: 2026-07-14T13:35:00Z
updated: 2026-07-14T15:05:00Z
---

## Description

First concrete sub-step of W4 (`bootstrap-09`). Move the `decide` bridge out of
the external probe `run.sh` scripts and into `check_package`, behind a new
opt-in flag `--tactus-bridge` (OFF by default — W4c does the default flip). No
verdict change yet when the flag is off.

Spec: `DESIGN-bootstrap.md` §4.4 (where the bridge lives) + §5 (W4 row);
`bootstrap-09` Progress (the code recon + crux risk).

**Scope (opt-in, no default change):**
- Add `--tactus-bridge` to `config.rs` (mirror `--tactus-emit-cert` at
  `config.rs:370` / `verifier.rs:2608`).
- Locate tactus-core's built `out/lib` oleans (the ones carrying `ref_wp`,
  `goals_eq`, and the mirror constructors). Settle provenance: env var pointer
  vs. sibling-crate convention. This is the crux plumbing (see `bootstrap-09`).
- In `check_package` (`generate.rs:3163`), when the flag is on: for each fn that
  emitted an obligation cert, emit a per-fn Bridge module (the cert body + the
  `example : goals_eq (ref_wp ctx sst) goals = 1 := by decide` the probe runners
  append), and elaborate it via the existing `ensure_stmt_olean`/`run_lean`
  plumbing with tactus-core `out/lib` added to `base_path` (today
  `generate.rs:3219` = `prelude_dir : defs.dir`).
- Collect PASS/FAIL into the report (do NOT wire failure→error yet; W4c does
  that). Print a note line `"N obligations bridge-checked (K passed, J failed)"`
  so the behavior is visible while opt-in.

**Decide in this card (open Qs from `bootstrap-09`):**
1. Obligation certs only, or also def_eq/dt_eq certs (W7, broader — 135 on the
   symbol cone)? Recommend obligation-only for W4a, add defs in a follow-on.
2. tactus-core olean provenance (the plumbing above).

**Done when:** `verus --lean-backend --tactus-package-check --tactus-bridge`
over the bootstrap-fixture (or the W3 tgt slice) elaborates the bridge modules
in-process and reports PASS/FAIL matching what probe9/probe11 `run.sh` report
externally today — same `decide`, same verdicts, now inside the gate. Flag OFF
= byte-identical gate behavior to today (no regression). Suite green.

**Blocked by:** nothing new — W3 (bootstrap-08) done, R1 package layers landed.

## Progress

- (2026-07-14, opus-w4a) **CLAIMED + implemented the in-gate bridge.** Both
  open Qs settled; local model consulted on the provenance fork (agreed).

  **Recon (the exact external bridge shape being promoted):** probe9/probe11
  `run.sh` append, per emitted cert `<out>/<crate>/cert/<leaf>.cert.lean`:
  `example : lib.goals_eq (lib.ref_wp cert_<leaf>_ctx cert_<leaf>_sst)
  cert_<leaf>_goals = 1 := by decide`, and elaborate with
  `LEAN_PATH=<tactus-core/out/lib>:<prelude>`. The cert imports
  `TactusDefs_lib_exec` (a `tactus-core/out/lib` olean carrying `ref_wp` /
  `goals_eq` + mirror ctors). Today `check_package`'s `base_path` =
  `prelude_dir:defs.dir` (`generate.rs:3243`) — **no pointer to tactus-core**.
  That gap is the whole crux.

  **Q1 (coverage) — obligation certs only for W4a.** The bridge step reads
  `<out>/<crate>/cert/*.cert.lean` and bridges only those carrying a
  `cert_<leaf>_goals` def (an all-excluded fn emits ctx+sst but no goal
  section — bridging it would reference an undefined name = a false FAIL, so
  it's skipped). Defs-layer `def_eq`/`dt_eq` certs (W7, broader) are a
  follow-on, as the card recommended.

  **Q2 (tactus-core provenance) — explicit env var `$TACTUS_CORE_OUT`**,
  matching the existing `$TACTUS_PRELUDE` / `$TACTUS_CORE_VOCAB` convention
  (auto-discovery across checkout layouts deliberately avoided — brittle).
  Unset (or dir missing `TactusDefs_lib_exec.olean`) ⟹ the bridge SKIPS with a
  loud note; opt-in, so no default gate path breaks. The dir's olean
  content-hash (FNV-1a over sorted `.olean` bytes, `core_olean_hash`) is
  recorded in the note NOW — audit trail for W4a and the seed of W4b's cache
  key (a `ref_wp`/`goals_eq` change flips the digest ⟹ no future stale PASS).

  **Code landed (all behind opt-in `--tactus-bridge`, OFF by default):**
  - `config.rs`: `OPT_TACTUS_BRIDGE` + optflag + `Args.tactus_bridge`;
    `--tactus-bridge` **implies `--tactus-emit-cert`** (the bridge consumes
    the emitted certs). `common/mod.rs` test-harness whitelist line added.
  - `verifier.rs:2611`: `generate::set_bridge_enabled(args.tactus_bridge)`
    (mirrors `set_cert_emit_enabled`). `run_package_gate` prints the bridge
    note in the success branch — **note only, never `count_errors`** (W4c
    flips that).
  - `generate.rs`: `BRIDGE_ENABLED` atomic + `set_bridge_enabled`;
    `PackageGateReport.bridge_note: Option<String>` (`None` when flag off or
    core oleans absent); `run_bridge_step` (locate `$TACTUS_CORE_OUT`, hash,
    per-cert concat + `run_lean` into `<out>/<crate>/bridge/Bridge_<leaf>.lean`
    with `core_out:base_path`, tally) + `core_olean_hash`. Bridge failures go
    to a LOCAL `failures` vec, never the gate's — so flag-on can't change the
    error count in W4a.
  - `sst_serialize.rs`: `pub fn cert_ns()` exposing `NS` for the bridge term.
  - Note line: `"N obligations bridge-checked against tactus-core (K passed, J
    failed) [core-olean fnv1a:…]"` (+ `; failed: …` when any fail).

  **Status:** code written; fork release build (`vargo build --release`) in
  flight to confirm it compiles. NOT yet run end-to-end against the tgt/fixture
  certs (the done-criterion) — next step after the build is green.

- (2026-07-14, opus-w4a) **BUILT + VALIDATED END-TO-END.** Fork release build
  green (vstd 1530/0). Key finding while testing: `check_package` runs only
  when the krate has ≥1 **tactic proof fn** (`build_tactic_bodies_map` is
  proof-mode-only, `verifier.rs:538`); the obligation certs come from **exec**
  fns. So a bridge demo needs BOTH a proof fn (to trip the gate) and exec fns
  (to emit certs) — real corpus (tgt) has both, an exec-only fixture does not.

  Built a minimal all-green fixture (`/tmp/w4a_green.rs`: 1 tactic proof fn
  `lemma_dbl` + 3 leaf exec fns `add_capped`/`max_u64`/`double_exec`) and ran
  `verus --crate-type=lib --lean-backend --tactus-bridge` with
  `TACTUS_CORE_OUT=$PWD/tactus-core/out/lib`. Result:
  ```
  note: tactus: package gate: 4 modules elaborated (2 reused …); … kernel-verified
  note: tactus: 3 obligations bridge-checked against tactus-core (3 passed, 0 failed) [core-olean fnv1a:ac56d5f007475edd]
  verification results:: 4 verified, 0 errors
  ```
  All 3 exec certs bridge-close IN-GATE — the same `example : lib.goals_eq
  (lib.ref_wp cert_<fn>_ctx cert_<fn>_sst) cert_<fn>_goals = 1 := by decide`
  probe9 runs externally, now emitted to
  `<out>/<crate>/bridge/Bridge_<fn>.lean` and elaborated in-process. Matches
  probe9's all-close-ok. ✓

  **Acceptance checks (all pass):**
  - **Flag OFF** (`--lean-backend`, no `--tactus-bridge`): gate note present,
    NO bridge note, `4 verified, 0 errors` — byte-identical to today. ✓
  - **Flag ON, `$TACTUS_CORE_OUT` unset**: loud note `bridge skipped:
    $TACTUS_CORE_OUT unset …`, gate still `kernel-verified`, `4 verified, 0
    errors` — verdict-neutral even when the bridge can't run. ✓
  - The gate's error count is untouched by bridge outcome (bridge FAILs go to a
    LOCAL failures vec, never the gate's). W4c is what flips FAIL→error.

  Remaining before `done`: confirm the existing package-check tests still pass
  through the harness (in flight: `vargo test … test_proof_fn_package_check_smoke
  test_exec_package_check_smoke`), and add a small `["tactus-bridge"]`
  verdict-neutral regression test.

- (2026-07-14, opus-w4a) **DONE.** Harness regression clean:
  `test_proof_fn_package_check_smoke` + `test_exec_package_check_smoke` → 2
  passed, 0 failed (my config/verifier/whitelist edits don't regress the gate
  path). Added durable regression test `test_bridge_opt_in_verdict_neutral`
  (`["tactus-package-check", "tactus-bridge"]`, no `$TACTUS_CORE_OUT` in env →
  bridge SKIPS, verdict stays Ok) → 1 passed, 0 failed. Marking done; Writeup
  below. W4b/W4c remain carded in bootstrap-09.

## Writeup

**What landed.** The refWp↔production `decide` bridge — previously only in the
external probe `run.sh` scripts (probe9/probe11) — now runs INSIDE the package
gate, behind a new opt-in flag `--tactus-bridge` (OFF by default). When on, for
every emitted obligation cert `<out>/<crate>/cert/<leaf>.cert.lean` that carries
a `cert_<leaf>_goals` def, the gate writes a Bridge module
`<out>/<crate>/bridge/Bridge_<leaf>.lean` = the cert body + the exact probe line
`example : lib.goals_eq (lib.ref_wp cert_<leaf>_ctx cert_<leaf>_sst)
cert_<leaf>_goals = 1 := by decide`, and elaborates it against tactus-core's
oleans. PASS/FAIL is tallied and printed as one gate note; it never becomes a
verification error (that's W4c).

**How the code works (files):**
- `config.rs`: `--tactus-bridge` (`OPT_TACTUS_BRIDGE`, `Args.tactus_bridge`).
  It **implies `--tactus-emit-cert`** (the bridge consumes the certs), wired in
  the parse: `tactus_emit_cert = emit_cert || bridge`.
- `verifier.rs`: `generate::set_bridge_enabled(args.tactus_bridge)` beside the
  cert-emit setter; `run_package_gate` prints `report.bridge_note` in the
  success branch (note only — the failures→`count_errors` path is untouched).
- `generate.rs`: `BRIDGE_ENABLED` atomic; `PackageGateReport.bridge_note:
  Option<String>`; `run_bridge_step` (the whole bridge loop); `core_olean_hash`
  (FNV-1a over sorted `.olean` bytes in the core dir). The bridge runs at the
  END of `check_package`, only if the gate's own `failures` are empty, and
  writes to a LOCAL failures vec so it cannot perturb the gate verdict.
- `sst_serialize.rs`: `pub fn cert_ns()` exposes the `NS` (`"lib"`) constant for
  the bridge term (single source of truth for a future vendored rename).
- `common/mod.rs`: test-harness whitelist line for `"tactus-bridge"`.

**Decisions settled (the two open Qs from bootstrap-09):**
1. **Coverage = obligation certs only** for W4a (skips all-excluded fns with no
   goal section; def/dt `def_eq`/`dt_eq` certs are a W7-adjacent follow-on).
2. **tactus-core provenance = explicit `$TACTUS_CORE_OUT`** env var (matching
   `$TACTUS_PRELUDE`/`$TACTUS_CORE_VOCAB`; auto-discovery deliberately avoided as
   brittle across checkout layouts). Unset or missing
   `TactusDefs_lib_exec.olean` ⟹ the bridge SKIPS with a loud note; opt-in, so no
   default gate path breaks. The core-dir olean content-hash is recorded in the
   note now — audit trail, and the seed of W4b's cache key (a `ref_wp`/`goals_eq`
   change flips the digest, so W4b's cache can never reuse a stale PASS).

**Key finding for the next instance.** `check_package` runs only when the krate
has ≥1 **tactic proof fn** (`build_tactic_bodies_map`, `verifier.rs:538`, is
proof-mode-only). The obligation certs it bridges come from **exec** fns. So the
bridge fires on any crate that has BOTH (all real corpus, e.g. tgt) but NOT on an
exec-only crate. The done-criterion was validated on a minimal fixture carrying
one tactic proof fn plus three leaf exec fns (see Progress).

**Assumptions / partial:**
- Bridges whatever certs are on disk at gate time. Under `--lean-backend`
  caching, a cache-hit fn skips cert re-emission, so a warm run may bridge fewer
  (or stale) certs than a cold one — acceptable for opt-in W4a; W4b's content-key
  makes this precise. Cold runs (direct `verus`, no `-V cache`) emit + bridge all.
- The bridge base_path is `core_out:prelude:defs.dir` (the gate's base_path with
  core prepended); the probe used only `core_out:prelude`. The extra `defs.dir`
  is the verified crate's own namespace (never `lib`), so no shadowing of
  tactus-core's `lib.*` — confirmed by the 3/3 close on the fixture.
- Not yet run against the full tgt slice in-gate (probe11's `--verify-module
  runtime` on tactus-group-theory needs the crate-local check.sh dep setup); the
  fixture demonstration exercises the identical in-gate code path.

**Follow-ons (already carded):** W4b (bootstrap-09 staging) = content-key the
bridge modules on `literal + stmts + core-olean hash`; W4c = default-on + bridge
FAIL → error. A defs-layer (`def_eq`/`dt_eq`) in-gate bridge is the natural
coverage extension.
