---
title: "W4-prereq — make --tactus-emit-cert test-quiet (census note + eprintlns) so flag-on suite is green"
status: todo
claimed_by:
created: 2026-07-13T23:35:00Z
updated: 2026-07-13T23:35:00Z
---

## Description

`--tactus-emit-cert` is **verdict-neutral** (proven at 550-fn scale during
N3c: 0/550 verdict changes) but **diagnostic-noisy**. Running the full e2e
suite with the flag on goes red 380/170 — NOT from any verification
regression (every failure is `expected Ok(()) but got Err(no errors)`, i.e.
the fn still verifies) but because Verus's exact-output test matcher rejects
two emission-only diagnostics:

1. the crate-end census **note** — `note: tactus: cert: certified M/N fns`
   (`rust_verify/src/verifier.rs` ~3335, gated only on `args.tactus_emit_cert`
   + non-empty census);
2. per-fn **eprintlns** — `tactus: cert: <fn> not serialized: <tag>` and
   `tactus: cert: <fn> write failed: …` (`lean_verify/src/sst_serialize.rs`
   ~698/703), which land in the harness's parsed stream as `[unexpected json]`.

W4 wants the flag **default-on** under the package gate, so the flag must be
test-clean before then. This is that cleanup.

**Approach (decide at kickoff):**
- Thread a quiet switch to both sites. `--internal-test-mode` is NOT currently
  plumbed into `verifier.rs`/`sst_serialize.rs` (it's handled at the driver
  level), so either (a) add a dedicated `--tactus-cert-quiet` arg that
  `rust_verify_test/tests/common/mod.rs` sets alongside `--internal-test-mode`,
  or (b) plumb the existing test-mode bool down to these two sites.
- Suppress the **diagnostics only** — keep the cert **file writes** so the
  emission path is still exercised under test.
- Alternative worth weighing: teach the harness's output matcher to ignore
  `tactus: cert:`-prefixed lines (test-infra change, no production touch).

**Done when:** `VERUS_EXTRA_ARGS="--tactus-emit-cert" vargo test -p
rust_verify_test --test tactus` is **550/0**, with cert files still emitted
(spot-check a few under `target/debug/test_inputs/*/tactus-lean/`), and the
flag-off suite unchanged at 550/0.

**Blocked by:** nothing (independent cleanup). **Feeds:** W4
(`bootstrap-09`, flag default-on).

## Progress

- (2026-07-13, opus-n3c) Filed. Root-caused during N3c §7.4 acceptance: the
  first-ever full flag-on run (prior sessions never completed one — the
  DESIGN-N3 "green flag-on" line was aspirational and has been corrected).
  All 170 flag-on failures are verdict-preserving; see N3c writeup
  (`bootstrap-04`) and DESIGN-N3 Status line.

## Writeup

_when done_
