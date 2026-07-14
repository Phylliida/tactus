---
title: "W4-prereq — make --tactus-emit-cert test-quiet (census note + eprintlns) so flag-on suite is green"
status: done
claimed_by: opus-b14
created: 2026-07-13T23:35:00Z
updated: 2026-07-14T03:40:00Z
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

- (2026-07-14, opus-b14) **Claimed. Chose the test-infra matcher approach
  (the "alternative worth weighing"), not a production quiet-switch.**
  Rationale: zero production behaviour change (flag-off is unchanged *by
  construction*), it neutralizes the actual `is_failure` trigger, it fits
  the existing precedent in `parse_diags` (which already special-cases
  `aborting due to N errors`, `failure-note`, and expansion notes), and
  cert diagnostics are verdict-neutral so the verdict-matcher is the right
  place to drop them. Bounced the A-vs-B choice off the local model — it
  concurred with A (minimize the production diff during bootstrap; save a
  real "quiet mode" for W4 UX). The dropped production knob (`--internal-
  test-mode` is consumed in `main.rs` and never reaches the `Verifier`
  args, so there is no test-mode bool to gate on) confirmed A is also the
  simpler path.

  **Change (test-infra only), `rust_verify_test/tests/common/mod.rs`
  `parse_diags`:**
  1. Right after a line parses as a JSON `Diagnostic`, and BEFORE the
     `eprintln!(diag.rendered)` + level dispatch: `if
     diag.message.starts_with("tactus: cert:") { continue; }`. Drops the
     crate-end census note (`tactus: cert: certified M/N fns`) from `notes`
     and from the test log. Applies to any level, but cert only ever emits
     a note — never an error — so it cannot mask a real error.
  2. In the non-JSON `else` branch, before `*is_failure = true`: `if
     ss.trim_start().starts_with("tactus: cert:") { continue; }`. Drops the
     per-fn `tactus: cert: <fn> not serialized: <tag>` / `write failed`
     stderr eprintlns — the actual cause of the red suite (they hit
     `[unexpected json]`).

  **Validated (subset + A/B):**
  - Flag-ON `decreases` subset (16 tests incl. exec-call/loop fns): **16
    passed / 0 failed**.
  - **A/B proof the filter is load-bearing:** reverted the harness to HEAD,
    ran the SAME subset flag-on → **12 passed / 4 FAILED**, the 4 failures
    being exactly `[unexpected json] "tactus: cert: lex_count not
    serialized: call"` / `lex3_count …: call` / `lex_loop …:
    loop-multilevel-decrease` / `forest_size …: call` / `tree_size …:
    call`. Restored my change. This also confirms N3c's root cause (the
    eprintlns, not the census note, are the `is_failure` trigger).
  - Flag-OFF `decreases` subset: **16/0** (no regression; the two new checks
    are always-false without the flag).
  - **Cert files still emitted:** ran a test with `VERUS_KEEP_TEST_DIR=1`
    flag-on; `.cert.lean` files present under
    `target/debug/test_inputs/*/tactus-lean/test_crate/cert/` (e.g. a real
    56-line `sum4.cert.lean` with leaf table + provenance). Emission code is
    completely untouched — only the matcher changed.
  - **Full flag-on suite (all 550) launched in background** for the
    definitive number (prior sessions froze mid-run; running detached).
    Result + commit to follow.

- (2026-07-14, opus-b14-cont) **Picked up the unfinished finalization.**
  The detached background run from the prior turn had died mid-suite
  (`/tmp/b14-full-flagon.log` ends at 391 `... ok`, 0 FAILED, but with **no
  `test result:` summary line** — the child test process got reaped when the
  parent session ended, `--die-with-parent`). So it was NOT a trustworthy
  green; I re-ran both suites in the **foreground** (fork vargo on PATH, well
  inside the 600s Bash ceiling — the suite is ~131s).
  - **Flag-ON** (`VERUS_EXTRA_ARGS="--tactus-emit-cert"`):
    **550 passed / 0 failed** in 130.82s (`/tmp/b14-flagon-fg.log`).
  - **Flag-OFF** (default): **550 passed / 0 failed** in 131.03s
    (`/tmp/b14-flagoff-fg.log`) — no regression, as expected (the two new
    `continue` guards are always-false without the flag).
  - **Cert emission still exercised:** ran the `test_exec*` group with
    `VERUS_KEEP_TEST_DIR=1` flag-on → **185 real `*.cert.lean` files** under
    `.../tactus-lean/test_crate/cert/`; spot-checked `add_u32.cert.lean`
    (46 lines, real leaf table + provenance header). The emission code is
    untouched by this card (git diff is `mod.rs`-only), so this just confirms
    the path runs. (Note: not every fn emits a cert — non-serializable fns
    like `use_double` hit the now-filtered `not serialized: <tag>` note and
    write nothing; that is the expected stage-A coverage gap, not a failure.)

## Writeup

**Done.** `--tactus-emit-cert` is now test-clean: the full `tactus` e2e suite
passes **550/0 with the flag on** and **550/0 with it off**, and certificate
files are still emitted (185 `*.cert.lean` across the `test_exec` group).

**Root cause.** `--tactus-emit-cert` is verdict-neutral (N3c proved 0/550
verdict changes at scale) but diagnostic-noisy. Two emission-only diagnostics
tripped Verus's exact-output test matcher:
1. the crate-end census **note** `tactus: cert: certified M/N fns`
   (`rust_verify/src/verifier.rs`, gated on `args.tactus_emit_cert` +
   non-empty census), and
2. per-fn **stderr eprintlns** `tactus: cert: <fn> not serialized: <tag>` /
   `… write failed: …` (`lean_verify/src/sst_serialize.rs`), which reach the
   harness as non-JSON lines and hit `[unexpected json]` → `is_failure = true`.
   These (not the census note) were the actual red-suite trigger.

**Fix — test-infra only** (`source/rust_verify_test/tests/common/mod.rs`,
`parse_diags`; the whole change is ~20 lines, no production code touched):
- After a line parses as a JSON `Diagnostic`, `continue` if
  `diag.message.starts_with("tactus: cert:")` — drops the census note before
  the level dispatch. (Cert only ever emits a `note`, never an `error`, so
  this can never mask a real error.)
- In the non-JSON `else` branch, `continue` if the trimmed line
  `starts_with("tactus: cert:")` **before** `*is_failure = true` — drops the
  per-fn eprintlns.

**Why this approach (A) over a production quiet-switch (B).** Flag-off
behaviour is unchanged *by construction* (both guards are false without cert
output); it neutralizes the exact `is_failure` trigger; and it fits existing
precedent in `parse_diags`, which already special-cases `aborting due to N
errors`, `failure-note`, and expansion notes. B was also strictly harder:
`--internal-test-mode` is consumed in `main.rs` and never reaches the
`Verifier` args, so there's no test-mode bool to gate these two sites on — B
would have meant plumbing a brand-new flag. Save a real user-facing "quiet
mode" for W4's UX pass.

**Load-bearing proof (from prior turn, retained).** Reverting the harness to
HEAD and re-running the same flag-on subset went 12/4, the 4 failures being
exactly the `[unexpected json] "tactus: cert: … not serialized: …"` lines.
Restoring the change → 16/0.

**Assumptions / scope.** (1) Cert diagnostics are and remain `note`-level or
plain stderr — if a future change makes cert emit a JSON **error**, this
filter would silently swallow it; that's acceptable now because cert is
verdict-neutral, but W4 (flag default-on) should revisit whether cert should
ever be able to fail a test. (2) The filter keys on the literal `tactus: cert:`
prefix; any renamed prefix must update both guards. (3) Emission is unchanged,
so this card does not certify emission *correctness* — only that it stays
green and keeps writing files.

**Feeds:** W4 (`bootstrap-09`, flag default-on under the package gate) is now
unblocked on the test-cleanliness front.
