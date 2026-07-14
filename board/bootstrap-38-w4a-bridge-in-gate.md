---
title: "W4a — run the kernel bridge INSIDE the package gate (opt-in --tactus-bridge)"
status: todo
claimed_by:
created: 2026-07-14T13:35:00Z
updated: 2026-07-14T13:35:00Z
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

## Writeup

_when done: findings, how the code works, assumptions made_
