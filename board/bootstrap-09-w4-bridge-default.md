---
title: "W4 — kernel bridge on by default in package mode"
status: in_progress
claimed_by: opus-w4
created: 2026-07-13T19:38:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Promote the stage-A certificate from opt-in to a standing part of the package
gate. After this, statement-STRUCTURE rendering leaves the TCB (trust-inventory
rows 2 and structurally 4).

Spec: `DESIGN-bootstrap.md` §5 (W4 row) + §2 table; `DESIGN-W2-refwp.md` §4.

- `--tactus-emit-cert` + bridge default-on under the package gate; the gate note
  gains one line: "N obligations bridge-checked against tactus-core".
- Bridge failure = verification error at the fn.
- Cache story: cert files + bridge oleans content-keyed like islands (a fn
  whose SST + goals are unchanged skips re-bridging). Needs W3's cost numbers
  to justify the default.

**Done when:** a normal `--lean-backend` package run bridge-checks every
serializable fn by default; cost is acceptable per W3's numbers; cache keeps
warm runs cheap; suite green.

**Blocked by:** bootstrap-08 (W3 — need divergences at zero and cost numbers
before defaulting on). R1 package layers already landed (M6).

## Progress

- (2026-07-14, opus-w4) **CLAIMED + blocker cleared + scoping recon done.** This
  turn = reconnaissance + a grounded staging plan; NO code landed yet (the first
  real sub-step touches the gate and is not a one-sitting change — split into
  W4a below so the next instance has a crisp entry point). Honest status:
  in_progress, plan written, implementation not started.

  **Blocker cleared.** bootstrap-08 (W3) is DONE: 0 unexplained tgt divergences
  (the one divergence is a triaged honest-fail serializer leaf gap, not a
  production/refWp bug), and cost `~1.2 s/fn` (olean-import bound, ≤ package-gate
  cost). W3's "done when" cost numbers + zero-divergence gate the default-on, so
  W4 is unblocked.

  **Where the pieces are today (code recon, bootstrap tree):**
  - **Gate entry:** `verifier.rs:3237 run_package_gate` → `lean_verify::
    check_package(krate, crate_name, tactic_bodies)` (`generate.rs:3163`). It
    builds unified defs, per-fn emits pkg proof modules + stmt modules, links,
    then **elaborates bottom-up: prelude → defs → stmts (`ensure_stmt_olean`) →
    pkg (`run_lean`) → Link**, and reports `"N modules elaborated; composition +
    axiom closures kernel-verified"` (`verifier.rs:3274`). Failures already flow
    to `self.count_errors += 1` + `error_bare` (`verifier.rs:3280-3286`) — the
    failure-as-error machinery W4 needs already exists for modules.
  - **Cert emission:** `emit_cert` / `emit_def_cert` / `emit_dt_cert`
    (`sst_serialize.rs:2782/2937/2967`), gate-flagged by `--tactus-emit-cert`
    (`config.rs:370`, `set_cert_emit_enabled` at `verifier.rs:2608`). Writes
    `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean` (+ `.defcert`/`.dtcert`)
    (`sst_serialize.rs:2819 write_cert_file`). **Emission is opt-in and
    verdict-neutral today** — it writes files, nothing bridges them in-process.
  - **The bridge itself is EXTERNAL.** The `decide` bridge
    (`example : goals_eq (ref_wp ctx sst) goals = 1 := by decide`, elaborated
    against tactus-core's `out/lib` oleans that carry `ref_wp`/`goals_eq` + mirror
    ctors) lives only in probe `run.sh` scripts (probe9, probe11_w3_tgt,
    probe17, probe20_w7_tgtslice). It is NOT part of `check_package`.

  **So W4 = promote the external bridge into a new in-gate module family**, run
  by default under the package gate, cached like stmts, failure=error, +1 report
  line. DESIGN-bootstrap.md §4.4 pins the home: per-fn Bridge modules beside
  Proofs, importing the fn's Stmts + tactus-core + the fn's literal module,
  invalidation key = `literal + stmts + tactus-core olean`.

  **Crux risk (confirmed w/ Danielle's local model):** the bridge needs
  **tactus-core's built `out/lib` oleans on the elaboration base_path**. Today
  `check_package`'s `base_path` = `prelude_dir : defs.dir` (`generate.rs:3219`);
  it has NO pointer to tactus-core's oleans. The gate must locate (or build)
  them, and the core-olean **content hash must be in the bridge cache key** (else
  a core-logic change silently reuses a stale PASS — a false negative on the
  soundness-relevant leg). This env-dependency is the whole blast radius; stage
  it so it's proven before it becomes the default failure path.

  **Staging (mirrors DESIGN §5; W4a is the crisp next actionable):**
  - **W4a** — bridge runs INSIDE the gate (opt-in `--tactus-bridge`, off by
    default): locate tactus-core `out/lib`, add it to `base_path`, emit per-fn
    Bridge modules over the SAME certs W3 bridges, elaborate them via the
    existing `ensure_stmt_olean`/`run_lean` plumbing, collect PASS/FAIL. Reuses
    the exact `decide` the probe runners use. **New card: bootstrap-38-w4a.**
  - **W4b** — caching: bridge-module content key = literal + stmts +
    tactus-core-olean hash; reuse the M5e content-compare/superset machinery
    (DESIGN §4.4 says it covers bridge modules with zero new code). Warm runs
    skip unchanged bridges. Needs W3's cost budget to justify.
  - **W4c** — default-on: flip `--tactus-bridge` on under the package gate;
    gate note gains `"N obligations bridge-checked against tactus-core"`; bridge
    FAIL → `count_errors += 1` (reuse `verifier.rs:3280` path); the crate
    axiom-closure line covers the bridge modules (core ∪ prelude ∪ tactus-core
    defs — no new axioms). Suite must stay green at acceptable cost.

  **Open questions for W4a to settle first:**
  1. **Coverage.** Stage-A emission is exec-fn-only and census-limited (W3: 1/9
     tgt exec fns emit a bridgeable obligation cert today; the other 8 are loud
     scope-rejections gated on bootstrap-02b Call + an assert-query arm). So W4
     defaulting on bridges *few* obligations on tgt until those arms land. That's
     fine (0 unexplained is the bar, not breadth) but the gate line must be
     honest: `"N obligations bridge-checked"` where N is the emitted-cert count,
     not the fn count. Defs-layer certs (W7, def_eq/dt_eq) are broader (135 on
     the symbol cone) and should be bridged too — decide in W4a whether W4
     covers obligation certs only or obligation+def+dt.
  2. **tactus-core olean provenance.** Is `out/lib` a committed/rebuilt artifact
     the gate can assume present, or must the gate build it on demand? The probe
     runners assume a prebuilt `out/lib`; the gate needs a deterministic pointer
     (env var? sibling-crate convention?). This is the plumbing W4a must nail.

## Writeup

_when done: findings, how the code works, assumptions made_

## Progress

- (2026-07-16, fable-plan) **Decomposed into cards** (board session with
  Danielle): **bootstrap-67** (W4b — cert/bridge content-keyed caching +
  cold/warm cost numbers on fixture + tgt) → **bootstrap-68** (W4c — the
  default flip, bridge failure = verification error, red-path e2e pin; closes
  this umbrella). The original blocker (bootstrap-08 W3) is done; the in-gate
  bridge is validated on real tgt (bootstrap-39). Coverage widening is tracked
  separately (bootstrap-69 assert-query, -70 call-generic, -71 ∀-path).
