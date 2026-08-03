---
title: "W4c — flip the kernel bridge on by default in package mode; close bootstrap-09"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Design review (2026-08-03, pre-implementation — the b67/b80 model)

Scope of this addendum: gate condition **P3(a)** (stmts-olean
staleness) — now DIAGNOSED end-to-end with a deterministic repro —
plus a scope correction on **P2** (the `hoist-mixed-shadow` detector
does not exist yet; the tag lives only in a doc comment). The flip
itself + red-path pin + trust-inventory line follow after these land.

### P3(a) — diagnosis (reproduced 5/5)

**Repro (deterministic).** Perturb the `seq_size_unfolds` pin
statement in tactus-core (`== 2` → `== 1 + 1`: semantically equal, so
`by { decide }` still closes), run a NORMAL warm tactus-core gate
(no interruption, no `--emit-lean`):

- `TactusStmts_lib_exec__lib__seq_size_unfolds.lean` is rewritten
  fresh (new content);
- its `.olean` is **NOT rebuilt** (stale, previous day's content);
- the gate reports **291/0 green**, package gate "kernel-verified".

strace: **zero** `lean` spawns for ANY `TactusStmts_*` module in the
whole run, while the fn's own pkg module gets its `--json -o` rebuild.
So the stale stmt olean is trusted indefinitely — the exact FINDINGS
§4 state, produced by an ordinary warm gate. The misleading Link
cascade of the original sighting needs only a downstream consumer of
the stale stmt def (seq_size_unfolds is a leaf pin, so this repro
stays quietly green instead — which is worse: silent).

**Root cause (env-gated instrumentation, `TACTUS_DEBUG_OLEAN`).**
`stmt_partition_for`'s memo is check-then-act: lookup, build, insert,
with NO build-once discipline. The verifier's per-fn worker pool (64
threads on this machine) starts ~50 package emissions concurrently;
every one of them misses the memo before the first insert. The trace
shows **~50 `build_stmt_partition` runs in ONE process**, each
re-rendering and tracked-writing ALL 26 stmt modules and computing
its own content-changed flags. The first finishers see the real diff
(`changed=true`); every later finisher sees files already fresh
(`changed=false`) — and the memo keeps the **last** insert. The
authoritative partition therefore carries `changed=false` for
genuinely-changed modules. Every downstream consumer — the per-fn
`cacheable` shortcuts, the per-fn `ensure_stmt_olean` loops, and the
crate-end gate's ensure loop — then computes
`may_skip = !ch && !defs.breaking = true`, so `ensure_stmt_olean`
takes its existence-only skip branch and the stale olean stands.

(The ~50 concurrent full-partition rewrites are also pure I/O churn:
~1300 tracked file writes per run where 26 would do.)

**Sibling cross-run hole (same acceptance criterion).** Even with the
race repaired, the skip condition is "content unchanged + olean
exists" — it cannot tell that an olean predates the `.lean` beside
it. Any run that dies (or errors) between emission and olean build
leaves exactly the skew, and the NEXT run skips the rebuild → the
misleading Type-mismatch/sorry cascade at Link, pointing everywhere
except the cause. The pkg-layer `cacheable` shortcut has the same
existence-only trust for pkg oleans (no race exposure there — one
writer per pkg file — but the same interrupt skew).

**The defs layer already solves both halves correctly**, two
different ways, both first-class idioms here: marker ordering
(`build_olean` writes the source only AFTER the olean rename
succeeds) and content-keyed sidecar markers (island `.verified`,
`Bridge_<leaf>.verified`, prelude marker).

### P3(a) — fix design (frozen)

- **F1 (race repair): per-key build-once for the stmt partition
  memo.** Swap `STMT_PARTITION_MEMO`'s check-then-act for the
  codebase's own `memo_cell` per-key `OnceLock` pattern (already used
  for `STMTS_OLEAN_MEMO` / `MUTUAL_CHECK_MEMO`): the first caller
  builds; other threads block on the `OnceLock`; every consumer
  shares the ONE build's accurate changed flags. Fail-once/warn-once
  semantics preserved (the `None` is cached inside the closure, same
  as today). No API change.
- **F2 (skew detection): content-keyed olean freshness markers**
  (island/bridge-marker discipline):
  - After a successful stmt olean build, write
    `TactusStmts_<…>.olean.srckey` = FNV-1a of {module `.lean`
    content, `toolchain_fingerprint()`, prelude fingerprint}; the
    marker is REMOVED before any live build and written only on
    success (a crash leaves no stale trust). `ensure_stmt_olean`'s
    skip branch becomes "olean exists AND srckey matches the current
    `.lean` content" instead of bare existence. `defs.breaking`
    stays as the defs-side condition (append-only defs rebuilds
    remain skippable, per the M5e design).
  - Same for pkg oleans: `pkg/<leaf>.olean.srckey` keyed on the pkg
    `.lean` content + toolchain/prelude; the `cacheable` check
    consults it in place of bare `olean.exists()`.
  - The driver "wide" snapshot filter (existence-only today) consults
    the stmt srckey — the driver is opt-in, but the filter must not
    reintroduce the hole for `TACTUS_DRIVER=1` runs.
- **F3 (pins):**
  - F1 unit pin (lean_verify): call `stmt_partition_for` concurrently
    from N threads, count `build_stmt_partition` invocations
    (instrumented via a test hook) — exactly 1, all threads share the
    result. Deterministic (does not rely on winning a race).
  - F2 regen pin (lean_verify or e2e, whichever is cheaper in-harness):
    hand-craft the skew — fresh `TactusStmts_*.lean` + stale/absent
    srckey — then assert the gate/olean-ensure REBUILDS (marker
    mismatch forces a live build) and writes a matching marker.
    Pre-fix behavior: skipped (existence-only trust).

**Sequencing:** F1+F2+F3 in one landing (same two functions, one
review unit), then P2 (below), then the flip + trust-inventory line
+ red-path pin.

**Not taken (considered):** defs-style marker ordering for stmts/pkg
(write the `.lean` only after the olean succeeds). It would require
restructuring emission (pending-file writes, build-dir elaboration)
and breaks the pkg failure path, whose `--json` span-mapped
diagnostics read the canonical `.lean`. The sidecar marker achieves
the same invariant without touching the write architecture. An
mtime-based check rejected for the same reason the codebase moved to
content keys everywhere (cp/touch fragility; b67 D3's precedent).

### P2 — scope correction: the `hoist-mixed-shadow` detector is ABSENT

The handoff/endgame notes describe it as "tagged but unhit — confirm
it's loud". Grep says otherwise: the string `hoist-mixed-shadow`
occurs exactly once in the tree, in the `bound_names` doc comment
(sst_serialize.rs) — there is NO detection site. A user hitting the
MIX case today (shadow freshening while wrap-free, wrap-forcer later
on the same walk path) gets an **unclassified bridge mismatch** — a
hard error under the flip (O7), not a named census tag. P2 therefore
requires IMPLEMENTING the detector, not just confirming it:

- **D1:** at the two wrap-forcing sites (`flet_forced` /
  `poison_forced` assignments in sst_serialize.rs), if `rename_env`
  is non-empty (a freshened shadow is live on this path), reject
  `Err("hoist-mixed-shadow")` — the census counts it loud instead of
  a bridge drift. Coarse-but-predictable (rejects even if the
  freshened name never reaches a later goal); per-If-branch snapshot
  discipline is already how these flags behave. Corpus census stays
  0 (nothing regresses).
- **D2:** a synthetic fixture fn that forces the MIX shape, pinned to
  census-reject with the tag (loudness pin), plus the tag added to the
  b68 card's closed tag table.

Both are pre-flip gate conditions (P2 + P3), so the landing order is:
**P3(a) F1–F3 → P2 D1–D2 → flip + trust-inventory line + red-path
pin** (each its own commit, battery green per landing).

## Completion record — P3(a) + P2 (2026-08-03)

**P3(a) LANDED (F1–F3).** F1: `stmt_partition_for` moved to the
per-key `OnceLock` `memo_cell` pattern — build-once per scope per
process; first-wave workers block instead of racing ~50 full-partition
builds whose last insert carried all-`false` changed flags. F2:
`<olean>.srckey` markers (FNV-1a of {`.lean` content, toolchain fp,
prelude dir}) with island-marker discipline (removed before a live
build, written only on success); `ensure_stmt_olean`'s skip, both pkg
`cacheable` checks, the Mutual path, the gate's pkg leaf loop, and the
driver "wide" snapshot filter all consult `olean_fresh` instead of
bare existence. F3: pins — `stmt_partition_builds_once_under_concurrency`
(8 threads, one shared Arc), `olean_srckey_freshness_contract` +
`olean_srckey_components` (lean_verify units), and e2e
`test_p3a_stmts_olean_skew_forces_rebuild` (manufactures the fresh-
`.lean`/stale-olean skew with the exact v2 render so the partition
sees no change; pre-fix the olean is never rebuilt, post-fix the
srckey mismatch forces it). `*.srckey` gitignored in tactus-core (local
freshness cache; oleans stay the tracked artifact). **Validated:**
migration run (no markers anywhere) rebuilt all oleans once, 2m31s,
green; next warm run 35.2s ≡ pre-fix baseline, 0 oleans rebuilt, 224
pkg cached; a statement perturbation now rebuilds exactly the affected
stmt olean + marker (pre-fix: never). One-time migration cost stands
for every existing out-tree (first run rebuilds everything, writes
markers).

**P2 LANDED (D1–D2).** The detector did not exist — implemented per
the addendum: `mark_flet_forced` / `mark_poison_forced` reject
`Err("hoist-mixed-shadow")` when `rename_env` is live at the forcing
site (18 call sites now `?`-propagate; both init sites have empty
`rename_env` by construction). Validated BOTH directions on
`mix_trip2` (rebind a taken name while wrap-free, Bool residue, then
`assert(b)` forcing wrap later on the path): detector ON →
`not serialized: hoist-mixed-shadow`, census counts it, fn still
verifies; detector NEUTERED (temporary experiment binary) → cert
emits and the bridge proves `goals_eq … = 1` FALSE — the class is
genuinely unbridgeable, so the rejection is sound, not a false
positive. Permanent tripwire: fixture F27 `mix_trip2` emits no cert
(census shows `1 hoist-mixed-shadow`); if the detector breaks, a
non-closing cert appears and probe9 goes red CLOSE-BROKE. Unit pin
`hoist_mixed_shadow_detected`. D2's planned fixture-census pin is
realized by the probe9 tripwire rather than a census-line assertion
(nothing in the tree pins census lines today; the CLOSE-BROKE channel
is the standing one).

**Battery (both landings):** units 436+7/0; tactus-core gate 291/0 +
54 + Link discharge 198/0 (repeated across migration/warm/perturbation
runs); e2e 829/2 (documented pre-existing pair); probes
9/11/13/14/17/37/38 ✓; fixture golden byte-stable.

**Remaining for the flip itself:** the `--tactus-bridge` default flip
(bridge failure = verification error), the trust-inventory gate line,
and the red-path e2e pin (emission-side hook — hand-editing an on-disk
cert does not red the bridge, per the b67 finding).

## Design review — the flip itself (2026-08-03, pre-implementation)

Survey of the flip surface (all line-anchored during the P3(a) work):

- `config.rs`: `tactus_bridge: matches.opt_present(OPT_TACTUS_BRIDGE)`;
  `tactus_emit_cert` already folds in `|| OPT_TACTUS_BRIDGE` (the
  bridge consumes certs). Package check is default under
  `--lean-backend` (`tactus_package_check_resolved`).
- `verifier.rs::run_package_gate`: `report.failures` non-empty → one
  verification error per (module, output) — the error channel the
  bridge failure must join. The `bridge_note` prints as a bare note.
- `generate.rs::check_package`: the bridge runs only when
  `failures.is_empty()` (no piling onto a red gate — keep).
- `generate.rs::run_bridge_step`: returns the one-line note; per-cert
  pass/cached/fail counted, `local_failures` (lean output) currently
  discarded. The W4b content-keyed pass cache makes cached PASSes
  sound by construction.

### Frozen design

1. **Default rule.** Bridge on iff `tactus_package_check_resolved` AND
   NOT `--tactus-no-bridge` (new opt-out flag, for dev loops).
   `--tactus-bridge` stays accepted (compat; now the default).
   `tactus_emit_cert` resolution folds in the resolved bridge bit
   (bridge consumes certs). `--emit-lean` runs never reach the gate,
   so probe11/fixture emit recipes are inert to the flip.
2. **Failure channel.** `run_bridge_step` returns a structured
   `BridgeStep { checked, passed, cached, failed: Vec<(leaf, output)>,
   note }` — lean output captured per failing leaf (today discarded).
   `check_package` appends each `(leaf, output)` to
   `PackageGateReport.failures` with the O7 wording ("goal drift
   against reference"), so verifier.rs's existing failures loop turns
   each into a verification error attributed at the fn. Census-
   rejected fns emit no cert → never bridge subjects (mix_trip2 et
   al. stay non-errors, per policy P2). A write-failure of the bridge
   module itself also enters `failed` (io, with its message).
3. **Unavailability ≠ failure.** No `TACTUS_CORE_OUT` / missing core
   oleans stays a loud skip NOTE (wording updated: no longer
   "opt-in…"), never an error — otherwise every e2e package test and
   every no-core user run reds. This is the one non-error bridge
   outcome post-flip; it is loud and it names the remedy.
4. **Trust-inventory line.** The gate note's bridge segment becomes
   the standing line: "N obligations bridge-checked against tactus-core
   (P passed, F failed, C cached) [core-olean H]; M fns census-excluded
   (tags: tag×n, …)" — M and the tags from the cert census
   (`CERT_REJECTIONS`, compact one-line form via a new
   `census_excluded_summary()` in sst_serialize). Printed only when the
   bridge actually ran (not on skip).
5. **Red-path pin.** New env knob `TACTUS_BRIDGE_PERTURB=<substring>`,
   checked at the goals-assembly site in `sst_serialize::emit_cert`:
   for fns whose leaf name contains the substring, swap the first two
   goals of the emitted `cert_<leaf>_goals` (fn must have ≥2 goals —
   the pin uses an assert + postcondition). Emission-side by
   construction (re-emission overwrites on-disk edits — the b67
   gotcha), deterministic, and loud (`eprintln` when the knob is set,
   documented test-only). The e2e test runs a green package crate with
   the knob set → expects failure with the O7 error naming the fn;
   the same crate with the knob unset stays green.
6. **Existing test update.** `test_bridge_opt_in_verdict_neutral`
   becomes the default-on coverage: bridge runs by default, loudly
   skips without core oleans, verdict still neutral; a second test
   pins `--tactus-no-bridge` restoring the pre-flip surface (no bridge
   note at all).

**Decisions taken under principles 1–6 (flag if you disagree):**
opt-out flag name `--tactus-no-bridge` (mirrors existing `--no-*`
negations); the perturb knob is an env var, not a flag (matches the
`TACTUS_*` knob convention; a test-only hook shouldn't widen the
public CLI surface); unavailability-stays-a-note (predictability: a
missing optional dependency must not red otherwise-green runs).

**Not taken:** surfacing bridge failures at per-fn check time (the
bridge is a crate-end gate artifact — certs only exist crate-wide
there; per-fn surfacing would need a second bridge run); making the
pass cache failure-aware (the content key already covers every input
to the verdict — a cached PASS is sound, and failures are never
cached).

## Completion record — the flip (2026-08-03)

All six design points landed as frozen, no deviations:

1. **Default rule** — `tactus_bridge_resolved` (config.rs): on iff
   package-check resolves, off via `--tactus-no-bridge`;
   `--tactus-bridge` stays accepted. Cert emission follows the
   resolved bit. Confirmed inert under `--emit-lean` (the gate is
   skipped at verifier.rs:3484 — fixture/probe11 recipes untouched).
2. **Failure channel** — `BridgeStep { note, failed }`;
   `run_bridge_step` captures lean output per failing leaf;
   `check_package` maps each to `cert <leaf> (goal drift against
   reference)` in `PackageGateReport.failures` → verification errors
   via the existing verifier.rs loop.
3. **Unavailability ≠ failure** — skip notes updated (no more
   "opt-in" wording); pinned by `test_bridge_default_on_skip_note`.
4. **Trust-inventory line** — live on tactus-core: "166 obligations
   bridge-checked against tactus-core (166 passed, 0 failed, 0 cached)
   [core-olean fnv1a:…]; 174 fns census-excluded (tags:
   call-unit-dest×32, rawvir-arm-pat×65, rawvir-block×4,
   rawvir-ctor×38, rawvir-dt-struct×5, rawvir-field-pat×8,
   rawvir-readplace-nonlocal×5, typ-specfn×17)".
5. **Red-path pin** — `TACTUS_BRIDGE_PERTURB=<substring>` swaps the
   first two goals at `goal_list` (loud eprintln when matched);
   `test_bridge_red_pin` drives it against the repo's tracked
   tactus-core oleans: control run green with the live bridge
   (1 passed, 0 failed), perturbed run red with the O7 error naming
   `red_pin_drift`. Harness gained `run_verus_with_env` (per-child
   env; the process-global env is not parallel-test-safe).
6. **Test updates** — `test_bridge_opt_in_verdict_neutral` replaced by
   `test_bridge_default_on_skip_note` + `test_bridge_no_bridge_opt_out`
   (stderr-pinned); the P3(a) regen pin landed earlier in the file.

**Battery:** units 436+7/0; tactus-core gate WITH default-on bridge
291/0 + 54 + 198/0-pending, 166 obligations bridge-checked live
(0 cached — emitter-fingerprint invalidation from the rebuild, the
b67 mechanism working as designed), 2m11s; e2e 829/2 (+3 new tests
green); probes 9/11/13/14/17/37/38 ✓; fixture golden byte-stable.

**B2 gate conditions — final status:** P2 (detector implemented +
pinned, corpus population 0) ✓; P3(a) (race repair + srckey markers +
pins) ✓; P3(b) (emitter fingerprint, b67) ✓; cost story (~1.4% warm,
b67) ✓; A-coverage (scoped probe11 census, all classified) ✓.
**Milestone B (b67+b68) is DONE.** bootstrap-09 (W4) closes with this
card. Next per the endgame: milestone E (W8 authority flip + trust
shrink — the N2 `branch_isvariant_of` detector is the last named
trusted predicate on the cert path).

## Description

The W4 default flip itself (umbrella bootstrap-09), once bootstrap-67's cache +
cost story justifies it:

- Bridge on by default under the package gate (`--lean-backend` package mode);
  an opt-out flag for dev loops if the numbers say one is needed.
- **Bridge failure = verification error at the fn** (today it is note-only /
  opt-in). Honest-fails (census-rejected shapes) remain non-errors — they emit
  no cert and are not bridge subjects; only a cert that exists and fails to
  close errors.
- Gate note gains the standing line: "N obligations bridge-checked against
  tactus-core (…)".
- Suite: pin at least one e2e test where a deliberately perturbed cert turns
  the run red (the mutation-kill discipline, in-harness).

**Done when:** a plain `--lean-backend` package run bridge-checks every
serializable fn by default; failure is a verification error; suite green
(including the red-path pin); bootstrap-09 closed with writeup.
A-coverage is confirmed on the SCOPED tgt modules (probe11 census:
every serializable fn bridges or is loudly tagged, zero unclassified
failures) — Danielle 2026-08-01 removed the one full-crate tgt
acceptance run (no full tgt gates; scoped per-module emits are the
accepted path).

**Blocked by:** bootstrap-67.
