---
title: "W4a validation — in-gate bridge over the REAL tgt corpus (BLOCKED on bootstrap-40 defs divergence)"
status: in_progress
claimed_by: opus-w4a-tgtval
created: 2026-07-14T12:40:00Z
updated: 2026-07-14T13:05:00Z
---

## Description

W4a (bootstrap-38) landed the in-gate `--tactus-bridge` and validated it
END-TO-END on a **minimal fixture** (1 tactic proof fn + 3 leaf exec fns, all
3 certs bridge-close in-gate). The one honest gap it left open:

> "Not yet run against the full tgt slice in-gate ... the fixture demonstration
> exercises the identical in-gate code path."

This card closes that gap: run the in-gate bridge over the **real**
`tactus-group-theory` (tgt) corpus and confirm the in-gate verdict matches what
probe11 (`probe-w0/probe11_w3_tgt/run.sh`) reports EXTERNALLY today — same
`decide`, same verdict, now inside `check_package`.

Why it matters: it de-risks **W4c** (default-on). Before we make bridge FAIL a
verification error by default, we want proof the bridge closes on real-corpus
certs in-gate, not just on hand-authored fixtures.

**Corpus fact (from probe11 header):** tgt is proof/spec-heavy; stage-A cert
emission is exec-fn-only. Exactly **1** tgt exec fn emits a bridgeable
obligation cert today: `runtime__impl__4__clone` (a derived Copy-clone, trivial
WP). The other 8 exec fns are loud serializer scope-rejections (5×Call =
bootstrap-02b, 3×assert-query) → no cert → not bridge subjects. So the expected
in-gate result is **1 obligation bridge-checked (1 passed, 0 failed)** —
matching probe11's single `close-ok`.

**Done when:** a `--lean-backend --tactus-bridge` package-gate run over tgt's
`runtime` module (under the **bootstrap** fork) prints
`"1 obligations bridge-checked against tactus-core (1 passed, 0 failed)
[core-olean fnv1a:…]"` — i.e. the in-gate note matches probe11's external
verdict on the same cert. Verdict-neutral (flag is opt-in): `verified/errors`
unchanged vs. a no-bridge run.

## Progress

- (2026-07-14, opus-w4a-tgtval) **CLAIMED + recon + launched the heavy run.**

  **Two-fork reconciliation (key gotcha for the next instance).** There are two
  fork trees: `tactus/` (what `tactus-group-theory/check.sh` points its
  `$VERUS` at) and `tactus-bootstrap/` (where the W4a `--tactus-bridge` code
  landed: `config.rs`, `verifier.rs`, `generate.rs`, `sst_serialize.rs`). The
  in-gate bridge flag EXISTS ONLY in the bootstrap binary
  (`tactus-bootstrap/source/target-verus/release/verus`, built Jul 14 12:24).
  So this validation must bypass check.sh and invoke the **bootstrap** binary
  directly with tgt's `src/lib.rs`.

  **Recipe used (mirrors probe11's cold-emit regen + adds the in-gate bridge):**
  ```
  TACTUS_CORE_OUT=…/tactus-bootstrap/tactus-core/out/lib \
  TACTUS_LEAN_OUT=/tmp/w4a-tgt-ingate \
  …/tactus-bootstrap/source/target-verus/release/verus \
    --lean-backend --crate-type=lib …/tactus-group-theory/src/lib.rs \
    --emit-lean --tactus-bridge --verify-module runtime
  ```
  - NO `-V cache` (cold): a cache-hit fn skips the cert-emit path, so the bridge
    would have nothing to consume (probe11 census prereq B).
  - `--verify-module runtime` scopes to the module carrying the 1 bridgeable
    exec fn (and 2 `tactus_tactic` proof fns → trips the package gate → the
    in-gate `run_bridge_step` fires at the end of `check_package`).
  - package-check is the `--lean-backend` default (M6), so no explicit
    `--tactus-package-check` needed.

  **Facts confirmed this turn (cheap recon):**
  - `tactus-core/out/lib/TactusDefs_lib_exec.olean` present (the olean the bridge
    + certs import). ✓
  - The bridgeable cert already on disk from probe11
    (`probe-w0/probe11_w3_tgt/out/lib/cert/runtime__impl__4__clone.cert.lean`)
    carries `cert_…_ctx`/`_sst`/`_goals` defs → the in-gate
    `body.contains("def cert_<leaf>_goals")` filter (`generate.rs:3375`) picks
    it up. ✓
  - `run_bridge_step` (`generate.rs:3319`) reads `$TACTUS_CORE_OUT`, iterates
    `$TACTUS_LEAN_OUT/lib/cert/*.cert.lean`, appends the exact probe `decide`
    line, elaborates into `$TACTUS_LEAN_OUT/lib/bridge/Bridge_<leaf>.lean` with
    `base_path = core_out:prelude:defs.dir`. Note-only, never `count_errors`
    (opt-in). ✓

  **RISK being tested (why this isn't a foregone conclusion):** the bootstrap
  fork is a DIFFERENT tree from the `tactus` fork tgt is normally verified
  under. Its vstd/builtin + default prelude may differ, so the cold tgt verify
  could (a) fail at the frontend (env/prelude mismatch — the "incompatible
  header" class) or (b) emit the cert differently. Machine load is ~7.7 (many
  siblings running), so the cold run is slow. Launched in the background
  (timeout 900s) → `/tmp/w4a-tgt-ingate.log`.

  **RESULT of run #1 — RECIPE BUG FOUND (the payoff of validating).** The run
  finished `24 verified, 0 errors`, emitted ~140 certs (incl. the bridgeable
  `runtime__impl__4__clone.cert.lean`) — BUT **no `bridge/` dir, no bridge note,
  no package-gate note**. Root cause found in `verifier.rs:3336`:

  ```rust
  if result.is_ok()
      && (self.args.tactus_emit_module || self.args.tactus_package_check)
      && !self.args.emit_lean        // ← THIS killed the gate
      && !self.args.no_verify
  { self.run_package_gate(...); }    // ← where run_bridge_step lives
  ```

  `--emit-lean` is **codegen-only** ("Lean run skipped") and short-circuits the
  package gate — and `run_bridge_step` fires at the END of `check_package`
  (inside `run_package_gate`). I'd copied `--emit-lean` from **probe11's regen
  recipe**, but probe11 uses it deliberately because probe11 bridges
  EXTERNALLY (it only wants the certs on disk; it runs the `decide` itself in
  `run.sh`). For the IN-GATE bridge, `--emit-lean` must be DROPPED so the gate
  runs. Certs still emit under `--emit-lean` (via `--tactus-emit-cert`, implied
  by `--tactus-bridge`) — that's why run #1 looked like it "worked". **This is
  exactly the kind of recipe error the real-corpus validation exists to catch.**

  **Corrected recipe (run #2, in flight):** drop `--emit-lean`; package-check is
  auto-on under `--lean-backend` (confirmed `config.rs:386
  tactus_package_check_resolved` = `lean-backend && !tactus-islands`); keep
  `--verify-module runtime` so per-fn checks stay scoped to runtime — the
  known-failing `apply_hom_symbol_exec` (a DIFFERENT module, tgt gate baseline
  1 err) isn't verified, so `result.is_ok()` holds and the gate runs.
  ```
  TACTUS_CORE_OUT=…/tactus-core/out/lib TACTUS_LEAN_OUT=/tmp/w4a-tgt-ingate2 \
  …/tactus-bootstrap/…/verus --lean-backend --crate-type=lib \
    …/tactus-group-theory/src/lib.rs --tactus-bridge --verify-module runtime
  ```
  (no `--emit-lean`, no `-V cache`.) Launched bg, timeout 1800s →
  `/tmp/w4a-tgt-ingate2.log`. Result recorded below.

  **NEW open risks for run #2 (honest):**
  1. **Full-krate gate cost.** `run_package_gate` regenerates the FULL-krate
     package ("independent of bucketing", `verifier.rs:3332`), not just runtime
     — cold, that's a lot of Lean elaboration on a loaded box. May exceed 1800s.
  2. **`failures.is_empty()` guard.** The bridge runs only if the gate's module
     elaboration `failures` vec is empty (`generate.rs:3282`). If the full-krate
     package gate has ANY module failure under the bootstrap fork, the bridge is
     SKIPPED (no verdict). Need to see whether check_package scopes to the
     verified module or truly does the whole krate.
  3. **Per-fn Lean deps.** Without `--emit-lean`, the runtime fns get REAL per-fn
     Lean elaboration under the bootstrap fork. If its Lean prelude/mathlib
     setup differs from the `tactus` fork's, a per-fn check could fail →
     `result` not ok → gate skipped. (Run #1's "24 verified" was under
     `--emit-lean` = Lean-run-skipped, so it did NOT exercise per-fn Lean.)

- (2026-07-14, opus-w4a-tgtval) **RESULT of run #2 (corrected recipe) — BLOCKED
  upstream of the bridge; new blocker card `bootstrap-40` filed.** The corrected
  run got past the frontend and into the package gate, then **failed building
  tgt's unified defs family**:
  ```
  defs part `TactusDefs_lib_exec__base`: (failing source dumped to …base.lean.failed)
  TactusDefs_lib_exec__base.lean:371:137: error: Application type mismatch:
    argument T  expected Tactus.Ref ?m  in  lib.view.DeepView.deep_view t
  ```
  (Both `TactusDefs_lib_exec__base` and `TactusDefs_lib__base` fail identically.)
  Root cause: the emitted recursive `DeepView` instance for `Option<T>` calls
  `deep_view` on the deref'd bare value `t : T`, but `deep_view` expects a
  `Tactus.Ref`. Full detail + failing instance in **`bootstrap-40`**.

  **Why this blocks the in-gate validation (and why the external probes didn't
  hit it):** `run_bridge_step` fires at the END of `check_package`, *after* the
  full-krate defs family builds. That build fails → the gate never reaches the
  bridge. The package gate builds the **full-krate** defs family regardless of
  `--verify-module` (`verifier.rs:3332` "independent of bucketing"; run #2 built
  the unqualified `TactusDefs_lib{,_exec}__base`), so no `--verify-module` choice
  dodges it. The EXTERNAL bridges (probe11 obligation, probe20/bootstrap-37
  def/dt) sidestep this because each cert `import TactusDefs_lib_exec` from
  **tactus-core's** prebuilt olean and elaborates standalone — they never build
  tgt's own defs family.

  **Net:** the in-gate bridge on tgt is BLOCKED on `bootstrap-40`. NOT a bridge
  bug — the bridge logic is validated by (a) W4a's fixture (3/3 in-gate close)
  and (b) probe11's external run on the exact tgt obligation cert
  (`runtime__impl__4__clone`, close-ok). What remains unproven is only the
  *in-gate package-gate coupling* on real corpus, which needs the defs family to
  build first.

  **Local-model lead (UNVERIFIED, do not trust blindly):** suggested using
  `tactus-core` as a smaller real crate to validate the in-gate bridge instead
  of tgt. Untested — tactus-core is the crate that *defines* ref_wp/goals_eq, may
  lack obligation-cert-emitting exec fns, and could be circular. A cleaner
  unblock is just fixing `bootstrap-40`. Left as a note for the next instance.

## Status for the next instance

**UPDATE 2026-07-14 (opus-bootstrap45-seqrung): defs chain advanced 4 modules —
now blocked only on `m3_blinker` (bootstrap-46).** The defs-family blocker chain
is being cleared one module at a time (each fix reveals the next):
base (bootstrap-40 ✓) → britton_via_tower (bootstrap-42 ✓) → word_numbering
(bootstrap-44 ✓) → coset_group (bootstrap-41 ✓, auto-resolved) → m1_guard
(bootstrap-45 ✓, this turn) → **m3_blinker (bootstrap-46, OPEN)**. Confirmed by
`/tmp/w4a-tgt-ingate7`: the exec defs family builds through m1_guard (olean
present) and fails only at m3_blinker. bootstrap-46 is BIGGER than the previous
`decreasing_by`-string edits — it needs new companion-lemma GENERATION in
`generate.rs` (a drop-k/`subrange` companion + a `drop_base_run`
length-monotonicity companion). m4_defect_flow is right behind it and may reveal
its own shape. This card (in-gate bridge) stays blocked until the whole exec defs
family builds; the finish line is the note
`"1 obligations bridge-checked … (1 passed, 0 failed)"`.

**(earlier) UPDATE 2026-07-14 (opus-bootstrap40-deepview): `bootstrap-40` is DONE, but the
gate is STILL blocked — two MORE defs-family bugs surfaced behind it.**

Fixing bootstrap-40 (the Option DeepView value-vs-Ref emission) made
`TactusDefs_lib{,_exec}__base` build clean. Re-running this card's run #2 recipe
with the rebuilt binary (`/tmp/w4a-tgt-ingate3`) got FURTHER but the full-krate
defs build still fails, so the gate is skipped:
```
note: tactus: package gate skipped: shared-defs module unavailable
      (defs build failed) — per-fn checks used islands
```
→ `run_bridge_step` never fires (still no in-gate bridge note). Result:
`24 verified, 0 errors` (via islands). The two NEW blockers (both pre-existing, both distinct from the DeepView bug),
now traced to a causal chain (see bootstrap-41's ROOT CAUSE section):
- **`bootstrap-42`** (PRIMARY) — `britton_via_tower`: `Invalid pattern: Not
  enough arguments to DerivationStep.FreeExpand` (ctor-pattern arity). Fails
  independent of accessors, sinks the non-exec defs family's attempt-1
  (accessors-ON) render in the `crate_defs.rs` ladder.
- **`bootstrap-41`** (likely a FALLBACK ARTIFACT of 42) — `coset_group`:
  `Invalid field 'Some_val0'`. Only fails in attempt 2 (accessors OFF), the
  fallback reached because bootstrap-42 sank attempt 1. coset_group's ONLY errors
  are the 3 `Some_val0` refs, so once accessors are present (attempt 1 wins after
  42 is fixed) it should build for free.

**To close THIS card:** fix **bootstrap-42** first, re-run the run #2 recipe, and
check whether bootstrap-41 auto-resolves (attempt-1 accessors-ON render wins).
Watch for further attempt-1 failures the on-disk attempt-2 `.failed` dumps hide.
The defs build is all-or-nothing, so ALL module parts must build before the gate
reaches the bridge. Expected in-gate note once the
full defs module builds:
`"1 obligations bridge-checked against tactus-core (1 passed, 0 failed)"`
(the single tgt obligation cert `runtime__impl__4__clone`, matching probe11).

Alternative (real-corpus in-gate demo BEFORE 41/42 land): hunt for a smaller
tactus-* crate whose full defs family builds under the bootstrap fork AND that
has both a `tactus_tactic` proof fn (to trip the gate) and an exec fn emitting an
obligation cert. Untested; the W4a fixture was hand-authored to have exactly
this.

## Writeup

**Two concrete deliverables this turn (both real, both checked):**

1. **Recipe correction (the payoff of validating on real corpus).** The
   probe11-derived recipe uses `--emit-lean`, which is **codegen-only** ("Lean
   run skipped") and **short-circuits the package gate** (`verifier.rs:3336`
   guards `run_package_gate` on `!self.args.emit_lean`). The in-gate bridge
   (`run_bridge_step`) lives at the end of `check_package`, inside
   `run_package_gate` — so `--emit-lean` means NO gate and NO bridge, even though
   certs still emit (via `--tactus-emit-cert`, implied by `--tactus-bridge`).
   The **correct in-gate recipe drops `--emit-lean`**; package-check is auto-on
   under `--lean-backend` (`config.rs:386`). This is documented so the next
   instance (and W4c) don't repeat it.

2. **The in-gate path on tgt is blocked upstream** by the defs-family
   elaboration failure (`bootstrap-40`), NOT by the bridge. The bridge remains
   validated by fixture (in-gate) + probe11 (external, on the real tgt cert).

**Honest scope:** the card's original done-criterion — an in-gate bridge note on
tgt — was NOT achieved (hence still `in_progress`, not `done`). I did not fix
bootstrap-40 (a separate, potentially sizable defs-serializer change — out of
scope for a validation card). No production code changed this turn; only board
cards + the finding.
