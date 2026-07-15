---
title: "W4a validation — in-gate bridge over the REAL tgt corpus (DONE: 1 passed, 0 failed)"
status: done
claimed_by: opus-w4a-tgtval
created: 2026-07-14T12:40:00Z
updated: 2026-07-14T17:14:00Z
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

## Progress (cont.) — DECIDE-FLIP DIAGNOSED (opus-bootstrap43-census, 2026-07-14)

**The `0 passed, 1 failed` is NOT an olean mismatch or a decide-line diff. The
two certs are DIFFERENT CHECKS, and the in-gate one correctly flags a known
`&`-deref divergence class.** Both leads in the "next instance" list below are
red herrings — resolved by comparing the two certs directly (no heavy run):

- **probe11 external cert** (`probe-w0/probe11_w3_tgt/out/lib/cert/runtime__impl__4__clone.cert.lean`,
  Jul 13) certifies with **OPAQUE LEAVES** — `_sst = StmData.Ret (LeafList.Cons 3
  …) (RetLet 4 5)`, `_goals = GoalData.All 0 1 (GoalData.Let 4 5 (GoalData.Leaf
  3))`. That's stage-A **assembly** only; leaf 3 (`_return = self.deref`) is an
  opaque id, never expanded. probe11's `close-ok` ran `stm_size`/`goal_count`
  decides, NOT `goals_eq (ref_wp …)` over expanded leaves.
- **in-gate cert** (`/tmp/w4a-bs47b/lib/bridge/Bridge_runtime__impl__4__clone.lean`,
  Jul 14, newer binary) emits the **EXPANDED W6/W7 form** — `_sst` is a full
  `RawExp.Span 6 (RawExp.BinOp 0 TyBool (RawExp.Var 4 (TyNamed 5)) (RawExp.Var 0
  (TyRef 5)))`; `_goals = GoalData.LeafE (ExprData.SpanMark 6 (ExprData.BinOp 0
  (Atom 4) (FieldProj (Atom 0) 0)))`; the bridge decides `goals_eq (ref_wp ctx
  sst) goals` over the fully-expanded trees (line 40).

**Root cause of the fail (exact term-level divergence):**
- `ref_wp(sst)` on the BinOp RHS: `render_exp (RawExp.Var 0 (TyRef 5))` =
  `ExprData.Atom 0`. `render_exp` maps `RawExp.Var id _ty => ExprData.Atom id`
  (`tactus-core/out/lib/expr_mirror_kernel_computes.lean:65`) — it **ignores the
  type tag**; only an explicit `RawExp.Deref` node becomes a `FieldProj`.
- production `_goals` RHS: `ExprData.FieldProj (Atom 0) 0` (`self.deref` — the
  `&self`-param auto-deref).
- `Atom 0 ≠ FieldProj (Atom 0) 0` → `expr_eq = 0` → `goals_eq = 0` → decide = 0.

**Why the reference side dropped the deref (and why the emit-gate didn't catch
it):** the raw SST at that position is a bare `ExpX::Var(self)` with a `&`(Ref)
type, NOT an explicit `UnaryOpr::Field(deref)` node. Production's goal walk
(`to_lean_sst_expr`) AUTO-INSERTS the `.deref` FieldProj via `apply_deref_chain`;
`raw_exp` (`sst_serialize.rs:666`) faithfully mirrors the bare `Var` →
`RawExp.Var id (TyRef _)` (in-class, no fail-loud). The documented emit-gate that
keeps `&`-deref divergences fail-loud (`sst_serialize.rs:766-769`) fires on the
`UnaryOpr::Field` arm — but there's no Field node here, so it never trips. Net:
the reference emits an in-class ref-typed `Var`, production emits the deref,
`render_exp` (no type-driven auto-deref) preserves the split → **the bridge
CORRECTLY reports a true divergence.** It is not a false negative.

**Consequence for this card's done-criterion.** "in-gate note matches probe11's
`1 passed`" is apples-to-oranges: probe11's cert never ran the expanded leaf
check. `runtime__impl__4__clone` is a `&self`-deref clone → it lives in the
**known-divergent `&`-deref class**, so the expanded bridge will `1 failed` on it
by design until the deref gap is closed. There is NO expanded-form `1 passed` to
be had on this particular cert. (This also corrects the card's "Corpus fact":
that cert is bridgeable but NOT closeable in expanded form.)

**FORK for Danielle (recorded; her call — she offered to weigh in on the
runtime__impl failures):**
- **(A) Re-scope W4a.** Accept the in-gate expanded bridge is working correctly
  (it flags the known `&`-deref divergence), treat W4a as validated by the
  fixture (3/3 in-gate close) + this diagnosis, and for a real in-gate `1 passed`
  demo either author/find a tgt exec fn in the *coverable* class (no `&`-deref)
  or gate W4c with the `&`-deref class explicitly excluded (fail-loud, not
  silent). Lower effort; no TCB change.
- **(B) Close the deref gap** (unblocks the whole `&self`-method class, common in
  tgt `runtime`). Reproduce production's `apply_deref_chain` on the reference
  side. Two spots: (B1) `render_exp` — add `RawExp.Var id (TyRef _) => FieldProj
  (Atom id) deref_field` (type-driven, shared, mirrors the `needs_nat_coercion`
  pattern); or (B2) `raw_exp` — wrap ref-typed deref positions in `RawExp.Deref`.
  ⚠ SOUNDNESS: (B1) touches the TCB reference lowering — it asserts "a `TyRef`
  Var in value position is ALWAYS an auto-deref," which must be validated against
  positions where a `&T` var is used AS a reference (not deref'd). Needs care +
  a rebuild + a heavy in-gate re-run to confirm the decide flips to pass.

## Progress (cont.) — FIX BUILT + VALIDATED AT THE DECIDE LEVEL (opus-w4a-tgtval, 2026-07-14)

**The `&`-deref divergence is closed by a one-site transcriber fix, and I
proved it directly (no heavy run needed to confirm the term-level close). The
card's A/B fork is REFINED — the fork's B1 sketch was UNSOUND; the correct fix
site is the BinOp arm, not the Var arm.**

### Finding that corrects the fork: the deref is context-dependent (BinOp-level), not a blanket Var rule

Read production's structural-binop lowering (`to_lean_sst_expr.rs:1157-1161`):
```rust
let dl = count_ref_decorations(&*lhs.typ);
let dr = count_ref_decorations(&*rhs.typ);
let m  = dl.min(dr);
let l  = apply_deref_chain(l, dl - m);   // peel deeper operand DOWN to shallower
let r  = apply_deref_chain(r, dr - m);
```
Production **min-balances**: it peels each operand to the *common* wrapper depth,
NOT to zero. So `&T == &T` (both depth 1 → m=1 → 0 peels) is left ALONE, while
`result:T == self:&Self` (0 vs 1 → m=0 → RHS peeled once) gets one `.deref`.

⟹ The card's **B1 sketch — `RawExp.Var id (TyRef _) => FieldProj (Atom id)
deref_field`, a blanket Var-level deref — is UNSOUND**: it would deref a `&T`
operand even when compared against another `&T`, where production does not. Any
correct fix (B1 or B2) must live at the **BinOp arm** and reproduce the
min-balance from BOTH operand types. (The clone's `self.deref` is a bare
`Var(self)` peeled by the BinOp balance — NOT a `UnaryOpr::Field` node — so the
Binary arm is the exact and *sufficient* fix site; the Field-arm fail-loud at
`sst_serialize.rs:766-769` is a different scenario.)

### What I built: B2-at-BinOp (`sst_serialize.rs`, compiles clean)

`raw_exp`'s `ExpX::Binary` arm now mirrors production's min-balance, wrapping the
deeper operand in `dl-m` / `dr-m` `RawExp.Deref` nodes (new `wrap_derefs`
helper). `render_exp` (TCB) is UNCHANGED — it already maps `RawExp.Deref e =>
FieldProj (render_exp e) deref_field`. Guarded **no-op** whenever either operand
has zero ref-decorations (every non-`&` cert → `m == both → 0` peels), so it
CANNOT flip any currently-closing cert (production min-balances all structural
binops the same way, so B2's derefs == production's derefs by construction).
Binary bg-rebuilt clean (`/tmp/w4a-b2-build.log`, vstd 1530/0).

### Direct decide-level validation (no corpus rebuild)

Took the real failing in-gate bridge (`/tmp/w4a-bs47b/lib/bridge/
Bridge_runtime__impl__4__clone.lean`), made two copies, ran each against the
built tactus-core olean (`LEAN_PATH=tactus-core/out/lib:$PRELUDE`, Nix lean):
- **control** (unmodified bare `Var 0 (TyRef 5)`): `goals_eq (ref_wp ctx sst)
  goals = 1` → `decide` proves it **false**, exit 1. Reproduces `0 passed, 1
  failed`.
- **fixed** (RHS operand wrapped in `RawExp.Deref`, byte-identical to B2's
  `wrap_derefs`+`box_raw` output): **all three decides pass**, exit 0.
  `ref_wp(sst) = FieldProj (Atom 0) 0 = goals`. Divergence **CLOSED**, nothing
  hidden behind it. (Also confirms B1 would work — same `FieldProj` result.)

### Soundness read (my analysis + Danielle's local model, INDEPENDENTLY): B1 > B2

I flagged that B2 shifts the deref-count into the untrusted transcriber: since
BOTH production and `raw_exp` compute the peel via the same
`count_ref_decorations`, the bridge no longer *independently* checks the
deref-count — a bug in that helper reproduces on both sides and silent-passes
(**common-mode failure**). The local model agreed unprompted: "Inserting
`RawExp.Deref` based on type-decoration logic is *semantic lowering*, not
faithful transcription… better a slightly larger correct TCB than a smaller TCB
that validates a shared mistake. **Verdict: B1.**"

- **B1-at-BinOp** (the SOUND form, NOT the card's unsound Var sketch): extend the
  TCB `render_exp` BinOp arm to min-balance-deref from the operand types it
  ALREADY reads for nat-coercion (`type_of l`, `type_of r`). Feasible + bounded
  (TypData ref-depth is 0/1). Keeps the deref in the trusted reference where W5
  validates it and the bridge independently checks production against it. Cost:
  touches tactus-core `lib.rs` + its `expr_mirror_kernel_computes` lemmas
  (kernel re-verify); mutually EXCLUSIVE with B2 (both → double-deref).
- **B2-at-BinOp** (what I landed): TCB-clean, validated, Danielle's stage-rec.
  Narrow common-mode gap (only bugs *within* `count_ref_decorations`, and W5
  isn't done yet), so defensible for this stage.

**My recommendation: B2 now (validated, unblocks the in-gate `1 passed`), B1 as
a tracked soundness follow-up for the TCB (new card `bootstrap-48`).** This
reverses the "B2 is the end-state" read but matches Danielle's "B2 for this
stage" instinct while teeing up the principled B1. Her call on whether to
fast-track B1 — see the decision request in the response.

### Remaining step for THIS card's done-criterion

The decide-level close is proven; the full in-gate coupling (`1 obligations
bridge-checked … (1 passed, 0 failed)`) is a heavy run I launched with the B2
binary (`/tmp/w4a-b2-ingate.log`, recipe = card run #2 + `PATH` carrying Nix
lean). If it prints `(1 passed, 0 failed)` this card is DONE. Result recorded
below once it lands.

## Progress (cont.) — B1/B2 DECISION MADE + IN-GATE RUN RELAUNCHED (tracked-bg) (2026-07-14)

**Root cause of the previous cut-off (important operational fact).** The B2
in-gate run (`/tmp/w4a-b2-ingate.log`) did NOT complete: the log stops at 16:56
mid cert-emission — no package-gate note, no `verified/errors` summary, no bridge
note — ~10 min after launch, well under its 1800s timeout. That is **not** a load
or timeout death: it's the known `die-with-parent` behavior (see memory
`reference_bootstrap_hold_turn_for_long_suites`) — the bg process was killed when
the launching turn ended. So the in-gate coupling was never actually exercised
under the B2 binary yet; the last run that REACHED the gate
(`/tmp/w4a-bs47b.log`, `0 passed, 1 failed`) was the PRE-B2 binary.

**Fix: relaunched in the harness's TRACKED-background mode** (`run_in_background`,
which survives the turn and re-invokes on exit — unlike a bare `&`). Script:
`/tmp/w4a-b2-ingate3.sh` → log `/tmp/w4a-b2-ingate3.log`, out `/tmp/w4a-b2-ingate3`.
Same corrected recipe (NO `--emit-lean`, NO `-V cache`, Nix lean on PATH, B2
binary 6ea3030 built 16:46). Confirmed before launch: binary is newer than the
committed B2 source (`sst_serialize.rs` 16:45 < binary 16:46), `wrap_derefs`
present at `sst_serialize.rs:3442`, core exec olean present. Since the defs-family
chain is fully cleared (bootstrap-40..47) — proven by the pre-B2 run reaching the
gate — the only remaining question is whether the B2 binary now emits the
Deref-wrapped RHS cert and the gate reports `1 passed`. Result recorded once the
tracked run exits.

**B1-vs-B2 decision — RESOLVED: keep B2 for this stage; B1 stays tracked debt
(bootstrap-48).** Danielle recommended B2 for this stage and offered the call to
me. My independent read agrees, and settles it on three points: (1) the
common-mode gap is narrow — confined to the `count_ref_decorations` helper — and
produces **no false verifications today**; it only narrows the bridge's
*independent-check* guarantee for that one helper. (2) **W5** (the actual
soundness proof of `ref_wp`) is not done; until it is, the TCB isn't "trusted" in
the strong sense anyway, so hardening it with B1 now is premature. (3) B1 touches
tactus-core `lib.rs` + re-verifies the `expr_mirror_kernel_computes` kernel
lemmas, which **invalidates the core olean every cert imports** — a real cost that
would stall W4 validation. Net: no revert, no pivot; momentum on W4 validation.
The gap is honestly recorded in bootstrap-48 as a soundness item W5 must own (not
a nice-to-have).

## Status for the next instance

**⚠ SUPERSEDED (read the "B1/B2 DECISION MADE" progress note above first).** The
`0 passed, 1 failed` in the bootstrap47-mono update below was the **pre-B2**
binary. B2 (`6ea3030`) closes that divergence (proven at decide level); the
current in-gate confirmation run is tracked-bg `/tmp/w4a-b2-ingate3.log` (relaunch
after a die-with-parent cut-off). Everything below is retained as history.

**UPDATE 2026-07-14 (opus-bootstrap47-mono): DEFS-FAMILY BLOCKER CHAIN CLEARED —
the exec defs family now builds end-to-end and the PACKAGE GATE RUNS.** With
bootstrap-47 (m3_blinker split_q monotonicity companion) landed, a fresh run #2
(`/tmp/w4a-bs47b`, rebuilt binary) shows: m3_blinker olean built, m4_defect_flow
built, exec umbrella `TactusDefs_lib_exec.olean` built, **0 `.lean.failed`
dumps**, runtime `24 verified, 0 errors`, and — the milestone this whole chain
was for — the gate REACHES the bridge:
```
note: tactus: package gate: 12 modules elaborated (6 reused from per-fn checks);
      composition + axiom closures kernel-verified
note: tactus: 1 obligations bridge-checked against tactus-core (0 passed, 1 failed)
      [core-olean fnv1a:ac56d5f007475edd]; failed: runtime__impl__4__clone
```
**So this card's coupling is now REACHABLE, but the verdict is `0 passed, 1
failed` — NOT the expected `1 passed, 0 failed`.** The in-gate obligation bridge
for `runtime__impl__4__clone` does NOT reproduce probe11's external `close-ok`.
That is now THE remaining gap for this card (no longer a defs-build blocker).
Leads for the next instance:
- The note pins `core-olean fnv1a:ac56d5f007475edd` — check whether the
  `$TACTUS_CORE_OUT` olean the gate imported matches the one probe11 bridged
  against (a stale/mismatched tactus-core olean under the bootstrap fork would
  explain a `decide` flip). Rebuild tactus-core under the bootstrap fork if in
  doubt.
- Confirm the in-gate `decide (ref_wp … = goals)` line is byte-identical to
  probe11's external one (generate.rs:~3319 `run_bridge_step`).
- Repro recipe unchanged (drop `--emit-lean`), fresh output already at
  `/tmp/w4a-bs47b` (log `/tmp/w4a-bs47b.log`).

**(earlier) UPDATE 2026-07-14 (opus-bootstrap45-seqrung): defs chain advanced 4 modules —
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

## Progress (cont.) — ✅ DONE: `1 passed, 0 failed` on the real tgt corpus in-gate (opus-w4a-tgtval, 2026-07-14 17:14)

**The card's done-criterion is MET.** A clean foreground in-gate run with the B2
binary (6ea3030) over tgt's `runtime` module printed exactly the target note:

```
note: tactus: package gate: 12 modules elaborated (6 reused from per-fn checks);
      composition + axiom closures kernel-verified
note: tactus: 1 obligations bridge-checked against tactus-core
      (1 passed, 0 failed) [core-olean fnv1a:ac56d5f007475edd]
verification results:: 24 verified, 0 errors (partial verification with `--verify-*`)
```

- **Verdict flip confirmed as the B2 fix, not a stale olean.** The `core-olean
  fnv1a:ac56d5f007475edd` is **byte-identical** to the pre-B2 run's hash
  (bootstrap47-mono, `0 passed, 1 failed`). Same tactus-core; the only change is
  the B2 binary now emits the `RawExp.Deref`-wrapped RHS in the obligation cert,
  so the expanded `goals_eq (ref_wp ctx sst) goals = 1 := by decide` closes.
  This is the corpus-level confirmation of the decide-level close proved earlier.
- **Verdict-neutral (opt-in flag).** `24 verified, 0 errors` matches the earlier
  no-bridge baselines (bootstrap47-mono's `/tmp/w4a-bs47b.log`, and the run-#1
  `--emit-lean` run). `--tactus-bridge` only appends the note; it changes no
  verification obligation (`config.rs:829` gates only the note; the implied
  `--tactus-emit-cert` writes cert files but adds no proof burden).
- **Obligation cert present:** `runtime__impl__4__clone.cert.lean` (2667 B)
  emitted during runtime-module verification into `$TACTUS_LEAN_OUT/lib/cert/`,
  which `run_bridge_step` reads (the `.defcert.lean`/`.dtcert.lean` twins are
  correctly excluded by the `.cert.lean` suffix filter, `generate.rs:3668`).

**Operational lesson (root cause of the repeated cut-offs — for the next
instance).** Every prior in-gate coupling run died mid-flight with NO verdict
(`/tmp/w4a-b2-ingate{,3}.log` both stop mid cert-emission at 16:56 / 17:01). This
is **die-with-parent**: in the autonomous board-loop each iteration is an
*ephemeral* `claude -p …` process under a bwrap with `--die-with-parent`, so when
a turn ends EVERY descendant dies — a harness `run_in_background` task AND a bare
`&`/`nohup` alike (the previous "tracked-bg" relaunch died for exactly this
reason). **Fix that actually works: run the ~5–6 min job in the FOREGROUND,
blocking, in a single `Bash` call** (`timeout 570000`). The process then lives and
dies inside one tool call — no turn boundary to cross. This run: 17:08:12 →
17:13:39 (5m27s) at load ~7.8, `rc=0`. Recorded in memory too.

Repro (exact): fresh `TACTUS_LEAN_OUT`, `TACTUS_CORE_OUT=…/tactus-core/out/lib`,
Nix lean on PATH, then foreground:
```
verus --lean-backend --crate-type=lib …/tactus-group-theory/src/lib.rs \
      --tactus-bridge --verify-module runtime
```
(NO `--emit-lean`, NO `-V cache`.) Log: `/tmp/w4a-b2-ingate4.log` (bridge note
line 758, summary line 786).

**Follow-ups (not blockers for this card):** `bootstrap-48` tracks the B1 TCB
hardening (move the min-balance deref into the trusted `render_exp` to close the
narrow `count_ref_decorations` common-mode gap) — a W5-era soundness item, not
needed for W4a. `bootstrap-09` (W4) is the next step: bridge on by default in
package mode.

## Writeup

> ✅ **CLOSED 2026-07-14.** Done-criterion met: in-gate `1 obligations
> bridge-checked against tactus-core (1 passed, 0 failed)` on the real tgt
> corpus (see the final Progress note above). The two deliverables below (the
> `--emit-lean` recipe correction and the defs-family blocker diagnosis) remain
> accurate history; the "NOT achieved" note at the end reflects an *earlier*
> turn and is superseded by the close.

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
