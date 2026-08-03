# HANDOFF — milestone B COMPLETE (b68 bridge default flip) — 2026-08-03

**For the next session: milestone B (b67 caching + b68 flip) is DONE —
the kernel bridge is default-on in package mode and milestone B closes
bootstrap-09 (W4). What remains per the endgame map: row 11b (A6-full,
the ∀-binder telescope arm that retires the `assert-forall` census
tag — now unblocked, "post-flip" per Q4), milestone F gap-work
(prelude hygiene / vstd-as-package / dual-backend differential), and
milestone E (W8 authority flip, b13) which is GATED ON THE B SOAK
(default-on across the corpus, two weeks, zero unclassified drift —
the soak started 2026-08-03).** The ordered program map is
`DESIGN-bootstrap-endgame.md` (milestones + policy P1–P4), the queue
header is `NEXT.md`, per-brick detail is `board/*.md`. B2's full
record (both design reviews + completion records + the P3(a) race
diagnosis) is `board/bootstrap-68-w4c-bridge-default-flip.md`.

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`, clean tree. HEAD = `85e7b0cd` (the flip; P2 detector
  `d6b2b367`; P3(a) race+markers `7f6dc814`).
- The mirror model: `tactus-core/lib.rs` (verified BY the worktree
  binary). The trusted serializer:
  `source/lean_verify/src/sst_serialize.rs` (+ `sst_to_lean.rs`,
  `expr_shared.rs`, `to_lean_sst_expr.rs`, `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` in the verus-cad
  parent (do NOT commit there).

## State (all green at handoff)

- tactus-core gate **291/0** + package gate 54 modules + Link discharge
  **198/0-pending** — bridge now DEFAULT-ON: **166 obligations
  bridge-checked** live (166 passed, 0 failed; 0 cached on a rebuilt
  binary — the b67 emitter fingerprint invalidates correctly; warm
  all-cached ≈ b67's 1.4%). The gate note carries the standing
  trust-inventory line: "…; 174 fns census-excluded (tags:
  call-unit-dest×32, rawvir-arm-pat×65, rawvir-block×4, rawvir-ctor×38,
  rawvir-dt-struct×5, rawvir-field-pat×8, rawvir-readplace-nonlocal×5,
  typ-specfn×17)".
- probe9 33/33 + probe11 11/11 CLOSE — zero honest-fails corpus-wide;
  the fixture's `mix_trip2` (F27) census-rejects `hoist-mixed-shadow`
  (the P2 MIX detector — implemented this session; it had never
  existed). probes 13 (22 classes)/14/17/37/38 ✓, lean_verify units
  **436+7/0**, golden byte-stable, e2e **829/2** (the 2 = documented
  pre-existing examples pair flat_combine/tutorial_fifo).
- probe20 **deferred** (vendored old-shape tgt defcerts; regenerate
  with the tgt-slice emit when tgt work resumes — Danielle's
  constraint: **NO full tgt gate runs**; probe11's scoped per-module
  emits are the accepted lighter path).
- The cert path has exactly ONE named trusted predicate left — the N2
  `branch_isvariant_of` detector (the milestone-E trust-shrink
  target). The poison mark is derived reference-side.

## B2 deliverables now in the tree

- **P3(a)**: stmts-olean staleness REPAIRED — it was a *race*:
  `stmt_partition_for`'s check-then-act memo let the 64-thread first
  wave run ~50 concurrent full-partition builds; the last insert
  carried all-false changed flags, so genuinely-changed stmt modules
  skipped olean rebuilds on ordinary warm gates (5/5 repro). F1 =
  per-key `OnceLock` build-once (memo_cell pattern); F2 =
  `<olean>.srckey` markers (FNV-1a of {`.lean` content, toolchain,
  prelude}) with island-marker discipline consulted by every skip
  path (stmt ensure, pkg cacheable ×3, gate leaf loop, driver wide
  filter); F3 = unit pins + e2e
  `test_p3a_stmts_olean_skew_forces_rebuild`. `*.srckey` gitignored.
  One-time migration: first post-flip run on an existing out-tree
  rebuilds every olean once (~2.5 min on tactus-core).
- **P2**: `mark_flet_forced` / `mark_poison_forced` reject
  `Err("hoist-mixed-shadow")` when `rename_env` is live at the forcing
  site. Validated both directions (neutered detector → cert emits and
  bridge proves goals_eq false — genuinely unbridgeable).
- **The flip**: `tactus_bridge_resolved` (config.rs) — on iff
  package-check resolves, `--tactus-no-bridge` opts out. Bridge
  failure = verification error (`cert <leaf> (goal drift against
  reference)`). Unavailability (no `$TACTUS_CORE_OUT`) = loud skip
  note, never an error. Red-path pin: `TACTUS_BRIDGE_PERTURB`
  (emission-side two-goal swap, loud, test-only) + `test_bridge_red_pin`
  (control green / perturbed red). Inert under `--emit-lean` (gate
  skipped at verifier.rs:3484).

## Next task candidates (Danielle picks)

- **Row 11b (A6-full)** — the ∀-binder telescope arm: model
  `assert forall` skolem binders in the stage-A telescope, retiring
  the `assert-forall` census tag (b68 scaffolding, never permanent).
  Card it first (step-0 evidence from the two
  `lemma_runtime_word_view_*` fns; the census population is exactly
  those 2 on tgt). Medium size.
- **Milestone F gap-work** — prelude hygiene (definitionalize
  `Tactus.index`/`Tactus.hasResolved`), vstd-as-package, dual-backend
  differential runner.
- **Milestone E (b13, W8 authority flip)** — BLOCKED on the soak:
  bridge default-on across the corpus for two weeks of active dev
  with zero unclassified drift errors (started 2026-08-03).
- **Ops**: port the decreasing_by fixes (`00827513`) to
  `tactus/source` (tgt's check.sh binary carries the same bugs);
  class-3 residual (11 errors in 3 recursive proof fns) stays HELD
  for the Z3-tactic-recreation arc (Danielle 2026-08-02).

## Recipes (all verified)

- tactus-core gate (from `tactus-bootstrap/`):
  `TACTUS_LEAN_OUT=$PWD/tactus-core/out ./source/target-verus/release/verus --crate-type=lib --lean-backend -V cache tactus-core/lib.rs`
  (~35s warm, ~10 min cold. The bridge now runs by default — loudly
  skips without `TACTUS_CORE_OUT`; add
  `TACTUS_CORE_OUT=$PWD/tactus-core/out/lib` for the live bridge,
  ~2m11s warm live-bridge.)
- Rebuild binary:
  `cd source && PATH="$PWD/../tools/vargo/target/release:$PATH" vargo build --release`
  (vstd 1531/0).
- Fixture certs:
  `rm -rf bootstrap-fixture/out && TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out ./source/target-verus/release/verus --crate-type=lib --lean-backend --emit-lean --tactus-emit-cert bootstrap-fixture/lib.rs`
  (run FROM tactus-bootstrap/ — CWD sets the `@rust:` loc prefix).
  Golden re-vendor: `cp bootstrap-fixture/out/lib/cert/add_capped.cert.lean source/lean_verify/src/testdata/add_capped.cert.lean`.
- Probes: `LEAN="$(command -v lean)" bash probe-w0/probe9_bridge/run.sh`
  (likewise probe11_w3_tgt, probe13_expr_mutations, probe14_g4_ifjoin,
  probe17_w7d_live, probe37_loop_closure, probe38_b70_b71_close).
  probe11 regen = two COLD per-module emits (`--verify-module runtime`
  / `--verify-module todd_coxeter_rt`, tgt src
  `/home/bepis/prog/verus-cad/tactus-group-theory/src/lib.rs`,
  `--emit-lean --tactus-emit-cert`, no `-V cache`, into
  `probe-w0/probe11_w3_tgt/out`, ~80s each).
- Units: `cd source && VERUS_IN_VARGO=1 cargo test --release -p lean_verify`
  (vargo rejects `-p lean_verify`).
- e2e: `cd source && vargo test -p rust_verify_test --release`
  (~15 min; expect 829/2 — the 2 = documented pre-existing
  flat_combine/tutorial_fifo).

## Gotchas (all bitten)

- **Serialize verus invocations** — concurrent ones cause transient
  "Failed to spawn lake env lean" (memory:
  feedback_tactus_concurrent_lake_spawn).
- **The fixture's 11 pre-existing per-fn errors skip the package gate**
  — the in-gate bridge NEVER runs on the fixture. In-gate bridge
  subjects = green crates (tactus-core today). tgt's runtime-module
  gate is currently RED under the worktree binary (pre-existing drift,
  see FINDINGS-tgt-runtime-module-gate.md) — the in-gate bridge has no
  tgt subject; probe11's external runner is the tgt lane.
- **Hand-editing an on-disk cert does not red the bridge** — the gate
  re-emits certs from SST before bridging. The red channel is
  emission-side drift — the e2e pin uses `TACTUS_BRIDGE_PERTURB` for
  exactly this reason.
- probe runners must GLOB `~/.cache/tactus/prelude-*` (a pinned single
  prelude dir goes stale-red).
- Nested `match` in spec fns breaks the one-line Lean emission (inner
  `_` swallows later outer arms → "redundant alternative"). Use the
  td_tag if-chain idiom (lib.rs documents it at the decide-checker
  note).
- New vocabulary variants/fields: every probe's hand-rolled match over
  the datatype needs arms or Lean fills sorryAx (probe37's axiom audit
  catches it — by design); every probe gen.py splitter that parses the
  cert literals needs its layout updated.
- After deleting fields/params, grep for the removed name in ALL
  emission format strings — a format hole + stale arg compiles fine in
  Rust but emits ill-typed Lean (the clamped_inc If-node miss).
- Do not pipe long suite output through `tail` in the launching
  command — you lose the per-binary result lines. Redirect to a file.
- The Link discharge's wf-transport resolves own-param args, NOT
  `<param>.<field>` projections — take the whole struct as the arg.
- The Link discharge's `feed_requires` assumes the threaded family's
  self-Call arg layout (currently pp-first); a new leading param means
  updating it + its unit pins.
- `by { decide }` pins can't take the threaded poison set as a free
  variable — pass `LeafList::Nil` explicitly.
- **The tactus-core out/ tree is git-tracked INCLUDING oleans** — a
  gate run can dirty `lib_exec.ladder` (run-dependent hash); revert
  it before committing unless the change is intentional.

## Danielle's standing principles

1 right-way/cleaner over faster, 2 trusted-surface shrink, 3
Lean-idiomatic, 4 transparency (generated Lean transparent from the
Rust), 5 predictability over special cases, 6 invest more work for
cleaner code. Constraints: no full tgt gates; coder agents don't
work well for implementation — do it yourself; commit freely in the
worktree (small commits per logical landing); design-review BEFORE
implementing anything non-trivial (the b67/b80/b68 addenda on the
cards are the model).
