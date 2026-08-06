# HANDOFF — row 11b (A6-full) COMPLETE; milestone A FULLY CLOSED — 2026-08-06

**For the next session: b81 (the ∀-binder telescope arm, endgame row
11b) is DONE — the `assert-forall` census tag is retired and milestone
A (A1–A7 coverage arms) is now FULLY CLOSED. What remains per the
endgame map: milestone F gap-work (prelude hygiene / vstd-as-package /
dual-backend differential — three independent small bricks, pick up in
gap sessions) and milestone E (W8 authority flip, b13) which is GATED
ON THE B SOAK (bridge default-on across the corpus, two weeks of active
dev, zero unclassified drift — the soak started 2026-08-03).** The
ordered program map is `DESIGN-bootstrap-endgame.md` (milestones +
policy P1–P4), the queue header is `NEXT.md`, per-brick detail is
`board/*.md`. b81's full record (design + both eras' completion notes)
is `board/bootstrap-81-a6full-forall-binder-telescope.md`.

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`. HEAD = era-1 `0f311a66` + the era-2 landing commit (see
  `git log`). The mirror model: `tactus-core/lib.rs` (verified BY the
  worktree binary). The trusted serializer:
  `source/lean_verify/src/sst_serialize.rs` (+ `sst_to_lean.rs`,
  `expr_shared.rs`, `to_lean_sst_expr.rs`, `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` in the verus-cad
  parent (do NOT commit there).

## State (all green at handoff)

- tactus-core gate **298/0** + package gate 54 modules + Link discharge
  **205/0-pending** — bridge default-on: **172 obligations
  bridge-checked** live (172 passed, 0 failed; the b67 emitter
  fingerprint invalidates correctly on every binary rebuild). Gate note
  trust-inventory line: 175 fns census-excluded (tags:
  call-unit-dest×33, rawvir-arm-pat×65, rawvir-block×4, rawvir-ctor×38,
  rawvir-dt-struct×5, rawvir-field-pat×8, rawvir-readplace-nonlocal×5,
  typ-specfn×17) — **all unmodelable-construct tags; no
  modeled-but-unmirrored tags remain** (`assert-forall` retired).
- probe9 35/35 (incl. NEW F28/F29 assert-forall subjects) + probe11
  **13/13** (incl. both `lemma_runtime_word_view_*` fns, certified and
  bridge-closed on their first live run) — zero honest-fails
  corpus-wide. probe13 **25 classes** (+3 scope-binder kills), probes
  14/17/37/38 ✓, lean_verify units **437+7/0**, golden re-vendored
  (pure @rust: line drift), e2e **829/2** (documented pre-existing
  examples pair flat_combine/tutorial_fifo).
- probe20 stays deferred (vendored old-shape tgt defcerts; no tgt
  gates — Danielle's constraint; probe11's scoped per-module emits are
  the accepted lighter path).
- The cert path's ONE named trusted predicate remains the N2
  `branch_isvariant_of` detector (the milestone-E trust-shrink
  target).

## What b81 landed (the short version)

- `StmData::DeadEnd(BinderList, ParamBoundList, body)` — the
  assert-forall skolem ∀-binders (production's `Wp::Scope` /
  `push_mod_var_frames`) transcribed by the serializer's DeadEnd arm
  (SAME `collect_assert_by_vars_in` detection, now constructive) and
  wrapped reference-side via the Loop arm's `mod_var_frames`
  (FBind + optional bound FHyp). `wp_stm_sound` absorbed the frame
  change with zero statement changes.
- `forall_bound_names` (serializer) mirrors production's
  `already_bound` dedup: DeadEnd scope binders + Loop mod-var binders
  + N2 IfCtor field binders, bundled into `branch_state`/
  `restore_branch`, restored at loop exit and DeadEnd exit.
- New model lemmas: `frame_append_fnil_right` (right identity, NOT
  definitional — `frame_append` recurses on its first arg), 4 missing
  `u_fapp_*` per-ctor unfolds, `u_mvf_nil_nil`,
  `deadend_scope_binder_pin` (the D-column field-shape pin).
- Fixture: F28 `forall_int_skolem` (Int, NoBound, mid-proposition ∀ —
  the tgt shape) + F29 `forall_u64_skolem` (u64, Bound, leading-prefix
  named-binder rendering) + `bumpi`/`bump` trigger helpers.
- probe13 classes: `scope_binder_drop` / `scope_bound_drop` /
  `scope_binder_typ_flip` (all baseline=1, kill=0).

## Next task candidates (Danielle picks)

- **Milestone F gap-work** — (1) prelude hygiene: definitionalize
  `Tactus.index`/`Tactus.hasResolved`, audit the `heightLt`
  companions; target = `arch_word_bits` pair as the only tactus axiom.
  (2) vstd-as-package: Boundary shrinks to imports; remaining vstd
  axioms become the explicit, closure-checked cross-crate trust
  surface. (3) Dual-backend differential runner: same crate through
  Verus-Z3 and tactus, fn-by-fn verdict comparison (machinery exists;
  the brick is a runner + CI-shaped report). All independent, small.
- **Milestone E (b13, W8 authority flip)** — BLOCKED on the soak
  (started 2026-08-03; two weeks of default-on dev with zero
  unclassified drift). After 11b the soak's census is cleaner than
  ever (no modeled-but-unmirrored tags).
- **Ops**: port the decreasing_by fixes (`00827513`) to
  `tactus/source` (tgt's check.sh binary carries the same bugs);
  class-3 residual (11 errors in 3 recursive proof fns) stays HELD for
  the Z3-tactic-recreation arc (Danielle 2026-08-02).

## Recipes (all verified)

- tactus-core gate (from `tactus-bootstrap/`):
  `TACTUS_LEAN_OUT=$PWD/tactus-core/out TACTUS_CORE_OUT=$PWD/tactus-core/out/lib ./source/target-verus/release/verus --crate-type=lib --lean-backend -V cache tactus-core/lib.rs`
  (~35s warm cached-bridge, ~2m live-bridge, ~10 min cold. Loudly
  skips the bridge without `TACTUS_CORE_OUT`.)
- Rebuild binary:
  `cd source && PATH="$PWD/../tools/vargo/target/release:$PATH" vargo build --release`
  (vstd 1531/0). **If vargo says "sources have changed": `cd tools/vargo && cargo build --release` first.**
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

## Gotchas (all bitten; b81 additions first)

- **Vocabulary ctor fields of list type are `Box<…>` — `box_()` the
  slot terms.** Era 1 emitted the DeadEnd list slots unboxed; EVERY
  era-1 cert was ill-typed-by-construction and no probe caught it
  because no corpus cert had a DeadEnd NODE (the 2 rejected tgt fns
  were the only DeadEnd-body subjects). The first live subject
  CLOSE-BROKE on elaboration — check elaboration separately from goal
  drift for a vocabulary arm's first subject.
- **`frame_append(f, FNil) == f` is NOT definitional** (recursion on
  the first arg) — use `frame_append_fnil_right`. And per the
  rec_1 eq-lemma gap, never let a closer `rw [lib.frame_append]`
  (hard elaboration abort, no `first |` backtracking): per-ctor
  unfolds enter VCs as HYPS via `u_fapp_*` calls; recursive lemmas
  need a custom `tactus_tactic` with the b79 termination-first
  ordering (`cases f <;> omega` before zetaDelta simp).
- **Arithmetic-only assert-forall bodies fail Verus trigger
  inference** — give `#[trigger]` a cast-free spec-fn application
  over the binder (fixture `bumpi`/`bump`). Spec-mode `+` on u64
  promotes to int.
- **Serialize verus invocations** — concurrent ones cause transient
  "Failed to spawn lake env lean" (memory:
  feedback_tactus_concurrent_lake_spawn).
- **The fixture's 11 pre-existing per-fn errors skip the package gate**
  — the in-gate bridge NEVER runs on the fixture. In-gate bridge
  subjects = green crates (tactus-core today). probe11's external
  runner is the tgt lane.
- **Hand-editing an on-disk cert does not red the bridge** — the gate
  re-emits certs from SST before bridging. The red channel is
  emission-side drift — the e2e pin uses `TACTUS_BRIDGE_PERTURB`.
- probe runners must GLOB `~/.cache/tactus/prelude-*` (a pinned single
  prelude dir goes stale-red).
- Nested `match` in spec fns breaks the one-line Lean emission (inner
  `_` swallows later outer arms → "redundant alternative"). Use the
  td_tag if-chain idiom (lib.rs documents it at the decide-checker
  note).
- New vocabulary variants/fields: every probe's hand-rolled match over
  the datatype needs arms or Lean fills sorryAx (probe37's axiom audit
  catches it — by design); every probe gen.py splitter that parses the
  cert literals needs its layout updated. probe37's
  `TactusLink_lib_exec.lean` is re-copied from the gate's pkg out —
  no manual edit.
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
implementing anything non-trivial (the b67/b80/b68/b81 addenda on the
cards are the model).
