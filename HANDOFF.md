# HANDOFF — b83 (F2 explicit Boundary) COMPLETE incl. review round; two standing-convention findings surfaced + b84/b85 carded — 2026-08-06

**For the next session: b83 (milestone F, brick 2 of 3) is DONE —
card `board/bootstrap-83-f2-vstd-package.md` (step-0 probe, design
freeze, completion + review records). Every Boundary axiom now carries
a compile-enforced class (`stipulated-base` vs `proved-upstream` —
the theorem-izable debt), the Link module header prints the sorted
inventory with totals, and the package gate reports the per-class
counts (`Boundary: N (S stipulated-base, P proved-upstream)`). The
SHRINK half of vstd-as-package is carded as b84
(`board/bootstrap-84-a8-trait-assoc-projections.md`): b83's probe
found vstd's own defs emission blocked on the trait
associated-type/instance-projection coverage class (140/140 errors,
one class) — that arm is the route to theorem-izing vstd's lemma
layer. TWO STANDING-CONVENTION FINDINGS (Danielle's calls pending):
(1) the full-e2e recipe fail-fasts at the pre-existing
examples_state_machines pair — only ~31/130 test binaries ran; the
quoted "829/2" was always that PREFIX, and the tactus suite (562
tests) had not run since at least b68; (2) the tactus suite was
pre-existing RED (attribution at fb1fcba7: 397/164) on W7d-era
`dt-cert:`/`def-cert:` census lines the JSON harness filter never
learned — filter fixed (b14-class rule), suite now 560/2, and the 2
remaining reds are REAL pre-existing stmt-emission bugs
(deref-decoration on non-Ref terms: literal `7.deref`; `Int.deref`),
carded as b85 with frozen repros.** The ordered program map is
`DESIGN-bootstrap-endgame.md`, the queue header is `NEXT.md`,
per-brick detail is `board/*.md`.

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`. HEAD ≈ `39324704` (b83 review follow-through +
  harness filter fix + b85 card) + `e97cea03` (battery) +
  `bce50c13` (D1–D4) + `a74a3691` (card). The mirror model:
  `tactus-core/lib.rs` (verified BY the worktree binary). The trusted
  serializer: `source/lean_verify/src/sst_serialize.rs` (+
  `sst_to_lean.rs`, `expr_shared.rs`, `to_lean_sst_expr.rs`,
  `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` in the
  verus-cad parent (do NOT commit there) — updated through b83.

## State (all green at handoff)

- tactus-core gate **298/0** + package gate 54 modules + Link discharge
  **205/0-pending** — bridge default-on: **172 obligations
  bridge-checked** live (172 passed, 0 failed). Gate note
  trust-inventory: 175 fns census-excluded (all
  unmodelable-construct tags; no modeled-but-unmirrored tags remain).
  The gate also prints the b83 line **`Boundary: 0 cross-crate axioms
  — crate is self-contained`** (tactus-core's Boundary is empty).
- **Prelude trust surface: the `arch_word_bits` pair is the ONLY tactus
  prelude axiom** (b82). Closure-check base list = classical core +
  arch pair + ofReduceBool/trustCompiler; probe37's adequacy leaves
  rest on `[propext]` alone.
- **Cross-crate trust surface (b83): explicit and machine-counted.**
  Every Boundary axiom carries `-- trust: stipulated-base` or
  `-- trust: proved-upstream (theorem-izable debt)` at its declaration
  site, the Link module header lists the sorted inventory with totals,
  and the package gate reports per-class counts. Live non-empty
  subject: a broadcast-using crate → `Boundary: 19 (15
  stipulated-base, 4 proved-upstream)`. The `proved-upstream` count is
  the b84 arm's diff metric (target P→0 as vstd's lemma layer
  theorem-izes).
- probe9 **37/37** + probe11 **13/13** + probe13 **27 classes** +
  probes 14/17/37/38 ✓, lean_verify units **439+7/0** (b83's 2 new
  inventory pins), golden byte-stable, e2e **full-coverage (all 130
  binaries, `--no-fail-fast`): 4578/9** — the 9 = the documented
  flat_combine/tutorial_fifo pair + 5 pre-existing state_machines reds
  (Z3-route, untouched by b83; never before run in the standing
  battery) + the b85 pair (tactus suite 560/2: REAL pre-existing
  stmt-emission bugs carded as **b85** —
  `test_exec_generic_with_wrapper_instantiation_probe` and
  `test_exec_package_check_smoke`, repros frozen on the card). The
  full-e2e recipe's fail-fast means the standing "829/2" is a PREFIX —
  see the gotcha; the tactus suite must be run explicitly
  (`--test tactus`).
- probe20 stays deferred (vendored old-shape tgt defcerts; NO tgt
  gates — Danielle's constraint; probe11's scoped per-module emits
  are the accepted lighter path).
- The cert path's ONE named trusted predicate remains the N2
  `branch_isvariant_of` detector (the milestone-E trust-shrink
  target).

## What b83 landed (the short version)

- **`lean_ast::Axiom.boundary_class`** — compile-enforced at all 7
  creation sites. The classification signal: `broadcast axiom fn`
  desugars to `#[verifier::external_body] proof fn`
  (builtin_macros syntax.rs:1018-1024), so `is_external_body` splits
  stipulated-base (irreducible while vstd keeps external_body) from
  proved-upstream (vstd PROVED it; re-stipulating is debt).
- **The manifest and the machine check share one source**: both the
  Link header inventory and the `#tactus_check_axioms` whitelist
  derive from the same `defs.cmds` axiom stream — drift impossible by
  construction. lean_pp tags `-- trust:` at each declaration site.
- **Step-0 probe (the reason for the A/B split):** vstd through the
  lean-backend emit (vstd_build flag set — on the b83 card) hits 140
  errors, ALL the trait associated-type/instance-projection class
  (`unresolved V/Error/(Self := (A))/USize`). Full theorem-ization =
  b84, a milestone-A-style arm.
- **Review round:** 0/131 tactus-suite failures involved the b83
  note; classification edge cases audited (user-authored axiom fns →
  StipulatedBase stays honest); island-mode comment drift confirmed
  inert by the battery.
- **Two convention findings:** (1) full-e2e fail-fast → "829/2" is a
  prefix, tactus suite unrun since ≥b68; (2) the suite was
  pre-existing red on W7d census-line prefixes the JSON harness filter
  never learned (attribution at fb1fcba7: 397/164) — filter fixed;
  2 remaining reds are REAL bugs → b85.

## What b82 landed (the short version)

- **The three prelude "allowed, shrink over time" axioms are gone.**
  `Tactus.index` → `noncomputable def` (`if h : 0 ≤ i ∧ i.toNat < n
  then a[i.toNat]'h.2 else Classical.choice inferInstance`; the N2
  `[Nonempty α]` bracket retained — the soundness-hole pin still
  blocks the Empty exploit under the def). `Tactus.hasResolved` /
  `Tactus.heightLt` → `opaque` Prop families (unspecified-but-fixed;
  the heightLt companion audit found ZERO — no well-foundedness
  assumption, no companion facts; the SST cert path never emits it).
  Closure-check base list = classical core + `arch_word_bits` pair +
  ofReduceBool/trustCompiler. Soundness shape = model-narrowing (the
  old axiom's model class strictly contains the new declaration's
  model); no explicit `:= True` witnesses (commits to an
  interpretation — banned per the card's Q2 resolution).
- **R0: cold-prelude rebuild thread race, found by the battery and
  fixed same-day.** `build_module`'s build dir is pid-unique but the
  gate's ~64 verifier threads share one pid; the prelude-text bump
  made the whole first wave see not-fresh and race in the SAME
  `build-<pid>-TactusDefs` dir (first finisher's `remove_dir_all`
  under the others' running lean → 230 fns red). Fix: process-wide
  `REBUILD_LOCK` in `ensure_prelude_olean` + freshness re-check under
  the lock. Validated by a deliberately cold-prelude gate rerun
  (dir wiped, oleans rebuilt from scratch, zero failures).
- **D5a:** `sanity.rs`'s prelude-name extractor learned the `opaque
  NAME …` form (+ `my_opaque` form pin + a `Tactus`-head pin in
  `recognises_current_prelude`).
- **Review round verdicts:** (a) no opacity-reliant consumers
  (model-narrowing held everywhere); (b) no opaque-vs-axiom
  elaboration differences in the vstd boundary (tgt lane 13/13 is the
  empirical sweep); (c) no `expected`-list entries anywhere name the
  three symbols (subset-check semantics would make them inert anyway).
  Detection-layer lesson: run the battery COLD (prelude dir wiped) at
  least once after any prelude-text change.

## Process changes from the b81 retrospective (apply to the NEXT card)

1. **Subject matrix at CARD time, over production-behavior
   dimensions** (not vocabulary dimensions — b81's R1/R2 were the
   missing rows of {leading, past-latch} × {flat, nested} ×
   {NoBound, Bound}).
2. **Per-path state audit at card time for any construct that
   DISCARDS path state** — enumerate bound_names, forall_bound_names,
   rename_env, flet_forced, poison_forced, hyp_ordinal (per-path) vs
   emit_ordinal (global, correctly not restored). **Open audit item:**
   `let_binder_typs` is written monotonically (call-dest lets) with
   NO branch/scope restore while production's OblCtx ledger is cloned
   per path — pre-existing, unconfirmed, no corpus subject; audit it
   at the next arm that touches let-records.
3. **Era-0 subject-first for vocabulary arms** (fixture subject
   before the serializer arm; era 1 validates the rejection, era 2
   the close; first live subject probes ELABORATION separately from
   drift).
4. **Review round is in Done-when** — the post-landing skeptic review
   is 3-for-3 on real bugs (b77, b78, b81); it is where interaction
   bugs live. (b82's review found none — the battery's cold gate run
   caught R0 first; infra-concurrency bugs are the class the
   walk-path audits don't see.)
5. **Recursive proof fns copy the nearest existing one's shape
   FIRST** (attributes + u_*-unfolds-in-arm + closer string — the
   rec_1 eq-lemma gap means no `rw` on height/Box-recursive spec fns;
   see `holds_close_e_wrap` as the template and
   reference_tactus_proof_authoring_idioms).

## Next task candidates (Danielle picks)

- **b85 — the two REAL pre-existing stmt-emission bugs** (carded with
  frozen repros; deref-decoration wraps non-Ref terms: literal
  `7.deref`, `Int.deref`; tactus suite 560/2 until fixed). Found by
  b83's revived suite; arguably first — real bugs outrank tooling.
- **b84 — trait-assoc-projection coverage arm** (carded; gates
  vstd-as-package proper / the Boundary P→0 shrink). Milestone-A-style
  arm: needs card-time subject matrix + design review.
- **Milestone F brick 3 — dual-backend differential runner**: same
  crate through Verus-Z3 and tactus, fn-by-fn verdict comparison
  (machinery exists; the brick is a runner + CI-shaped report).
- **Milestone E (b13, W8 authority flip)** — BLOCKED on the soak
  (started 2026-08-03; two weeks of default-on dev with zero
  unclassified drift). The census is cleaner than ever (no
  modeled-but-unmirrored tags) and the prelude is down to the arch
  pair.
- **Ops**: port the decreasing_by fixes (`00827513`) to
  `tactus/source` (tgt's check.sh binary carries the same bugs);
  class-3 residual (11 errors in 3 recursive proof fns) stays HELD
  for the Z3-tactic-recreation arc (Danielle 2026-08-02).

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
- Per-goal bridge debugging (b81 review round recipe): copy the cert,
  append a `gl_nth` accessor + `lib.goal_eq (gl_nth N (lib.ref_wp …))
  (gl_nth N …_goals) = 1 := by decide` per goal to find WHICH goal
  diverges; then `#reduce gl_nth N …` both sides and text-diff to find
  WHERE (Box'd nodes print as `{ deref := … }`).
- Units: `cd source && VERUS_IN_VARGO=1 cargo test --release -p lean_verify`
  (vargo rejects `-p lean_verify`).
- e2e: `cd source && vargo test -p rust_verify_test --release`
  **fail-fasts at the pre-existing examples_state_machines pair —
  the quoted "829/2" is a PREFIX (~31/130 binaries)**. For the real
  battery: `vargo test -p rust_verify_test --release --test tactus`
  (the tactus pins; expect 560/2 — the b85 pair) AND periodically
  `vargo test -p rust_verify_test --release --no-fail-fast` (all 130
  binaries; ~20 min).

## Gotchas (all bitten; newest first)

- **The standing full-e2e recipe fail-fasts** —
  `vargo test -p rust_verify_test --release` stops at the FIRST red
  test binary (the pre-existing examples_state_machines pair), running
  only ~31 of 130 binaries; "829/2" was always that prefix. The
  tactus suite (562 tests, ALL the tactic/package/bridge/boundary
  pins) went unrun from ≥b68 (2026-08-03) until b83 — long enough for
  two REAL stmt-emission bugs to land invisibly (b85). Run
  `--test tactus` explicitly; `--no-fail-fast` for full coverage.
- **Cold-prelude gates are safe post-b82, but the race exists in
  EVERY older binary** — `build_module`'s build dir is pid-unique,
  not thread-unique; any pre-`902fb99b` binary rebuilding a prelude
  from scratch under a multithreaded gate can red 200+ fns with
  "failed to create file 'TactusDefs.olean'" (transient — rerun with
  the now-complete prelude dir, or use the new binary). Fixed via
  `REBUILD_LOCK` in `ensure_prelude_olean` + freshness re-check under
  the lock; validated by a deliberately cold-prelude gate rerun.
- **The `hyp_ordinal` walk counter is PER-GOAL-PATH, not global** —
  production's `split_leading_binders` numbers each goal's Hyp frames
  1-based after the base binders, so any construct that DISCARDS hyps
  from the path (DeadEnd scopes today) must restore the ordinal at
  exit (the b81 review round's real catch: latent pre-b81, surfaced
  by F30's post-scope named ∀-fact; pinned by probe13
  `scope_exit_name_drift`). The If arms already do this via
  `branch_state`; the DeadEnd arm now mirrors it.
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
implementing anything non-trivial, skeptic review AFTER landing
(both are in Done-when now); poem breaks whenever — they're part of
the work.
