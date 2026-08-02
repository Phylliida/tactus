# HANDOFF — milestone B2 (b68 bridge default flip) — 2026-08-02

**For the next session: milestone B1 (b67 caching) is COMPLETE, and
the tgt runtime-module gate failure it surfaced is DIAGNOSED with the
defs layer REPAIRED (`00827513`; findings doc
`FINDINGS-tgt-runtime-module-gate.md`). What remains per the endgame
map is B2 (the b68 bridge default flip), then E (W8 authority flip +
trust shrink). Open decision for Danielle: the class-3 residual (11
errors in 3 recursive proof fns — N3 script-form closer class) wants
either N3 script-author work or S2c fn-level overrides, and the
decreasing_by fixes need porting to `tactus/source`.** Everything you
need is here; the ordered program map is `DESIGN-bootstrap-endgame.md`
(milestones + policy P1–P4), the queue header is `NEXT.md`, per-brick
detail is `board/*.md`. B1's full record (design review + cost table +
findings) is `board/bootstrap-67-w4b-cert-bridge-caching.md`. (This file replaces
the milestone-B handoff; history lives in git.)

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`, clean tree. HEAD = `7b9b0cbc` (FINDINGS doc; the
  decreasing_by fixes are `00827513`).
- The mirror model: `tactus-core/lib.rs` (verified BY the worktree
  binary). The trusted serializer:
  `source/lean_verify/src/sst_serialize.rs` (+ `sst_to_lean.rs`,
  `expr_shared.rs`, `to_lean_sst_expr.rs`, `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` in the verus-cad
  parent (do NOT commit there).

## State (all green at handoff)

- tactus-core gate **291/0** + package gate 54 modules + Link discharge
  **198/0-pending** — now routinely run WITH `--tactus-bridge`:
  **166 obligations bridge-checked (166 cached warm / 166 live cold)**.
- probe9 **33/33 CLOSE**, probe11 **11/11 CLOSE** — zero honest-fails
  corpus-wide. probe13 **22 classes**, probes 14/17/37/38 ✓, lean_verify
  units **432+7/0**, golden byte-stable, e2e **829/2** (the 2 =
  documented pre-existing examples pair flat_combine/tutorial_fifo).
- probe20 **deferred** (vendored old-shape tgt defcerts; regenerate
  with the tgt-slice emit when tgt work resumes — Danielle's
  constraint: **NO full tgt gate runs**; probe11's scoped per-module
  emits are the accepted lighter path).
- The cert path has exactly ONE named trusted predicate left — the N2
  `branch_isvariant_of` detector (W7-adjacent; the E-milestone
  trust-shrink target). The poison mark is derived reference-side.

## B1 deliverables now in the tree (b67, `c1133ddb` + `3fdf6fd5`)

- Cert writers content-compare (M5e pattern): byte-identical
  re-emission keeps mtime.
- Per-cert bridge pass cache: `Bridge_<leaf>.verified` markers keyed on
  {bridge module text, `core_olean_hash`, toolchain fingerprint,
  emitter fingerprint}; island-marker discipline (removed before live
  run, written only on success). Gate note: "N obligations
  bridge-checked against tactus-core (P passed, F failed, C cached)
  [core-olean H]".
- `emitter_fingerprint()` (`lean_verify::project`): VARGO_BUILD_VERSION
  + FNV-1a of current_exe bytes. Mixed into the `-V cache` base —
  **P3(b) DONE** (a rebuilt binary no longer reuses old Z3 verdicts).
- Warm bridge overhead ≈ 1.4% (35s vs 34.7s); cold+bridge 10m35s.
  **B2 gate condition 3 (cost story) DONE.**

## Next task: B2 = b68 (`board/bootstrap-68-w4c-bridge-default-flip.md`)

Flip `--tactus-bridge` on by default in package mode; bridge failure =
verification error at the fn (census-rejected honest-fails stay
non-errors); gate note gains the standing trust-inventory line: "N
obligations bridge-checked against tactus-core, M fns census-excluded
(tags: …)". Red-path pin: one e2e test where a deliberately perturbed
cert turns the run red.

**B2 gate conditions — status:**

1. **P2** — every honest-fail class is a fixed arm or a loud census
   tag; unclassified drift = hard error (O7 "goal drift against
   reference"). Mostly there: zero honest-fails corpus-wide; the
   remaining known gap is the `hoist-mixed-shadow` MIX detector
   (population 0, tagged but unhit — confirm it's loud).
2. **P3** — (a) stmts-olean staleness (a fresh `TactusStmts_*.lean`
   without a rebuilt olean → misleading Type-mismatch/sorry cascade;
   fix the rebuild logic, pin with a regen test) — **OPEN**;
   (b) emitter-binary fingerprint in the cache key — **DONE (b67)**.
3. B1 cost story — **DONE** (~1.4% warm overhead).
4. A-coverage — **amended** (Danielle 2026-08-01): scoped tgt modules
   via the probe11 census (every serializable fn bridges or is loudly
   tagged, zero unclassified failures); the full-crate tgt acceptance
   run is REMOVED (no full tgt gates).

Design-review BEFORE implementing (the b67/b80 addendum model);
Danielle's principles 1–6 apply.

## Recipes (all verified)

- tactus-core gate (from `tactus-bootstrap/`):
  `TACTUS_LEAN_OUT=$PWD/tactus-core/out ./source/target-verus/release/verus --crate-type=lib --lean-backend -V cache tactus-core/lib.rs`
  (~35s warm, ~10 min cold. Vocab/pin-statement edits: `rm -rf
  tactus-core/out` first — warm stmts oleans false-red the Link, the
  P3(a) class.)
- tactus-core gate WITH in-gate bridge (the b67 measurement config):
  same + `TACTUS_CORE_OUT=$PWD/tactus-core/out/lib --tactus-bridge`
  (~35s warm all-cached, ~2m17s warm live-bridge, 10m35s cold).
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
  see the b67 card findings) — the in-gate bridge has no tgt subject;
  probe11's external runner is the tgt lane.
- **Hand-editing an on-disk cert does not red the bridge** — the gate
  re-emits certs from SST before bridging (content-compare writes only
  on real diffs). The red channel is emission-side drift, which flips
  marker keys by construction. B2's perturbed-cert red pin needs an
  emission-side hook, not a file edit.
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

## Danielle's standing principles

1 right-way/cleaner over faster, 2 trusted-surface shrink, 3
Lean-idiomatic, 4 transparency (generated Lean transparent from the
Rust), 5 predictability over special cases, 6 invest more work for
cleaner code. Constraints: no full tgt gates; coder agents don't
work well for implementation — do it yourself; commit freely in the
worktree (small commits per logical landing); design-review BEFORE
implementing anything non-trivial (the b67/b80 addenda on the cards
are the model).
