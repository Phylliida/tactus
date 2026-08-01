# HANDOFF — milestone B (b67 caching + b68 flip) — 2026-07-31

**For the next session: bootstrap-80 is COMPLETE (A7 vocab + F4 poison
derivation, both eras, plus a post-implementation review pass). What
remains per the endgame map is milestone B, then E (W8 authority
flip + trust shrink).** Everything you need is here; the ordered
program map is `DESIGN-bootstrap-endgame.md` (milestones + policy
P1–P4), the queue header is `NEXT.md`, per-brick detail is
`board/*.md`. (This file replaces the old 9k-line cumulative
HANDOFF.md — history lives in git; stage-2's session handoff is
preserved at `HANDOFF-bootstrap-80-stage2.md`.)

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`, clean tree. HEAD = `fe708cae`.
- The mirror model: `tactus-core/lib.rs` (verified BY the worktree
  binary). The trusted serializer:
  `source/lean_verify/src/sst_serialize.rs` (+ `sst_to_lean.rs`,
  `expr_shared.rs`, `to_lean_sst_expr.rs`, `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` in the verus-cad
  parent (do NOT commit there).

## State (all green at handoff)

- tactus-core gate **291/0** + package gate 54 modules + Link discharge
  **198/0-pending**.
- probe9 **33/33 CLOSE**, probe11 **11/11 tgt CLOSE** — zero
  honest-fails corpus-wide. probe13 **22 classes**, probes
  14/17/37/38 ✓, lean_verify units **428+7/0**, golden byte-stable,
  e2e **829/2** (the 2 = documented pre-existing examples pair
  flat_combine/tutorial_fifo, the standing baseline).
- probe20 **deferred** (vendored old-shape tgt defcerts; regenerate
  with the tgt-slice emit when tgt work resumes — Danielle's
  constraint: **NO full tgt gate runs**; probe11's scoped per-module
  emits are the accepted lighter path).
- Stage-2 residue: the cert path now has exactly ONE named trusted
  predicate left — the N2 `branch_isvariant_of` detector (needs a
  mirror datatype environment, W7-adjacent; the E-milestone
  trust-shrink target). The poison mark is derived reference-side
  (`poisoned_props(c)` over `FnCtxData.residue_names` + `prop_deeps`).

## Next task: milestone B (two bricks, cards exist)

### B1 = b67 (`board/bootstrap-67-w4b-cert-bridge-caching.md`) — FIRST

Cert + bridge caching (content-keyed warm-run skip) + cost numbers.
Key facts from the card:

- Reuse the M5e content-compare machinery (`render_and_build` /
  `up_to_date`) — do NOT invent a second scheme.
- Compose explicitly with `-V cache`: a Z3-cache-hit fn skips the emit
  path entirely (probe11 census prereq B). Decide + document the
  intended composition (cache-hit ⟹ unchanged cert by construction;
  the bridge cache keys on cert content).
- **The P3 emitter-fingerprint key lands here** (same code area): the
  closer/emitter BINARY version is not in the cache key today
  (documented hole, b74 card).
- Cost numbers (the justification for defaulting on): cold + warm
  wall-clock with `--tactus-bridge` on fixture and tgt
  (`--verify-module runtime` + a full-crate run) vs. without. Target:
  warm-run bridge overhead ≈ 0 on unchanged fns; flip target = gate
  wall-time within ~10% of pre-bridge warm runs.
- In-gate bridge is already VALIDATED (bootstrap-39, real tgt "1
  passed, 0 failed"). Recipe gotcha: **NO `--emit-lean`** on the
  in-gate-bridge path — it short-circuits the package gate.

### B2 = b68 (`board/bootstrap-68-w4c-bridge-default-flip.md`) — blocked by B1

Flip `--tactus-bridge` on by default in package mode; bridge failure =
verification error at the fn (census-rejected honest-fails stay
non-errors); gate note gains the standing trust-inventory line:
"N obligations bridge-checked against tactus-core, M fns
census-excluded (tags: …)". Red-path pin: one e2e test where a
deliberately perturbed cert turns the run red.

**B2 gate conditions (all four):**

1. **P2** — every honest-fail class is a fixed arm or a loud census
   tag; unclassified drift = hard error (O7 "goal drift against
   reference"). Mostly there: zero honest-fails corpus-wide today; the
   remaining known gap is the `hoist-mixed-shadow` MIX detector
   (population 0, tagged but unhit — confirm it's loud).
2. **P3** — both infra staleness holes fixed + pinned:
   (a) stmts-olean staleness (a fresh `TactusStmts_*.lean` without a
   rebuilt olean → misleading Type-mismatch/sorry cascade; fix the
   rebuild logic, pin with a regen test);
   (b) emitter-binary fingerprint in the cache key (lands with B1).
3. B1 cost story acceptable.
4. A-coverage: one full tgt acceptance run where every serializable fn
   bridges or is loudly tagged — zero unclassified failures. (Scoped
   emits for iteration per the no-tgt-gates constraint; confirm with
   Danielle how the ONE full acceptance run fits the constraint.)

## Recipes (all verified)

- tactus-core gate (from `tactus-bootstrap/`):
  `TACTUS_LEAN_OUT=$PWD/tactus-core/out ./source/target-verus/release/verus --crate-type=lib --lean-backend -V cache tactus-core/lib.rs`
  (~4 min warm, ~10 cold. Vocab/pin-statement edits: `rm -rf
  tactus-core/out` first — warm stmts oleans false-red the Link, the
  P3(a) class.)
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

## Gotchas (all bitten in the last two sessions)

- **Serialize verus invocations** — concurrent ones cause transient
  "Failed to spawn lake env lean" (memory:
  feedback_tactus_concurrent_lake_spawn).
- probe runners must GLOB `~/.cache/tactus/prelude-*` (a pinned single
  prelude dir goes stale-red).
- Nested `match` in spec fns breaks the one-line Lean emission (inner
  `_` swallows later outer arms → "redundant alternative"). Use the
  td_tag if-chain idiom (lib.rs documents it at the decide-checker
  note).
- New vocabulary variants/fields: every probe's hand-rolled match over
  the datatype needs arms or Lean fills sorryAx (probe37's axiom audit
  catches it — by design); every probe gen.py splitter that parses the
  cert literals needs its layout updated (era-2 taught this twice).
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
implementing anything non-trivial (the b80 stage-2 addendum on the
card is the model).
