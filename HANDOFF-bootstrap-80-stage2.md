# HANDOFF — bootstrap-80 stage 2 (poison derivation) — 2026-07-31

**For the next session: A7 scope items 1+3 are DONE and fully
validated. What remains of bootstrap-80 is scope item 2 (F4, the
poison derivation), then milestone B (b67 caching + b68 flip).**
Everything you need is here; the per-brick detail is
`board/bootstrap-80-a7-callee-signature-vocab.md` (completion record
at the bottom), the ordered program map is
`DESIGN-bootstrap-endgame.md`, the queue header is `NEXT.md`.

## Where you are

- Worktree `/home/bepis/prog/verus-cad/tactus-bootstrap`, branch
  `bootstrap`, clean tree. HEAD = `6bc3bbe1`.
- The mirror model: `tactus-core/lib.rs` (verified BY the worktree
  binary). The trusted serializer:
  `source/lean_verify/src/sst_serialize.rs` (+ `sst_to_lean.rs`,
  `expr_shared.rs`, `to_lean_sst_expr.rs`, `typed_expr.rs`).
- Memory: `memory/project_tactus_bootstrap_program.md` has the b80
  arc record (in the verus-cad parent — do NOT commit there).

## State (all green at handoff)

- tactus-core gate **286/0** + package gate 54 modules + Link
  discharge **198/0-pending**.
- probe9 **33/33 CLOSE** (zero honest-fails corpus-wide — first
  time), probe11 **11/11 tgt CLOSE**, probe13 **21 classes**,
  probe14/17/37/38 ✓, lean_verify units **428+7/0**, golden
  byte-stable, e2e **829/2** (the 2 = documented pre-existing
  examples pair flat_combine/tutorial_fifo, matches b79 baseline).
- probe20 **deferred** (vendored old-shape tgt defcerts won't
  elaborate against the new RawList; regenerate with the tgt-slice
  emit when tgt work resumes — Danielle's constraint: **NO full tgt
  gate runs**; probe11's scoped per-module emits are the accepted
  lighter path).
- A7 landing commits: `1b01cb11` (vocab), `df5c184b` (F5),
  `f22a50c9` (Assign coerce), `6e20ed39`/`0a6c7e00` (probes),
  `d61fa877`+`6bc3bbe1` (records).

## Next task: stage 2 (F4 — derive the poison mark reference-side)

Frozen design (card § "Design freeze" F4 + review addendum A3/A4):

- **FnCtxData gains two fields** (arity 7→9, ONE tactus-core edit):
  `residue_names: LeafList` (interned ids of the hoist-residue
  names — serializer `residue_names` vec, sst_serialize.rs:594,
  pushed at :1274/:1320) and `prop_deeps` — a side table mapping
  poison-relevant prop leaf ids to their `RawExp` transcriptions.
  Frames and goals are UNTOUCHED (hyp props stay opaque leaf ids
  everywhere — byte-neutrality; `wp_stm_sound` sees zero churn).
- **refWp derives on the fly** at the sites that read the bit today
  (`has_poisoned_hyp` / `forces_wrap`, and the FLetH→FLet collapse):
  `raw_exp_mentions(residues, prop_deep)` — simple recursive spec fn
  over RawExp Var atoms (name ids intern consistently by the
  atom-id invariant). Wrap-forcing = any poisoned hyp in the run;
  collapse = the let's own eq prop poisoned.
- **Impl-time checklist (A3):** enumerate EVERY `hyp_poison` call
  site — FHyp props, FLetH eq props, the cond site (`c_lx`,
  sst_serialize.rs:1104), IfCtor eq/neg props (the IfCtor poison
  BITS are the same mark — covered; the N2 `branch_isvariant_of`
  DETECTOR is a separate trusted predicate, explicitly scoped OUT —
  see card A3). Transcribe deep for exactly those props.
- **Sequencing (A4):** land table + derivation with the bit slots
  still present; refWp switches to derivation-driven assembly; green
  bridges ⟹ derivation ≡ bit on the corpus (the probe battery IS
  the cross-check). Then delete the bit slots (FHyp/FLetH/If.cond/
  IfCtor/Loop.cond — same arc), and re-point probe13 `poison_flip`
  at the derivation INPUT (overwrite residue_names with names that
  DO occur in the deep props ⟹ wrap forces ⟹ bridge flips 1→0).
- **Acceptance:** P1 contract paragraph in sst_serialize.rs header
  updated (bit no longer trusted; N2 detector paragraph stays);
  probes 9/11/13/14/17/37/38 green; units + golden; gate +
  discharge; probe13 poison_flip still flipping post-repoint.

## Recipes (verified this session)

- tactus-core gate (from `tactus-bootstrap/`):
  `TACTUS_LEAN_OUT=$PWD/tactus-core/out ./source/target-verus/release/verus --crate-type=lib --lean-backend -V cache tactus-core/lib.rs`
  (~4 min warm, ~10 cold. Vocab edits: `rm -rf tactus-core/out`
  first — warm stmts oleans false-red, P3 class.)
- Rebuild binary: `cd source && PATH="$PWD/../tools/vargo/target/release:$PATH" vargo build --release` (vstd 1531/0).
- Fixture certs: `rm -rf bootstrap-fixture/out && TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out ./source/target-verus/release/verus --crate-type=lib --lean-backend --emit-lean --tactus-emit-cert bootstrap-fixture/lib.rs`
  (run FROM tactus-bootstrap/ — CWD sets the `@rust:` loc prefix).
- Probes: `LEAN="$(command -v lean)" bash probe-w0/probe9_bridge/run.sh`
  (likewise probe11_w3_tgt, probe13_expr_mutations,
  probe14_g4_ifjoin, probe17_w7d_live, probe37_loop_closure,
  probe38_b70_b71_close). probe11 regen = two COLD per-module emits
  (`--verify-module runtime` / `--verify-module todd_coxeter_rt`,
  tgt src `/home/bepis/prog/verus-cad/tactus-group-theory/src/lib.rs`,
  `--emit-lean --tactus-emit-cert`, no `-V cache`, into
  `probe-w0/probe11_w3_tgt/out`, ~80s each).
- Units: `cd source && VERUS_IN_VARGO=1 cargo test --release -p lean_verify`
  (vargo rejects `-p lean_verify`). e2e:
  `vargo test -p rust_verify_test --release` (~15 min; expect 829/2).
- Per-goal bridge bisection idiom (invaluable this session): cert +
  probe38's `gl_nth`/`gl_nth_eq` (`lib.goal_eq`), `#reduce` both
  sides' `gl_nth … N` and textual-diff the GoalData terms.

## Gotchas (all bitten this session)

- **Nested `match` in spec fns breaks the one-line Lean emission**
  (inner `_` swallows later outer arms → "redundant alternative").
  Use the td_tag if-chain idiom (lib.rs:3161 documents exactly this).
- **Serialize verus invocations** — concurrent ones cause transient
  "Failed to spawn lake env lean" (memory:
  feedback_tactus_concurrent_lake_spawn).
- probe runners must GLOB `~/.cache/tactus/prelude-*` (probe17 was
  stale-red on a pinned single prelude dir).
- New ExprData variants: every probe's hand-rolled match over
  ExprData needs arms or Lean fills sorryAx (probe37's axiom audit
  caught it — by design).
- Do not pipe long suite output through `tail` in the launching
  command — you lose the per-binary result lines. Redirect to a file.

## Danielle's standing principles

1 right-way/cleaner over faster, 2 trusted-surface shrink, 3
Lean-idiomatic, 4 transparency (generated Lean transparent from the
Rust), 5 predictability over special cases, 6 invest more work for
cleaner code. Constraints: no full tgt gates; coder agents don't
work well for implementation — do it yourself; commit freely in the
worktree (small commits per logical landing).
