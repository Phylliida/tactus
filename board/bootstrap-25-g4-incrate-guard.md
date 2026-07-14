---
title: "G4 hardening (optional) — in-crate ref_wp decide guard for the value-if-lift + probe13 max_u64 mutation class"
status: todo
claimed_by:
created: 2026-07-14T20:45:00Z
updated: 2026-07-14T20:45:00Z
---

## Description

Two OPTIONAL hardenings split out of `bootstrap-24` (W6e) at its completion.
W6e's "Done when" is fully met and triple-validated (probe9 13/13, probe13 4/4,
probe14 green, add_capped golden-identical, `cargo test -p lean_verify --lib`
339/0). These two items add belt-and-suspenders durability but were NOT required
for W6e and each needs a tactus-core rebuild, so they get their own turn.

1. **In-crate `ref_wp`-level `decide` guard in `tactus-core/lib.rs`** (parallel
   to the existing `ref_wp_if_twoway_join` at `:2112`). Add `mx_ctx()` /
   `mx_sst()` / `mx_goals()` open-spec defs (the max_u64 branch-folded
   `Ret([impl15, impl16], RetNone)` SST + the two deep `Implies`-topped goals —
   translate them from `probe-w0/probe14_g4_ifjoin/probe14_g4_ifjoin.lean`'s
   `sst_wired` / `goals_wired`, `lib.`-prefix off, `Tactus.Box.mk X` →
   `Box::new(X)`, space-application → comma-args) and a
   `proof fn ref_wp_value_if_lift() ensures goals_eq(ref_wp(mx_ctx(), mx_sst()),
   mx_goals()) == 1, goal_count(...) == 2, <a mutation-kill flips to 0> by
   { decide }`. This pins the fix INSIDE the verified crate (checked every
   tactus-core verify), not just when the probes are run.

2. **A max_u64 If-fold mutation class in probe13** (`probe-w0/probe13_expr_mutations/`)
   now that its leaves are deep — e.g. drop the inner `let m`, or swap a branch
   value (y↔x) — proving the deep bridge flips 1→0. (probe14's part-C already
   has 6 such kills through the real `ref_wp`, so this is additive coverage in
   the mutation-harness style, not new assurance.)

**Why optional / redundant.** The render shape is already pinned in-crate by
G4.1's `expr_mirror_kernel_computes` kernel guard; the FULL `ref_wp` bridge is
pinned by the checked-in, runnable `probe14`; and `probe9` validates the real
emitted cert. So item 1 is a convenience regression-guard, item 2 is extra
coverage.

**Cost / watch.** Editing `tactus-core/lib.rs` adds a new fn → the base hash
changes → the WHOLE crate re-verifies (per the caching doc), and the emitted
`tactus-core/out/lib` oleans rebuild — so after the edit you must re-emit the
oleans and re-run probe9/13/14 (which depend on them) to confirm the chain still
holds. The `mx_*` literals are large; the safest authoring path is to write them
with a few named sub-defs in dependency order (feedback: open-spec fns must be in
dependency order for Z3 structural equality) OR one giant literal matching the
`cd19_*` style. Verify with the crate-local tactus-core check (Lean backend).

**Done when:** `tactus-core` verifies with the new guard (0 errors, clean axiom
closure); the guard's mutation-kill flips to 0; probe9/13/14 stay green against
the rebuilt oleans; probe13 gains the max_u64 If-fold class (flips 1→0).

**Blocked by:** nothing (W6e done). **Blocks:** nothing — W7 (`bootstrap-12`) is
independent.

## Progress

- (2026-07-14, opus-b30) Task created at W6e completion. The exact literals to
  translate live in `probe14_g4_ifjoin.lean` (`sst_wired`, `goals_wired`, `ctx`).

## Writeup

_when done: how the in-crate guard reads, what the mutation-kill demonstrates,
and confirmation the rebuilt oleans keep probe9/13/14 green._
