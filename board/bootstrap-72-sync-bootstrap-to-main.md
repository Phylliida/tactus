---
title: "sync — merge bootstrap branch → tactus main (W5/W6/W7 + serializer fixes; incl. the W7 typ_data fix)"
status: in_progress
claimed_by: fable-mainline
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T19:05:00Z
---

## Description

Everything since the 2026-07-12 merge (`f2f80a0`) lives only on the `bootstrap`
branch / worktree: the W5 probe ladder, W6/W7 certificates, the Call arm, the
in-gate bridge, and notably the **W7 `typ_data` faithfulness fix**
(`sst_serialize.rs:588`, usize/char → TyNat) — while `tactus/source` (the tree
`tactus-group-theory/check.sh` points at) is behind. A stale main means tgt's
daily verification binary lacks the serializer fixes and the bridge.

**Timing is Danielle's call** — this card records the checklist so the merge
is mechanical when she says go:

- Merge `main` → `bootstrap` first if main has moved (last sync `8abdcf7` was
  clean); resolve, battery, then proper 2-parent merge `bootstrap` → `main`
  (the f2f80a0 pattern, backup tag first).
- Known gotcha: `vargo` runs `git` internally and can clear `MERGE_HEAD`
  mid-merge — don't build while a `--no-commit` merge is in flight.
- Battery: e2e suite (`vargo test --release`), `cargo test -p lean_verify`,
  fixture probe runners (probe9/17/13/14), tactus-core `--lean-all-proofs`.
- tgt gate baseline: re-run `tactus-group-theory/check.sh` against the merged
  binary; expected baseline = 0 errors (the 2026-07-13 `935179f` clean-gate
  baseline, ~2700v) — compare error *locations*, not counts
  (`reference_tgt_gate_baseline_errors`).
- Parent verus-cad submodule pointer: not bumped without Danielle
  (`feedback_commit_in_ai_fortress_not_top_repo`).

**Done when:** main carries the bootstrap arc, full battery green, tgt gate at
its clean baseline, backup tag kept until Danielle confirms.

**Blocked by:** Danielle's go on timing. Sensible point: after bootstrap-66
(loop closure) or bootstrap-68 (default flip), whichever lands first.

## Progress

- (2026-07-16) Danielle gave the go (main-line planning session): sync needed
  NOW because main's defs build regressed (bootstrap-40/41 fixes live here
  only) — main's tgt gate is in islands fallback and the squeeze census is
  blocked on elaborable artifacts. Syncing at bootstrap-61 (48df388, gates
  green) rather than waiting for 66/68. W5-authoring mid-work (62-64
  uncommitted in this worktree) is NOT included — only committed state rides.
  Claimed by the main-line session (fable-mainline); merge executes in the
  MAIN checkout; main→bootstrap pre-merge skipped (main's divergence = 3
  board-only commits, no conflict surface).
