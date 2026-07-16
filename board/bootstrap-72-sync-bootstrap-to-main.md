---
title: "sync — merge bootstrap branch → tactus main (W5/W6/W7 + serializer fixes; incl. the W7 typ_data fix)"
status: done
claimed_by: fable-mainline
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T20:15:00Z
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

## Writeup

**DONE — main carries the bootstrap arc through bootstrap-61 (merge `a254eb8`,
2026-07-16).** Backup tag `backup-main-pre-sync-20260716` KEPT until Danielle
confirms.

Execution notes vs the checklist:
- Synced at bootstrap-61 (48df388 + board-claim aebdff0), before the 66/68
  "sensible point" — Danielle pulled timing forward because main's defs build
  regression (bootstrap-40/41 fixes lived here only) had tgt's gate in islands
  fallback and blocked the squeeze census. W5-authoring mid-work (62-64,
  uncommitted in the bootstrap worktree) did NOT ride — committed state only.
- main→bootstrap pre-merge skipped: main's divergence was 3 board-only
  commits, zero conflict surface. Merge was clean ('ort', no conflicts; the
  two boards' file prefixes don't collide).
- `vargo test -p lean_verify` isn't a thing (vargo rejects the package) — the
  correct form is `VERUS_IN_VARGO=1 cargo test --release -p lean_verify`.

Battery (all on the merged tree, fresh release build; vstd 1530/0):
| stage | result |
|---|---|
| e2e suite (`vargo test --release -p rust_verify_test --test tactus`) | **551 passed / 0 failed** (159s) |
| lean_verify units | **367 + 7 / 0** |
| tactus-core `--lean-all-proofs` | **98 verified / 0 errors**, package gate: 50 modules, kernel-verified |
| fixture cert regen (`--tactus-emit-cert`) | 23 verified / 0, 24 certs |
| probe9 bridge | ALL BRIDGES BEHAVE AS CLASSIFIED ✓ |
| probe13 expr mutation-kill | PASS ✓ (4 baselines close, 4 drops flip) |
| probe14 G4.2 if-join | OK ✓ (opaque 0 / wired 1 / 6 kills flip) |
| probe17 W7d live def-bridge | OK ✓ (every def/dt cert closes) |
| tgt gate (`check.sh`, live Lean) | **24 verified + 6322 cached / 0 errors**, **package gate LIVE**: 12 modules, composition + axiom closures kernel-verified (5m28s cold) |

tgt gate baseline: 0 errors — better than the "compare locations" fallback
needs. The package gate note replacing the "skipped: shared-defs unavailable"
fallback note is the defs-regression heal, confirmed end-to-end.

Parent verus-cad submodule pointer NOT bumped (per checklist / Danielle).
The bootstrap branch's copy of this card still says in_progress — reconciles
at the next sync (updates recorded here on main, the card's post-merge home).
