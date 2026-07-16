---
title: "Per-measure decreasing_by dispatch (kill the rung chain)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

The `decreasing_by` tactic in `to_lean_fn.rs` (DECREASING_BY_TACTIC) is a
`first`-chain of static branches (div, seq-companion, Int.toNat/omega, ...) — a
mini-tactus_auto by the guiding rule ("dispatch counts too: emitter picks ONE
tactic — it knows the goal class it built"). The emitter knows the measure shape
it just rendered; replace the chain with per-measure-shape dispatch, reusing
S1's classify-then-select machinery in `tactic_select.rs`.

Known measure shapes to cover (from the F2/companion history): plain
datatype/structural, seq drop_first/drop_last (proven companions), div, Int
measures via `.toNat` wrap (F2b), `(repeat split) <;> omega` shapes,
wf_preprocess-threaded ∨/∧ guards (F2c). Each gets a named branch selected at
emission, not tried in sequence.

**Done when:** DECREASING_BY_TACTIC no longer emits a `first`-chain; each
dispatch arm is selected from the rendered measure; suite green, 0 regressions
(termination obligations are preamble-def replays — validate with the e2e
termination tests + the F2b/F2c pins).

**Blocked by:** nothing hard; naturally rides after mainline-05 lands the
generalized select machinery.
