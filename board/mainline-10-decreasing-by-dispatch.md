---
title: "Per-measure decreasing_by dispatch (kill the rung chain)"
status: done
claimed_by: kimi
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

## Progress

- (2026-07-17 ~14:00Z, kimi) Claimed. Ground truth first: the chain is
  `all_goals (first | omega | mod | div | div∘simp | subrange |
  drop_first | drop_last | split | chaining | decreasing_tactic)`.
  Design settled empirically: classify on the SELF-CALL argument
  transformation (verified via find_cancellation_from — its measure is
  Int.toNat-wrapped + seq-shaped, but the self-call arg is `start+1`
  (linear) → omega closes; measure-head classification would have
  misrouted it).
- (2026-07-17 ~15:30Z, kimi) Dispatch landed (`decreasing_kind` in
  to_lean_fn.rs), then THREE real classifier gaps found by the gt
  gate's full defs rebuild, each pinned by a unit test:
  (1) let-bound self-call args (`let rest := drop_first w; f data rest`
  — britton_via_tower.translate_word_at) — let-values are searched and
  their signals merge into later args;
  (2) self-calls inside let VALUES (`let rc := f (drop_first w) n` —
  britton.stable_letter_count) — values are searched for self-calls
  BEFORE registering the var's arg-shape signals;
  (3) nested suffix behind a let-var (`split_q (drop_base_run after)`
  — m3_blinker) — the lets map threads through the suffix-context walk
  so `drop_base_run (drop_first W)` reads as Chaining.
- (2026-07-17 ~16:20Z, kimi) **The factorial deep-dive (the big one).**
  factorial failed with an unconnectable `tmp__1✝` atom — root cause:
  a goal-position `let` intro'd by B4's peel becomes a CONTEXT
  let-var, which omega treats as OPAQUE (it never unfolds context let
  bindings). The old ladder survived by zeta-reducing goal-lets with
  simp BEFORE any intro. Fix: peel's Let case emits
  `intro <name>; subst <name>` (zeta-substitution), verified against
  the real failing theorem (154:18 overflow check with
  `result*(i+1) ≤ 3628800` in context). A/B showed the failure
  predates mainline-10 (B4-era) — the tutorial's shared target dir
  had been masking it with cached islands.
- (2026-07-17 ~16:45Z, kimi) **FULL BATTERY GREEN:** gt gate 3116/0
  (multiple full defs rebuilds, 0 failed parts) · tutorial 10/10 ·
  suite 138/140 (= main-line parity, same 2 pre-existing Z3-path
  failures) · lean_verify 374 + 12 new dispatch tests. Final
  decreasing_by distribution in gt: 28 omega / 15 drop_first / 2
  drop_last / chaining for split_q — ONE named rung per artifact, no
  `first`-chain anywhere in default emission.

## Writeup

**Done-when review:** DECREASING_BY_TACTIC's `first`-chain is gone —
each dispatch arm is selected at emission from the rendered measure +
self-call args ✓ (distribution above; no `first |` outer chain in any
fresh artifact); suite green ✓; 0 regressions ✓ (gt gate 3116/0,
tutorial 10/10, termination e2e green).

**The classifier (decreasing_kind, to_lean_fn.rs):** signals from
self-call argument transformations + measure shape, resolved through
let-bindings (both directions: let-bound args, and self-calls inside
let values). Priority: Chaining (nested suffix + registered monos) →
SeqSubrange → SeqDropFirst → SeqDropLast → Modular → Div →
Structural (ctor-shaped args → decreasing_tactic) → Split (If/Match
in measure) → Linear (omega; covers Int.toNat-wrapped measures with
linear self-call args — verified).

**Side effects worth knowing:** (1) the Let zeta-substitution fix in
render_peel (B4's peel) — `intro <name>; subst <name>` — fixes a
class of failure where ANY leaf tactic meeting a goal-let faced an
opaque context let-var (omega/simp-all can't unfold context let
bindings; only goal-position lets get zeta-reduced). (2) proof-fn
bodies render once extra for signal detection (emission-only, no
artifact change). (3) div keeps an inner 2-ladder — the bootstrap-44
Prop-ite guard case is guard-shape dependent, not measure-dependent.

**Follow-ons:** mainline-18 (prelude cache race) hit twice during
validation (tutorial flakes under concurrent gates — solo always
green); the defs may_skip logic leaves deleted-.lean parts
sourceless-but-cached (harmless but surprising during forensics).
