---
title: "W6e — expression-level mutation-kill (the Friction-2 kill) + G4 If/Let/Tuple fold-in"
status: todo
claimed_by:
created: 2026-07-14T05:05:00Z
updated: 2026-07-14T05:05:00Z
---

## Description

Fifth (final) rung of the W6 ladder. W6d (`bootstrap-23`) landed the deep bridge
end-to-end: for the coverable fixture corpus, obligation leaves emit
`GoalData::LeafE(ExprData)` on both sides, `refWp` closes via
`render_exp(rawExp)`, and the bridge `decide`s `expr_eq`. probe9 is green
(12/13 close-ok deep, max_u64 hfail-ok), verdict-neutral, and a spot-check
deep-mutation confirmed the deep compare is load-bearing (a `RawExp.Lit`
flip fails the bridge).

**W6e turns the spot-check into the systematic kill AND folds in the last gap:**

1. **The Friction-2 mutation-kill (the payoff).** On the PROD serializer side,
   drop an `Int.toNat` cast at one `sum_to` obligation site (the cast class:
   `Int.toNat r = lib.tri (Int.toNat n)`). The production emitter renders the
   coerced form; the reference `render_exp` re-derives the correct coercion. If
   the serializer silently omits a coercion the bridge MUST FLIP to fail (that
   is the entire point of the symmetric deep compare — stage-A string-compare
   would silent-pass a renderer that produced the "right-looking" string from a
   structurally-wrong `ExprData`). Wire this as a repeatable mutation harness
   (parallel to `probe10_mutations` / the bootstrap-15 RHS/SST kills), so a
   regression that re-introduces the blind spot is caught. Cover at least: a
   dropped nat-coercion (cast class), a dropped `.deref` (G2 head_exec), a wrong
   field accessor (G3 mk_point/swap_pair), a wrong HasType width (G6 add_capped).

2. **G4 — `If`/`Let`/`Not` fold-in (max_u64).** max_u64's two ensures leaves are
   the whole `x<y → (let r := let m:=y; m; r≥x ∧ r≥y)` If-fold, living on the
   GOAL path (`goal_data`/`GoalShape`), NOT `oblig_leaf`. Needs `ExprData::Let` +
   a `Not` (unary) representation + the goal-side fold that lifts the branch
   condition + let-bound return into one obligation expression (cf. bootstrap-19
   two-way-If-join / bootstrap-17 If-fallthrough for the SEQ desugaring already
   in place). This is the deepest gap and bites only one fixture fn — do it after
   the mutation-kill lands so the corpus win is banked first. When it lands,
   max_u64 flips from `hfail-ok` to `close-ok` in probe9 and its honest-fail
   entry in `probe9_bridge/run.sh` must be removed.

**Done when:** the mutation harness demonstrably FLIPS the bridge for each of the
four coercion-drop classes (never silent-passes); G4 lands and max_u64 bridges;
probe9 shows 13/13 close-ok (no honest-fails remaining); the whole thing stays
verdict-neutral for the un-mutated emission.

**Blocked by:** nothing (W6d done). **Blocks:** W7 (`bootstrap-12`, defs-layer)
is independent; W6e is the last correctness rung before the W6 ladder is closed.

## Progress

- (2026-07-14, opus-b27) Task created at W6d completion. Starting point: the deep
  bridge is live + Lean-verified + probe9-green; the tri_one deep-mutation
  spot-check (in bootstrap-23 W6d.3 progress) is the seed for harness item 1. The
  gap taxonomy (G0–G7) and per-fn coverage map are in bootstrap-23. G4 shape +
  the SEQ-desugar precedent are in bootstrap-17/19.

## Writeup

_when done: findings, how the mutation harness works, what each coercion-drop
kill demonstrates, the G4 fold-in mechanism, and any remaining Tier-2 residue._
