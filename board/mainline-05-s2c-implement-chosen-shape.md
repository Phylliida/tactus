---
title: "S2c — implement the derivation-first squeeze (uniform CORE tactic + residue inline proofs)"
status: in_progress
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T22:50:00Z
---

## Description

Implementation of the mainline-04 decision (derivation-first, no store — see
DESIGN-transparent-automation.md §3.4). SCOPE FINAL per that decision.

- **The derivation rule** (rule budget: ONE) in
  `lean_verify/src/tactic_select.rs`, generalizing S1's classify-then-select:
  when the closer would be `tactus_auto`, emit instead the uniform text
  `simp_all only [CORE] <;> omega` where CORE is the fixed 43-lemma
  site-invariant list from MEASUREMENT-s2a-derivability.md §6. Same single
  chokepoint (emit_with_extras), NEVER overrides user closers or S1's
  linear-fragment omega selection (S1's omega is cheaper for its goals; the
  derived simp is the fallback for everything else). Every derived tactic is
  name-is-spec at the site; the rule itself spec'd in a code comment.
- **Feasibility gate FIRST**: before touching the emitter, validate the
  uniform tactic over the FULL Brick-1 pool (all 215 theorems, not just the
  T2 winners) — the census proved the derived tactic closes T2 goals, but
  lower-rung goals (rfl/decide/omega/peel winners, 32.6% of Brick 1) must
  also still close. If unconditional replacement regresses lower-rung goals,
  the rule becomes: keep S1's rung-preserving selection for goals the emitter
  classifies (S1 machinery), derived simp for the rest — still rule-budget
  one, still no store.
- **Residue inline proofs**: apply the 13 squeezed lists (2 clusters, 3
  effective sites) as inline `by { }` proofs in gt source — MEASUREMENT doc
  §7 has the clusters; the CSV has the per-theorem lists. This is the
  task's validation that the residue path works, AND it pays down the T2
  share directly.
- **Suggestion report for future residue**: obligations whose derived tactic
  fails (new shapes falling out of CORE) get surfaced with their squeezed
  list ("N obligations suggest inline proofs" + per-site text), NOT silently
  ladder-closed. Failure is LOUD per §3.4.

Preservation methodology (the S1 standard): per-file pre/post error-count
diff over the 114 known-passing gt artifacts = 0 regressions required; suite
green; tutorial 9/9; tgt gate stays 0 errors.

Progress bar: re-run `tools/rung-attrib/fast_attrib.py` after landing — the
T2 share (67.4% at Brick 1) trending toward 0 IS the tactus_auto-removal
progress bar. Record the new histogram here and in the design doc.

**Done when:** derivation rule landed with 0 regressions, residue inline
proofs applied in gt (or explicitly deferred as counted residue), new
rung-attribution histogram committed.

**Blocked by:** mainline-04 — CLEARED 2026-07-16 (decision recorded in
DESIGN-transparent-automation.md §3.4).

## Progress

- (2026-07-16 ~22:50Z, kimi) Claimed after the 04 decision. Starting with
  the feasibility gate: full-pool validation of the uniform derived tactic
  (census covered T2 winners only; the 68 lower-rung theorems must also
  still close).
