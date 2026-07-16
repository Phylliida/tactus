---
title: "S2a — squeeze spike + derivability census over the 145 T2 theorems"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

THE key measurement brick of the squeeze arc — measurement, NOT machinery. Do not
build any persistence layer in this task.

Two halves:

1. **Squeeze spike (empirical-first, scratch Lean before Rust).** Confirm the
   used-lemma extraction API on the pinned toolchain (v4.25.0): `simp_all?` /
   `Simp.Stats` used-theorem tracking (`DESIGN-transparent-automation.md` §3.1
   flags "confirm exact API"). Hand-squeeze a few of the 145 T2 theorems to
   `simp only [named] (<;> omega)` and confirm the minimized forms close.
   Scratch loop: `cd tactus/lean-project && LEAN_PATH=~/.cache/tactus/prelude
   lake env lean file.lean`.

2. **Derivability census.** Extend `tools/rung-attrib/fast_attrib.py` (or a
   sibling harness) to squeeze ALL 145 T2 theorems in the Brick-1 pool and, for
   each minimized lemma list, classify:
   - **DERIVABLE**: every lemma is computable from what the emitter knows at that
     obligation site — for preconditions: the callee's requires-mentioned spec-fn
     defs; for postconditions: the fn's own ensures-mentioned defs; plus the
     broadcast axiom set already in scope as `_tactus_bc` hyps, and datatype
     accessor/ctor lemmas of mentioned types.
   - **GOAL-SPECIFIC**: needs lemmas outside that computable set (creative
     choices — these are inline-proof candidates).
   Report per-kind rates (preconditions are 81% T2 and the doc predicts their
   lists are "small and formulaic" — test that prediction), plus the pred-twin
   dedup view (~70 effective theorems).

Output: `MEASUREMENT-s2a-derivability.md` + per-theorem CSV. This census is the
decision data for mainline-04 — if the derivable share is high, pin STORAGE is
unnecessary and the whole arc stays two-surface.

**Done when:** census doc committed with per-kind derivability table, the
squeeze API confirmed working on our toolchain, and ≥3 hand-validated squeezed
theorems demonstrating the minimized forms elaborate.

**Blocked by:** nothing (harness + pool exist from Brick 1).
