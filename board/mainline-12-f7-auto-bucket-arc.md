---
title: "F7 — the auto bucket (~24k goals): per-cluster policy arc"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

The honest `--lean-all-proofs` migration workload: ~24,080 auto-closer goals
across ~2,230 currently-failing proof fns (post F1-F4 re-measure). This is a
POLICY arc per cluster, not one code fix. Taxonomy (from the overnight-log
kickoff analysis):

- **46% quantified/let-wrapped** — the closer has no intros; `tactus_peel <;>
  omega` validated against all shapes incl. let-Props in scratch. After
  mainline-07 this is emitter-emitted explicit structure + omega — i.e. this
  cluster should fall to the S-arc machinery largely for free. Measure it.
- **41% seq-op** — broadcast axioms ARE in context (`_tactus_bc` hyps); the gap
  is INSTANTIATION, not availability. The squeeze/derivation tooling
  (mainline-03/05) is exactly the instrument: derived `simp only` lists that
  name the needed axioms.
- **12% unfold-shaped** — spec-fn definitional unfolds; derivation-rule
  candidates (the emitter knows the mentioned defs).
- **Nonlinear: 10 goals total** — inline proofs, ignore for machinery.
- **Pred-twin modules duplicate ~2×880 goals** — effective work is roughly half.

Sequencing: AFTER mainline-05/06/07 land — those change this population
wholesale; re-taxonomize before hand-work. The full corpus re-measure is ~14h
(6h-timeout legs + -V cache resume; britton_via_tower + machine_group are
multi-hour) — plan it as an overnight run.

**Done when:** post-S-arc re-taxonomy committed; per-cluster policy decided and
recorded; pass count meaningfully above the 723/2,953 baseline with the residue
counted and named (no silent caps).

**Blocked by:** mainline-05 (and ideally -06/-07).

## Status update (2026-07-17, after S2c/B4/B6/B10)

Everything this arc was sequenced behind has now LANDED (mainline-05/06
derivation + 07 peel + the AssertQuery fallback + 10 decreasing
dispatch), so the re-taxonomy it planned is due, with better numbers
than it expected:

- **The 46% quantified/let-wrapped cluster**: B4's explicit peel +
  the zeta-substitution fix (Let case = `intro <name>; subst <name>`)
  is exactly this machinery. Note the let-opacity lesson: context
  let-vars are opaque to omega; goal-lets must be substituted. Any F7
  hand-work in this cluster should use the current binary, which
  handles it natively.
- **The 41% seq-op cluster**: the S2a census says the gap is NOT
  instantiation-by-name in this pool — the `_tactus_bc` broadcast hyps
  in context already carry the seq axioms and simp_all uses them.
  ZERO named seq-axiom lists were needed in the 295-theorem census.
  Expect a smaller residue than the taxonomy predicts.
- **The 12% unfold-shaped cluster**: confirmed real via the tutorial
  (fib unfolds needed user `unfold` texts). Per-goal mentioned-spec-fn
  unfolding is the one derivable shape the census found NO need for in
  gt but the tutorial needed — candidate rule #2 if the re-measure
  shows it at scale (would need Danielle's rule-budget sign-off).
- **Harness assets for the re-measure**: the full-pool gate
  (per-file combined runs, ~2 min over 397 theorems) and
  `tools/rung-attrib/squeeze_census.py` + `union_core_test.py` are
  committed and directly reusable for the ~24k-goal taxonomy. The
  6h-timeout legs + `-V cache` resume plan stands.
- **Nonlinear: 10 goals** — inline proofs, ignore for machinery.
  (The tutorial's nonlinear asserts all close via `by(nonlinear_arith)`
  with the DERIVED fallback composed in — that path is healthy.)
