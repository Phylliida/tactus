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
