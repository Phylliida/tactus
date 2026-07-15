---
title: "W5f — adequacy spine: Val-level `holds` → user-facing `Prop`s"
status: todo
claimed_by:
created: 2026-07-15T05:10:00Z
updated: 2026-07-15T05:10:00Z
---

## Description

Final W5 ladder rung (`DESIGN-W5-soundness.md` §4, W5f row; §2.1 note). Spun out
of bootstrap-53 now that W5a–e have all landed (probe21–26).

The hand-Lean **adequacy spine**: `TGoal.toProp` + a structural induction
relating the **Val-level** `holds` denotation (`DESIGN-W5-soundness.md` §2.1 —
the `holds : GoalData → St → Prop` used by probe21–26) to the **user-facing
`Prop`s** that appear in the theorems users actually prove, with generated
per-datatype embedding lemmas.

W5 v1 (probe21–26) states soundness at the **Val level only** — that is already
the full drift-detector (`ref_wp c s` faithfully computes the obligation
telescope, and if those goals hold the operational safety predicate holds). W5f
lifts this from the Val level to the user's `Prop`s, so that "the emitted goals
hold" ⟹ "the user's stated theorem holds".

Small, **audited-once, not trusted** — it is the *statement* of soundness, so
spec-adequacy covers it (master plan §8.5). It does NOT re-prove any Val-level
math; it is a thin denotational bridge.

**Blocked by:** none remaining — W5a–e all done (bootstrap-49..53).

## Design notes (starting points)

- The Val-level `holds` (probe26 `w5e_sem.lean`) is structural on `GoalData`:
  Leaf→`hp id st`, LeafE→`he e st`, Imp→`hp h st → holds t`, All→`∀ n, holds t
  (upd st x n)`, Let→`holds t (upd st x (lv v st))`. The three oracles
  (`hp`/`he`/`lv`) are the seam: the adequacy spine must relate a *concrete*
  interpretation of these oracles (from the real Val universe) to the user `Prop`.
- Likely shape: a `TGoal.toProp : GoalData → Prop` that reads the deep expression
  content (W6's `render_exp` deepening gives `he` a concrete meaning) and a
  theorem `holds hp he lv g st ↔ TGoal.toProp g` for the concrete oracle triple,
  by induction on `g`. Per-datatype embedding lemmas handle the leaf universe.
- Interaction with W6 (stage-B deep expressions): W5 is valuation-parametric
  (`DESIGN-W5-soundness.md` §1, option b) precisely so the oracle interpretation
  is deferred; W5f is where a concrete interpretation gets pinned. Check whether
  W5f should wait for / co-design with W6's `render_exp` semantics, or state the
  spine parametrically and specialise later.

## Progress

## Writeup
