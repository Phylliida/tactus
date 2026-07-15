---
title: "W5e — reference-WP soundness, closures (+ W5f adequacy spine)"
status: todo
claimed_by:
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T21:30:00Z
---

## Description

Final W5 ladder rungs (`DESIGN-W5-soundness.md` §4).

- **W5e**: model closures in the operational semantics and prove the
  `ClosureBody`/closure `wp_stm` arms sound.
- **W5f** (spun out here, can start once W5a–e land): the hand-Lean **adequacy
  spine** — `TGoal.toProp` + a structural induction relating the Val-level
  `holds` denotation (`DESIGN-W5-soundness.md` §2.1) to the user-facing `Prop`s,
  with generated per-datatype embedding lemmas. Lifts soundness from the Val
  level (the drift-detector) to the actual theorems users prove. Small,
  audited-once, not trusted (it is the *statement* of soundness; spec-adequacy
  covers it, master plan §8.5).

**Blocked by:** the rest of the W5 ladder.

## Progress

## Writeup
