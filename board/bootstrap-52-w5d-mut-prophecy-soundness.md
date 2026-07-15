---
title: "W5d — reference-WP soundness, &mut / prophecy (∀-final-value model)"
status: todo
claimed_by:
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T21:30:00Z
---

## Description

W5 ladder rung (`DESIGN-W5-soundness.md` §4). Model `&mut` / prophecy semantics
(`final`/resolve) in the operational semantics and prove the corresponding
`wp_stm` arms sound. Standard trick: model prophecy by **∀-quantifying the final
value** (master plan O5) — pick ∀-final-value vs two-state framing by whichever
makes the proof go through; document the choice as part of spec adequacy (§8.5).

Hardest modeling in the ladder; do last (before closures).

**Blocked by:** bootstrap-49/50/51 (the frame + call + loop machinery).

## Progress

## Writeup
