---
title: "Heartbeats triage (998 blocks at last measure — stale, re-count first)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

998 maxHeartbeats-exceeded blocks in the §10.2 re-measure — the number predates
the F2b/F2c batch, B5 merge, and Option B, so RE-COUNT before triaging
(cheap grep over a fresh overnight-run log; can ride mainline-12's re-measure).

Triage questions: which tactic burns (tactus_auto search? simp_all in
particular?); does the S-arc's search removal dissolve most of these (derived
`simp only` is far cheaper than ladder search — plausible bulk win); what's the
per-fn distribution (a few multi-hour modules vs spread)? Remember:
"rlimit exceeded" under --lean-backend is a mislabel for Lean maxHeartbeats.

Policy options per cluster after counting: derived-tactic replacement (free via
S-arc), goal splitting, genuine heavy proofs → inline with raised local budget,
never a global heartbeats raise (the rlimit-cliff moral equivalent).

**Done when:** fresh count + burn attribution committed; per-cluster
disposition recorded; any global-budget change explicitly ruled out or
justified to Danielle.

**Blocked by:** soft — best after mainline-05 (population changes).
