---
title: "(Optional) Profile the ~85s verus-side warm floor on tgt"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

Post-M6, tgt warm runs sit at ~82-92s and that cost is VERUS-SIDE (rustc + VIR +
emission/harvest over 3116 fns), not Lean — lean-side waste was fully
eliminated by the island/package caches. If daily tgt iteration should go under
~30s, this floor is the frontier. Candidate suspects (from the island-cache
arc): island emission rendering for all lean fns; spec-world walks ×2 scopes;
ladder-hash checks; rustc itself; Z3-cache hashing.

Discipline notes: check `uptime` BEFORE trusting any wall-clock (the phantom
89→300s "regression" was host loadavg 208); worktree A/B baselines need
source/z3 + tree-sitter-tactus copied in; `/tmp/defs_repro.rs` + debug binary =
20s ladder iteration for emission-side hypotheses.

Priority: LOW — only matters if iteration speed starts hurting. Danielle's
call whether to spend a session here.

**Done when:** profile breakdown committed (where the 85s goes, in buckets) +
either one landed win or an explicit "not worth it" close.

**Blocked by:** nothing.
