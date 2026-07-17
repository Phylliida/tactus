---
title: "(Deferred) tactus-computability-theory Option B tactic-text migration"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

DEFERRED BY DANIELLE — parked here so it isn't lost, activate when it matters.

tactus-computability-theory's user tactic texts predate Option B naming (no
namespace wrapper, full dotted names at root). The gt migration needed ~80 site
edits (lib. prefixes) + hazards documented in the follow-ons arc (silent `try
unfold` misses, shadow wrong-resolution). ct needs the same sweep whenever it
returns to a live gate (it was dropped from the M6.4/5 validation protocol per
Danielle).

Note: if mainline-15 adopts `open <crate> in`, do THAT migration here directly
instead of the lib.-prefix sweep — don't migrate twice.

**Done when:** ct's crate-local ./check.sh gate green under the current
main-line binary.

**Blocked by:** Danielle's activation call; sequence after mainline-15's
decision.
