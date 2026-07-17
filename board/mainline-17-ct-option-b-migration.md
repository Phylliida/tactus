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

## Status update (2026-07-17, after S2c/B4/B6/B10)

Two things this task now inherits:
1. **The dependency-injection contract** (MEASUREMENT-s2a §6.2): ct's
   user tactic texts will hit the same three shapes the tutorial did —
   nullary-lemma applications (fix: drop the spurious arg), recursive
   self-calls needing explicit injected stmt binders
   (`mat_pow_square mat_mul_assoc m (k-1)`), and cross-fn proof-fn
   references that must stay UNQUALIFIED to hit the local stmt binder.
   Budget for ~80 site edits like gt's, plus this contract documented
   as the checklist.
2. **The B6 no-search gate**: when ct returns to a live gate, its
   check.sh should assert the claim via
   `tools/check-no-search.py` — with `--allow <file>` for any
   legitimately-counted residue until its overrides migrate (the
   zero-residue state gt reached is the goal but not the entry price).
