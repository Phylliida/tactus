---
title: "S2c — implement the chosen squeeze shape (likely: derivation rules + suggestion report)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

Implementation of whatever mainline-04 decides. SCOPE IS PLACEHOLDER until then;
rewrite this description after the decision. Under the primary candidate
(derivation-first) the shape is:

- **Derivation rules per obligation kind** in `lean_verify/src/tactic_select.rs`,
  generalizing S1's classify-then-select: when the closer would be
  `tactus_auto` and the obligation's kind has a derivation rule whose lemma set
  is site-computable, emit `simp only [derived list] (<;> omega)` instead.
  Same single chokepoint (emit_with_extras), never overrides user closers.
  Every derived tactic is name-is-spec at the site; the derivation rule itself
  is spec'd in code comments per kind.
- **Suggestion report for the residue**: obligations whose squeeze needed
  goal-specific lemmas get surfaced ("N obligations suggest inline proofs" +
  per-site text), NOT silently ladder-closed. Applying suggestions to gt source
  is part of this task's validation (the ~70 effective T2 theorems shrink to
  whatever derivation doesn't cover).

Preservation methodology (the S1 standard): per-file pre/post error-count diff
over the 114 known-passing gt artifacts = 0 regressions required; suite green;
tutorial 9/9; tgt gate stays 0 errors.

Progress bar: re-run `tools/rung-attrib/fast_attrib.py` after landing — the T2
share (67.4% at Brick 1) trending toward 0 IS the tactus_auto-removal progress
bar. Record the new histogram here and in the design doc.

**Done when:** derivation rules landed with 0 regressions, residue suggestions
emitted and (for gt) applied or explicitly deferred as counted residue, new
rung-attribution histogram committed.

**Blocked by:** mainline-04.
