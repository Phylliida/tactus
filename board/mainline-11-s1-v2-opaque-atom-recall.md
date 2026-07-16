---
title: "S1 v2 (optional) — admit consistent-occurrence opaque atoms as free int vars"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

S1's classifier is deliberately conservative: opaque atoms (`Seq.len s`, spec-fn
apps) fall OUT of the linear fragment, because omega treating them as free vars
is unsafe syntactically (cross-atom equality trap). Cost: recall 24 selections
vs the harness's 37 omega-closable count on gt.

v2: admit single-occurrence / consistent-occurrence opaque atoms as free
integer variables (each distinct atom = one fresh var, only when no two distinct
atoms could alias in a way omega would misuse). GATED on the same 0-regression
per-file pre/post diff over the 114-fn pool — measure, don't assume.

Priority: LOW for gt (opaque-heavy corpus, T2 is the lever); value scales with
arithmetic-heavy exec crates. Pick up opportunistically or when such a crate
becomes a gate.

**Done when:** re-diff shows 0 regressions and recall strictly improves
(target: close the 24→37 gap on gt); classifier rule documented in
tactic_select.rs with the aliasing argument.

**Blocked by:** nothing.
