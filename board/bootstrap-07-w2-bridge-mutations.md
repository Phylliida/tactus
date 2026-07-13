---
title: "W2b — the bridge + mutation-kill acceptance (fixture scale)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Wire refWp against the serialized certs and prove the certificate is both
correct AND sensitive.

Spec: `DESIGN-W2-refwp.md` §2.3–2.5.

- Per fixture fn, emit the bridge line
  `example : goals_eq (refWp ctx sst) production = true := by decide`
  (and confirm `rfl` also closes).
- **Mutation kills** (the whole point — green-on-everything proves nothing):
  hand-perturb copies of one cert file (swap two hypotheses, drop a binder,
  reorder two goals, change one leaf id); each mutation MUST flip the verdict.
  Check in as `probe-w0/probe10_mutations/` with a runner.
- Record per-fn bridge wall-clock (P2 baseline: 600-stm ≈ 2.8s with raised
  maxRecDepth; expect fixture fns far below).
- Every cert header carries the honest stage-A scope statement (§2.5):
  certifies statement ASSEMBLY, not leaf rendering / serializer / frontend /
  SST adequacy. A stage-A pass coexisting with a leaf-renderer bug is expected.

**Done when:** every fixture bridge closes by `decide`; all mutations flip the
verdict; timings recorded; scope statement present in headers.

**Blocked by:** bootstrap-04 (N3c cert files) + bootstrap-06 (W2a worker).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
