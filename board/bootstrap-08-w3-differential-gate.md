---
title: "W3 — differential gate over tgt (the bug-finding payoff)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Run serializer + bridge across tgt. Every fn where `decide` says NO is a bug in
production, refWp, or the serializer — all three are interesting. This is a
bug-FINDING deliverable independent of the W5 soundness proof, and the first
milestone where the certificate holds at real-corpus scale.

Spec: `DESIGN-W2-refwp.md` §3; claim-ladder rung 3 in `VERIFICATION-PATH.md`.

- Certs emitted during a normal gated run; bridge files batch-elaborated like
  stmt modules (reuse `ensure_stmt_olean`-style plumbing).
- Failures reported per-fn with both GoalData terms pretty-printed + a small
  Rust differ computing the first-divergence path (goal index → spine
  position) so triage never reads raw terms.
- Triage discipline: classify every divergence (production bug / refWp bug /
  serializer bug / stage-A scope gap) in a running table in `DESIGN-W2-refwp.md`.
  Scope gaps feed stage B; production bugs get pinned e2e tests (like this
  week's five).
- Bridge wall-clock budget ≤ the package gate's own cost (else flag for W4).

**Done when:** tgt divergences = 0 UNEXPLAINED; certified fraction reported;
triage table complete; any production bugs found are pinned with e2e tests.

**Blocked by:** bootstrap-07 (W2b bridge) + bootstrap-05 (N4 census informs
which constructs are in scope).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
