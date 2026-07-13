---
title: "N4 — serializer census over tactus-group-theory (~3116 fns)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Run `--tactus-emit-cert` over tgt + the fixture family. The crate-end
`certified M/N` summary + per-construct rejection counts IS the deliverable —
it sets the stage-B coverage roadmap and is the first honest measure of the
stage-A subset.

Spec: `DESIGN-W2-refwp.md` §1.

- Plumb the flag through tgt's crate-local `check.sh` (one line; the
  CRATE-LOCAL check.sh is the way to verify tactus-* — Lean backend + gt
  export).
- Append a ranked table (construct → fn count) to `DESIGN-W2-refwp.md`.
  Expected big buckets: trait-method obligations, generics, closures, bv.
- Measure cert-emission overhead (wall-clock delta flag on/off on tgt);
  budget expectation = rendering leaves twice.
- Confirm ZERO verification-behavior delta at scale (flag must not perturb
  verdicts) — re-check N3 acceptance §7.4 on the big crate.

**Done when:** the ranked table is in the doc; overhead is measured; verdict
delta is zero; the stage-B roadmap is legible from the numbers.

**Blocked by:** bootstrap-04 (N3c) — needs the working serializer.

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
