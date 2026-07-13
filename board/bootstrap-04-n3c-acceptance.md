---
title: "N3c — serializer acceptance: elaborate + decide smoke + golden + determinism"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Close out the serializer per its acceptance criteria. Small; may share a
session with N3b.

Spec: `DESIGN-N3-serializer.md` §7.

- Every exec/WP-proof fn in `bootstrap-fixture/lib.rs`, `w15_probe.rs`, and
  `tactus-core/lib.rs` either serializes or is a documented stage-A exclusion
  (expect: the two bv fixture fns excluded, everything else in).
- Every cert file ELABORATES against the vendored TactusCore olean, and one
  `decide`/`#eval` probe per file (`stm_size <literal> = <n>`) confirms the
  literal kernel-computes. (Folds N5's smoke into acceptance.)
- Two consecutive runs ⇒ byte-identical cert files.
- Suite stays green with the flag off AND on (cert emission must not perturb
  verdicts).
- Golden-file unit test pinning one fixture fn's full cert text (drift =
  reviewed diff, like the trusted code it is).
- `sst_serialize.rs` under 1k lines incl. the contract doc-comment; verify.

**Done when:** all six criteria pass; doc §9 open-questions answered from the
real structs; battery green flag-on and flag-off.

**Blocked by:** bootstrap-03 (N3b).

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
