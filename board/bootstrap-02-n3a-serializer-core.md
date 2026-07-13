---
title: "N3a — SST serializer core + emission plumbing + fail-loud census"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Write `lean_verify/src/sst_serialize.rs` — THE new trusted component. Boring,
1:1, <1k lines, one file, faithfulness-contract doc-comment.

Spec: `DESIGN-N3-serializer.md` (whole doc; §2 snapshot, §3 contract, §4
leaves, §6 plumbing/versioning, §7 acceptance, §9 open questions).

Scope of N3a (no production-emitter changes beyond the hook call):
- Snapshot at the inputs of `sst_to_lean::exec_fn_theorems_to_ast` (the single
  source of obligation shape both island + pkg paths feed).
- Emit the SST literal in the tactus-core vocabulary (post-N2.1 shapes).
- Leaf interning via the PRODUCTION renderer (`sst_exp_to_typed(..).into_slot`)
  — identical text ⇒ same id; first-appearance walk order defined by the spec.
- Fail-loud: uncaptured construct ⇒ per-fn diagnostic + crate-end
  `certified M/N`. This one mechanism also IS the N4 census.
- `--tactus-emit-cert` flag (default off); cert files at
  `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean`.
- Vocabulary versioning: vendor `tactus-core/emitted/TactusCore.lean`,
  content-hash it into every cert header (mismatch = hard error).
- The faithfulness-contract doc-comment MUST enumerate every
  `FunctionSst`/`FuncCheckSst` field read and every field deliberately not,
  each with one line of why. That list is what a reviewer audits.

Answer, on first contact with the real structs (record in the doc §9):
FuncCheckSst field inventory; whether loops arrive pre-split; whether Call
contract exps are pre-instantiated at the snapshot point.

**Done when:** fixture + tactus-core cert files emit; census counters correct;
determinism holds (byte-identical across two runs); suite unaffected with flag
off. (Elaboration/decide smoke is N3c.)

**Blocked by:** bootstrap-01 (N2.1) — the literal shape must be frozen first.

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
