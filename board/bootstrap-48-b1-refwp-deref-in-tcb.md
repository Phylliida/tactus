---
title: "B1 (soundness follow-up) — move the structural-binop deref-balance into the TCB render_exp (close bootstrap-39's common-mode gap)"
status: todo
claimed_by:
created: 2026-07-14T17:00:00Z
updated: 2026-07-14T17:00:00Z
---

## Description

`bootstrap-39` closed the `&`-deref bridge divergence with **B2**: the
transcriber `raw_exp` (`sst_serialize.rs`, `ExpX::Binary` arm) inserts
`RawExp.Deref` nodes by mirroring production's structural-binop min-balance
(`to_lean_sst_expr.rs:1157-1161`, driven by `count_ref_decorations`). That works
and is validated, but it has a **common-mode soundness gap**: production AND
`raw_exp` both compute the peel from the same `count_ref_decorations` helper, so
the bridge no longer *independently* checks the deref-count — a bug in that
helper reproduces identically on both sides of `goals_eq` and silent-passes. The
reference `render_exp` (TCB) sees only pre-baked `Deref` nodes; it never derives
the peel itself. (My analysis + Danielle's local model both landed on this,
independently.)

**B1 closes the gap** by moving the deref-balance into the trusted reference:
extend the TCB `render_exp` BinOp arm to compute the peel from the operand types
it ALREADY reads for nat-coercion (`type_of l`, `type_of r`), emitting the
`FieldProj … deref_field`s itself. Then:
- `raw_exp` goes back to emitting the bare ref-typed `Var` (revert B2's
  `wrap_derefs` in the Binary arm — B1 and B2 are MUTUALLY EXCLUSIVE; keeping
  both double-derefs).
- The deref-balance lives where W5 will prove it sound and where the bridge
  *independently* checks production's deref against the reference's.

**Feasibility note (from bootstrap-39 recon):** TypData ref-depth is bounded 0/1
(`TypData.Ref inner` where inner is Named/Int/…, never nested `Ref`), so the
BinOp-arm min-balance in `render_exp` is a small bounded change, structurally
identical to the existing `needs_nat_coercion` coercion the arm already does.

**Done when:**
- `render_exp` (tactus-core `lib.rs`) BinOp arm min-balance-derefs from operand
  types; its `expr_mirror_kernel_computes` companion lemmas re-verify green.
- `raw_exp`'s Binary arm reverts to bare-operand emission (drop B2's
  `wrap_derefs`; the helper can stay if unused-warnings are silenced, or be
  removed).
- The `runtime__impl__4__clone` in-gate bridge still closes (`1 passed, 0
  failed`) — now with the deref logic in the TCB, independently checked.
- e2e suite green; the bootstrap-38 fixture still 3/3 in-gate close.

**Blocked by / relationship:** do NOT start until Danielle rules on B1-vs-B2 for
bootstrap-39 (she recommended B2 "for this stage"; this card is the principled
upgrade). If she keeps B2, this stays `todo` as recorded tech-debt. If she
fast-tracks B1, revert the B2 commit first.

## Progress
- (2026-07-14, opus-w4a-tgtval) Filed as the soundness follow-up to bootstrap-39.
  B2 landed there (validated at decide level). See bootstrap-39's "FIX BUILT +
  VALIDATED" section for the full B1/B2 analysis, the unsound-Var-sketch
  correction, and the local-model verdict.

## Writeup
_when done_
