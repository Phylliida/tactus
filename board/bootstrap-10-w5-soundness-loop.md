---
title: "W5 — soundness of the reference WP (the bootstrap loop closes) [staged, very large]"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Prove refWp sound against a written-down operational semantics of SST, authored
as tactus proof fns, verified by tactus, emitted as one more kernel-checked
package. This closes the loop non-circularly (the fixed point is checked by the
kernel, not by tactus). **tactus-group-theory-scale formalization** — this is an
umbrella; split into W5a–e sub-tasks when started.

Spec: `DESIGN-bootstrap.md` §5 (W5 row) + §6 (loop diagram);
`DESIGN-W2-refwp.md` §4 open question §5.5.

- `SstSem`: fuel-indexed big-step evaluator over the mirror SST (total spec fn).
  `refWp_sound : (refWp ctx s) all-hold → safe s`, partial correctness first
  (termination obligations as their own family, as Verus splits them).
- **Decide first (open Q §5.5):** a fuel evaluator cannot evaluate opaque
  leaves. Either land stage B (W6) first, OR make `SstSem` VALUATION-PARAMETRIC
  (leaf oracle `LeafId → State → Value`, `refWp_sound` quantified over oracles
  consistent with the leaf-table typing). (b) preserves the planned parallelism
  and front-loads the leaf-typing discipline W6 needs anyway.
- Staging: W5a straight-line + if/else + assert/assume; W5b calls (the exec
  call rule DESIGN-emit-module §4.4 leaves open); W5c loops + havoc; W5d
  &mut/prophecy (∀-quantify the final value); W5e closures.
- Needs R0a-quality lean-only coverage on tactus-core itself (everything routed
  to Lean) for the loop-closure claim.

**Done when (umbrella):** refWp_sound proven for the stage-A fragment and its
package passes the axiom-closure gate; claim becomes "kernel-checked
obligations ⟹ the operational spec".

**Blocked by:** bootstrap-06 (W2a shapes) for authoring; can run long in
parallel with W3/W4. The valuation-parametric decision unblocks starting before
W6.

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
