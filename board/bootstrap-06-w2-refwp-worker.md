---
title: "W2a — reference WP worker (wpStm/frameAfter/goal_eq) in tactus-core"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Author the reference WP as `tactus-core` spec fns over the (post-N2.1) mirror
types. The emitted defs ARE the checker the certificate runs.

Spec: `DESIGN-W2-refwp.md` §2 (shape, equations, equality).

- `refWp : FnCtxData → StmData → GoalList` (LHS of the bridge).
- First-order worker `wpStm(frame, stm)` + companion `frameAfter(frame, stm)`
  — NO spec_fn continuations (closures are trigger/kernel-hostile). `Seq(a,b)`
  = `wpStm(f,a) ++ wpStm(frameAfter(f,a), b)`. Single-datatype structural
  recursion over `StmData` (what N2's Seq/Skip design bought).
- Implement the §2.2 equations: Assert/Assume/Assign/Call/If/Loop/Ret/DeadEnd/
  Skip, and `refWp`'s frame seeding + fall-through Ret.
- `goal_eq`/`goals_eq : … → Bool` structural spec fns for the `decide` bridge
  (avoids a DecidableEq emission feature; that knob is a separate follow-on).
- All spec fns `#[verifier::structural_decreases]`; in-crate `decide` unit
  examples; verifies lean-only-clean through the package gate.

Answer empirically (from fixture cert diffs) and record in doc §5:
- §5.1 post-If continuation: does the walker duplicate the rest per branch or
  join? Mirror follows whatever it does.
- §5.2 fall-through postcondition placement.
- §5.3 loop-body invariant obligations: SST Assert nodes or walker-synthesized?
- §5.4 overflow-guard asserts: pre-injected or walker-injected?

**Done when:** refWp + helpers verify 0 errors under the package gate; `decide`
unit examples compute; the §5 open questions are answered.

**Blocked by:** bootstrap-01 (N2.1 shapes). Can overlap N3 (N3 produces the
cert data this consumes); the bridge itself is W2b.

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
