---
title: "W5-auth-1 — land the W5 semantic model in tactus-core (one batched cache-churning edit)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Author the W5 semantic model as tactus-core spec fns, in the shape frozen by
bootstrap-60. This is the one deliberate cache-churning edit of the authoring
arc — batch **all** model spec fns + any datatype additions into a single
commit so the tactus-core fn cache invalidates once (the N2/W6b discipline).

Contents (mirroring `DESIGN-W5-soundness.md` §2 and probes 21–24):

- Oracle params as `spec_fn` arguments (probe32-validated): leaf-holds oracle
  `hp`, let-value oracle `lv` (+ state type St per the frozen interface).
- `holdsAll : GoalList → …` (Val-level goal denotation over oracles).
- `closeSem : FrameList → St → cont → …` (FBind→forall, FHyp→implies,
  FLet→let) in the bootstrap-60 winning shape.
- `execSafeF : FrameList → StmData → St → …` — **total over all 10 StmData
  constructors** (Skip/Assume/Assert/Assign/Seq/If/Call/Ret/DeadEnd/Loop; the
  W5c frame-carrying formulation, no inFragment predicate).
- `frameDelta` + any frame-algebra spec helpers the proofs need
  (`frame_append` exists already).
- `structural_decreases` throughout; decide guards pinning kernel computation
  on a small concrete St/oracle instance (the W6b guard pattern), so a
  kernel-inert regression is caught at crate-verify time.

No soundness proofs on this card — spec fns + guards only, so the churn commit
stays reviewable.

**Done when:** tactus-core verifies `--lean-backend --lean-all-proofs` with 0
errors, axiom closures kernel-verified, decide guards pass, `out/lib`
regenerated, and the existing probe suite (probe9 16/16, probe17, probe21–26
runners) still passes against the regenerated emission.

**Blocked by:** bootstrap-60 (frozen shape).
