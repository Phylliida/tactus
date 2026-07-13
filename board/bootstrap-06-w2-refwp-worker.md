---
title: "W2a — reference WP worker (wpStm/frameAfter/goal_eq) in tactus-core"
status: in_progress
claimed_by: opus-n3c
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T23:55:00Z
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

- (2026-07-13, opus-n3c) **Claimed after closing N3c. Prep + §5 empirical
  answers from the fixture certs already on disk** (`bootstrap-fixture/out/lib/
  cert/*.cert.lean`). Substrate confirmed: the N2.1 mirror types in
  `tactus-core/lib.rs` (`StmData`/`GoalData`/`GoalList`/`FrameList`/`FnCtxData`/
  `LeafList`/`BinderList`/`ParamBoundList`) match `DESIGN-W2-refwp.md` §2.1
  1:1, and the measure/`decide`-sanity scaffolding (`stm_size`, `goal_size`,
  `goal_count`, `frame_len`, `binder_len`, `param_bound_len`, `fnctx_arity`,
  all `#[verifier::structural_decreases]`) is already there. What W2a ADDS:
  `wpStm`/`frameAfter`/`refWp`/`goal_eq`/`goals_eq`.

  **Frame-seed order (from `add_capped`/`max_u64` goal spines):** refWp seeds
  the frame as, per value param, `∀ x, ∀ h_x_bound` — i.e. each param binder
  is IMMEDIATELY followed by its own bound-hyp (NOT all binders then all
  bounds): spine = `∀0(x):1(Int), ∀19(h_x_bound):2, ∀3(y):1, ∀18(h_y_bound):4,
  [∀ req hyps], obligation`. So `refWp`'s seeding interleaves `params` with
  `param_bounds` positionally, then appends `reqs` as `FHyp`s. Matches the
  `FrameList` single-ordered-list design.

  **§5.1 / §5.2 — the CRUX, found in `max_u64`** (`let m = if x<y {y} else {x};
  m`, ensures `r≥x, r≥y`, fall-through return):
  - Stage-A SST literal = a SINGLE `Ret([5,6])` where leaf5=`r≥x`, leaf6=`r≥y`
    (the RAW ensures). The `if` is INVISIBLE in the literal — the frontend
    absorbed it into the return-value rendering before the snapshot.
  - Production goals = TWO, split BY BRANCH not by ensures: goal0 = `∀tele,
    Leaf7` where leaf7 = `x < y → (let r := (let m := y); r≥x ∧ r≥y)`; goal1 =
    the `¬(x<y)` branch (leaf10). Same telescope as refWp would build, but the
    LEAVES differ (5,6 vs 7,10) and the pairing differs (per-ensures vs
    per-branch, both happen to be 2 here).
  - ⇒ A naive `refWp(ctx, Ret[5,6])` emits `∀tele,Leaf5` and `∀tele,Leaf6`,
    which will NOT `goals_eq`-match production's `Leaf7`/`Leaf10` (structural
    on leaf ids). **So `max_u64`'s bridge will NOT close under the obvious
    refWp.** This is the first thing W2a authoring must decide:
    (a) treat if-in-fall-through-return as a documented stage-A leaf/structure
        divergence (bridge intentionally open; §2.5 already disclaims leaf
        rendering) and pick fixture fns without it for the "every bridge
        closes" acceptance; OR
    (b) the `Ret` handling / fall-through must mirror the branch split — but
        the branch data isn't in the literal, so (b) is not achievable at
        stage A. Leaning (a). Confirm against `add_capped` (which DOES close:
        its `Ret([7])` is the single explicit-value ensures and its asserts
        are real SST `Assert` nodes → refWp reproduces exactly).

  **§5.3 / §5.4 — loops (from `sum_to`):** the `Loop` literal has
  **`binders = BinderList.Nil`** (confirms the N3a `modified_vars = None`
  caveat: the havoc set isn't populated at the raw `check.body` snapshot).
  BUT production loop goals carry the full loop-state telescope (binders
  i=5, acc=7 + the four invariant hyps + cond). ⇒ **refWp must RECONSTRUCT the
  loop-state binders itself** (compute the modified set from the loop body's
  `Assign` dests), because the literal doesn't carry them. Init/maintain/use
  obligations ARE walker-synthesized from `Loop.invs` (goals 0-3 init /
  6-9 maintain / 10 decrease / 11 postcondition), NOT distinct SST Assert
  nodes — so refWp synthesizes them identically from the `invs` leaf list.
  User asserts inside the loop body (lib:117/118) ARE present verbatim as SST
  `Assert 13`/`Assert 15` nodes (§5.4: overflow/user asserts serialized
  post-injection, refWp just folds them). The maintain goal's telescope order
  is a concrete target to match: `∀params, ∀i, ∀acc, ∀(4 inv hyps), ∀(cond),
  Let…, Imp13,Imp13, Let5:=14, Imp15,Imp15, Let7:=16, Leaf(inv)`.

  **NOT started:** the actual `wpStm`/`frameAfter`/`refWp` spec fns. That's a
  focused authoring+verification session (single-datatype structural recursion
  over `StmData`, `++` for `Seq`, `#[verifier::structural_decreases]`, in-crate
  `decide` unit examples, verify lean-only-clean via the package gate). Start
  there next, with the crux above resolved first (recommend a `bridge-closes`
  fixture subset that excludes if-in-fall-through, per §2.4.1).

## Writeup

_when done: findings, how the code works, assumptions made_
