---
title: "W2a — reference WP worker (wpStm/frameAfter/goal_eq) in tactus-core"
status: done
claimed_by: opus-n3c
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T00:40:00Z
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

## Progress

- (2026-07-14, opus-n3c) **AUTHORED + VERIFIED.** `tactus-core/lib.rs` now
  carries the full reference-WP family; package gate `30 verified, 0 errors`
  (lean-only-clean). Canonical check:
  `TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus
  --crate-type=lib --lean-backend --lean-all-proofs lib.rs`.

## Writeup

### What landed (tactus-core/lib.rs)

The DESIGN §2.2 equations, as single-datatype structural spec fns (snake_case;
DESIGN names in parens):

- `close(frame, oblig)` — folds a `FrameList` around one obligation leaf.
  First (outermost) frame entry = outermost `GoalData` constructor. FBind→All,
  FHyp→Imp, FLet→Let, FNil→Leaf.
- `frame_append`, `hyps_of_leaves`, `binders_to_frame`, `close_each`,
  `goals_append` — the plumbing (`++`, list→frame conversions).
- `frame_after` (`frameAfter`) — the frame extension seen by what FOLLOWS a
  stm. Assert/Assume→+FHyp, Assign→+FLet, Call→+FBind(dest)+enss-hyps,
  Loop→+binders+invs-hyps+¬cond, DeadEnd/Ret/If/Skip→unchanged, Seq→compose.
- `wp_stm` (`wpStm`) — goals of a stm given the frame before it. Assert emits
  `close`; Ret/Call emit `close_each`; If splits under cond/¬cond; Loop emits
  init ++ body ++ maintain-re-close; Seq threads `frame_after`.
- `seed_params` / `seed_frame` / `ref_wp` (`refWp`) — seed the frame from the
  signature (typ-params, then value params interleaved with bound-hyps, then
  reqs), then `wp_stm` the body.
- `goal_eq` / `goals_eq` — STRICT structural equality for the `decide` bridge,
  plus projection accessors (`gd_tag`, `gd_leaf_id`, …, `gd_child`, `gl_tag`,
  `gl_head`, `gl_tail`).
- In-crate `decide` examples: `probe_*` (graded reduction coverage),
  `ref_wp_seed_and_assert`, `ref_wp_seq_threads_frame`, `goal_eq_strictness`
  (mutation sensitivity — DESIGN §2.4.2).

### §5 open questions — empirical answers (from bootstrap-fixture/out/lib/cert/)

- **§5.1 post-If continuation:** UNRESOLVED for a *mid-Seq* If, because none of
  the fixtures actually contain one. In `max_u64` the frontend ABSORBS the `if`
  into the returned-value rendering (leaf 7 = `x<y → (let r := let m := y; …)`)
  before the SST snapshot, so the If never appears as an SST node. refWp's
  stage-A choice (`frame_after(If)=frame`; continuation sees the pre-if frame)
  is thus authored but untested against production. Needs a fixture fn with a
  genuine post-if continuation (recorded for W3).
- **§5.2 fall-through postcondition:** the serializer emits an explicit
  `StmData::Ret(enss)` node — ALL three fixtures end in `Ret`. So refWp does
  NOT synthesize a fall-through Ret (it walks the explicit one). BUT `sum_to`
  production prepends `Let 39 7` (`let r := acc`) before the postcondition
  leaf — production binds the return value as a frame let (finding-4 / open-Q2
  `return_var`). refWp does not add this yet.
- **§5.3 loop-body post:** WALKER-SYNTHESISED, confirmed. Init/maintain/decrease
  invariant obligations are NOT distinct SST Assert nodes; they are synthesised
  from `Loop.invs` (sum_to goals 0-3 init / 4-5 body-asserts / 6-9 maintain /
  10 decrease / 11 postcondition). refWp synthesises init+maintain identically.
- **§5.4 overflow-guard asserts:** SERIALIZED POST-INJECTION, confirmed. They
  are real SST `Assert` nodes at the snapshot (add_capped Assert 8/13; sum_to
  Assert 13/15). refWp just folds them — no injection mirror needed.

### Additional findings (the crux for W2b — bridges do NOT close yet)

Under the CURRENT serializer output, refWp will NOT `goals_eq`-close any fixture
bridge. Not a refWp bug — an unfaithful-literal problem. The strict checker
(kept deliberately strict) makes each gap visible; the fix is a faithful
serializer, NOT a lax comparison:

1. **Obligation-annotation gap (dominant).** Production renders every
   *obligation* leaf with a `/- @rust:file:line -/` source annotation — a
   DISTINCT interned leaf — while the SST statement carries the BARE prop leaf.
   add_capped `Assert 8` → production `Leaf 15`; sum_to inv `10` → `Leaf 17`.
   refWp emits the bare id. Fix: the serializer must carry the annotated
   obligation leaf on Assert/Loop-inv/Ret (an Assert then needs BOTH a bare
   forward-hyp leaf and an annotated obligation leaf).
2. **Hyp-name gap.** Bound-hyps and requires render as NAMED ∀-binders
   (`All 19 2` = `∀ (h_x_bound : 0≤x∧x<2^64)`), not arrows. FnCtxData carries
   only the prop leaf (`ParamBoundList::Bound(2)`, `reqs: LeafList`), not the
   name leaf (19/18/17/16). refWp emits anonymous `FHyp`→`Imp`. Fix (N2.1-round-
   2): `ParamBoundList` carries `(name_leaf, prop_leaf)`; `reqs` becomes a
   `BinderList`. Then seed_params switches those FHyp→FBind.
3. **Loop-binder gap.** SST `Loop.binders = Nil` (the modified-var havoc set is
   not populated at the raw snapshot — N3a `modified_vars = None`). Production's
   maintain/use telescopes quantify over i, acc + their bound hyps + invariants-
   as-hyps + cond/¬cond + a `_tactus_d_old` decreases-let. refWp can't
   reconstruct this from Nil. Fix: serializer populates `Loop.binders` (body
   Assign dests + bound hyps) and adds a decreases leaf + d_old let.
4. **Ret return-binding.** (see §5.2) production binds the return value as a
   frame let before the fall-through postcondition; refWp does not.

### Backend gotchas discovered (cost real iterations — pin for the next session)

5. **`bool` spec fns → noncomputable `Prop`.** A `bool`-returning spec fn lowers
   to a NONCOMPUTABLE Lean `Prop` def; `Decidable (goal_eq a b)` then resolves
   to `Classical.propDecidable` and `decide` gets STUCK on `Classical.choice`.
   Equality checkers therefore return `nat` (1/0). The W2b bridge line is
   `goals_eq (refWp …) production = 1 := by decide`, NOT `= true` (DESIGN §2.3
   sketch superseded). `if Int-eq` itself DOES reduce (probe confirmed).
6. **Nested `match a { … match b … }` emits ambiguously.** The tactus Lean
   backend flattens to one line; later OUTER arms bind past the inner match's
   wildcard → "redundant alternative". A tuple `match (a,b)` fixes emission but
   BREAKS structural-recursion inference (`t1.deref` no longer a subterm of
   `a`). Resolution: match the first arg ALONE (structural + unambiguous) and
   read the second through non-recursive PROJECTION accessors (nat tag + field
   getters), keeping every arm body a chain of `if`s.

### Assumptions / scope

- refWp is authored to the shape the CURRENT mirror types allow; signature
  hyps as anonymous `FHyp` pending finding-2. `If` `frame_after` = unchanged
  (stage-A join-not-merged) pending a real fixture (§5.1).
- STRICT `goal_eq` is a deliberate design choice: keep the TCB honest, let W3
  surface divergences. Making it lax to close bridges would be this project's
  `assume(false)`.
- Bridges closing + mutation-kill (DESIGN §2.4.1/.2) are W2b (bootstrap-07),
  gated on the serializer-faithfulness amendments (findings 1-4) — see the new
  prereq task.
