---
title: "W2b-prereq — serializer faithfulness (annotated obligations, hyp names, loop binders) so bridges CAN close"
status: todo
claimed_by:
created: 2026-07-14T00:45:00Z
updated: 2026-07-14T00:45:00Z
---

## Description

W2a (bootstrap-06) authored `refWp`/`wpStm`/`frameAfter`/`goal_eq`/`goals_eq`
and verified them (30 verified, 0 errors). But it discovered that under the
CURRENT serializer output NO fixture bridge closes under strict `goals_eq` —
because the SST literal / FnCtxData the serializer emits is not faithful to
what production actually renders. The equality checker is deliberately STRICT
(keeps the TCB honest); the fix belongs in the serializer/shape, not in a lax
comparison. This task makes the literal faithful so W2b's `by decide` bridges
CAN close.

Findings to fix (full detail in bootstrap-06 writeup + DESIGN-W2-refwp.md §5):

1. **Obligation-annotation gap (dominant).** Production renders every
   OBLIGATION leaf with a `/- @rust:file:line -/` source annotation (a distinct
   interned leaf); the SST statement carries the BARE prop leaf. E.g. add_capped
   `Assert 8` → production `Leaf 15`; sum_to inv `10` → `Leaf 17`. Make the
   serializer carry the annotated obligation leaf on Assert / Loop-inv / Ret.
   NOTE this splits Assert's single leaf into TWO roles: a bare forward-hyp
   leaf (the `Imp e` that Assert;Assume adds) AND an annotated obligation leaf
   (the goal). Likely an N2.1-round-2 shape change: `StmData::Assert(oblig,
   hyp)` (or similar), and refWp's Assert/Loop equations switch to the
   annotated leaf for the goal, bare for the forward hyp.

2. **Hyp-name gap.** Bound-hyps and requires render as NAMED ∀-binders
   (`All 19 2` = `∀ (h_x_bound : …)`), not arrows. FnCtxData carries only the
   prop leaf. Add the name leaf: `ParamBoundList::Bound(name, prop)`; `reqs`
   becomes a `BinderList` of `(name, prop)`. Then flip refWp's `seed_params`
   bound-hyp + reqs emission from `FHyp` to `FBind`.

3. **Loop-binder gap.** SST `Loop.binders = Nil` (modified-var havoc set not
   populated — N3a `modified_vars = None`). Production's maintain/use telescopes
   quantify over the loop-modified locals + their bound hyps + invariants-as-
   hyps + cond/¬cond + a `_tactus_d_old` decreases-let. Populate `Loop.binders`
   from the body's Assign dests (+ bound-hyp leaves), and add a decreases leaf
   (+ the d_old let) so refWp's maintain telescope + decrease obligation match.

4. **Ret return-binding.** Production binds the return value as a frame `let`
   before the fall-through postcondition (sum_to `Let 39 7` = `let r := acc`).
   Either add `FnCtxData.return_var: (name, typ)` (deliberately omitted in N2.1,
   see DESIGN §5 open-Q2) and have refWp's Ret prepend the let, OR confirm the
   serializer can bake it. Decide empirically before adding (avoid churn).

**Careful:** items 1-3 change the frozen literal shape (N2.1) and the N3
serializer. Re-run N3 acceptance (golden files, determinism, verdict-neutral)
after each. Plan the datatype changes together (base-hash invalidation).

**Done when:** the serializer emits annotated obligations, named signature
hyps, and populated loop binders; refWp is re-pointed to the faithful leaves;
at least add_capped + max_u64 (branch-in-leaf caveat noted) bridge lines close
by `decide` on a hand-run. Then bootstrap-07 (W2b) does the batch + mutation
kills.

## Progress

- (2026-07-14, opus-n3c) Created from the W2a empirical read. Recommend
  sequencing: finding-2 (hyp names, smallest, self-contained) → finding-1
  (obligation annotations, dominant) → finding-3 (loop binders, largest) →
  finding-4 (return-binding, confirm-first). Each ends with N3 acceptance green.

## Writeup

_when done: findings, how the code works, assumptions made_
