---
title: "W2b-prereq — serializer faithfulness (annotated obligations, hyp names, loop binders) so bridges CAN close"
status: in_progress
claimed_by: opus-w2b-f2
created: 2026-07-14T00:45:00Z
updated: 2026-07-14T02:00:00Z
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

- (2026-07-14, opus-w2b-f2) **finding-2 (hyp names) LANDED across all three
  layers; spec side PROVEN + verified, serializer side compiles.** End-to-end
  fixture regen is the one remaining (mechanical) step — needs a vargo verus
  rebuild. Details:

  **Ground truth (add_capped.cert.lean goal 0):** the seed telescope is ALL
  named `All` binders — `All 0 1 (All 19 2 (All 3 1 (All 18 4 (All 17 5 (All
  16 6 (Leaf 15))))))` = `∀(x:Int) ∀(h_x_bound:2) ∀(y:Int) ∀(h_y_bound:4)
  ∀(h_req0:5) ∀(h_req1:6), oblig`. Both bound-hyps (names 19/18) AND requires
  (names 17/16 = `h_req0`/`h_req1`) are named ∀, never `Imp`.

  **Production naming (must be mirrored byte-for-byte for interner unify):**
  bound-hyp = `format!("h_{}_bound", name.as_str())` (sst_to_lean.rs:4138,
  build_param_binders); req = `format!("h_req{}", i)` (sst_to_lean.rs:4271,
  build_req_binders). `LeanName::synthetic(s).as_str() == s` (verbatim), and
  the goal-walk interns those via `text_leaf(b.name.as_str())` — so ctx-side
  and goal-side hit the SAME LeafTable and unify to one id.

  **tactus-core/lib.rs (spec side) — verified 31/0 under the package gate:**
  - `ParamBoundList::Bound(u64, Box)` → `Bound(u64 name, u64 prop, Box)`.
  - `FnCtxData.reqs: LeafList` → `reqs: BinderList` (name, prop pairs).
  - `seed_params` Bound arm: `FHyp(prop,…)` → `FBind(hname, prop,…)` (→ `All`).
  - `seed_frame` reqs: `hyps_of_leaves(c.reqs)` → `binders_to_frame(c.reqs)`.
  - `param_bound_len` Bound arm updated; all `decide` literals migrated.
  - NEW `decide` test `ref_wp_add_capped_seed_spine` reproduces production
    goal-0's fully-named telescope EXACTLY (leaf ids 0/1/3/19/18/17/16/2/4/5/6
    /15 from the fixture cert). Isolates finding-2: given the annotated
    obligation (finding-1), the named seed telescope matches verbatim.

  **source/lean_verify/src/sst_serialize.rs (serializer) — cargo check green
  (16s, no new warnings):**
  - `param_bound_list(&[Option<u64>])` → `&[Option<(u64,u64)>]`, emits
    `Bound name prop`.
  - param loop mints `hname = text_leaf(format!("h_{}_bound", name))` alongside
    the prop, pushes `Some((hname, prop))`.
  - reqs walk: `req_leaves: Vec<u64>` → `req_entries: Vec<(u64,u64)>` with
    `hname = text_leaf(format!("h_req{}", i))`; `FnCtxData.mk` emits
    `binder_list(&req_entries)` for the reqs slot (was `leaf_list`).
  - module doc updated.

  **Remaining for finding-2 (mechanical, needs vargo verus rebuild):**
  1. `vargo build` the verus fork so the binary carries the new serializer.
  2. Re-emit the fixture certs (`bootstrap-fixture/`) — confirm add_capped's
     `cert_add_capped_ctx` now shows `ParamBoundList.Bound <hname> 2 …` and a
     `BinderList` reqs slot, and that the seed-spine portion of the bridge
     `goals_eq (refWp ctx) production` closes (finding-1's obligation-leaf gap
     still blocks the FULL add_capped bridge — that's a separate finding).
  3. Refresh the golden `source/lean_verify/src/testdata/add_capped.cert.lean`
     (+ `leaf_texts.len()` assertion in sst_serialize_tests.rs — id count will
     grow by the interned hname leaves) and re-run N3 acceptance
     (golden/determinism/verdict-neutral).
  NB the golden test does NOT re-run `serialize()` (it round-trips the golden
  bytes through `render_cert`), so it did not spuriously fail — but the golden
  + on-disk fixture certs are now semantically STALE until step 2/3.

  NEXT after this: finding-1 (obligation annotations — the dominant gap; the
  Assert node must carry BOTH a bare forward-hyp leaf and an annotated
  obligation leaf), then finding-3 (loop binders), finding-4 (return-binding).

## Writeup

_when done: findings, how the code works, assumptions made_
