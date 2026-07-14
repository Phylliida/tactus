---
title: "W2b-prereq — serializer faithfulness (annotated obligations, hyp names, loop binders) so bridges CAN close"
status: in_progress
claimed_by: opus-w2b-f2
created: 2026-07-14T00:45:00Z
updated: 2026-07-14T04:30:00Z
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

- (2026-07-14, opus-w2b-f1) **finding-1 ASSERT SPLIT LANDED across spec +
  serializer; serializer VALIDATED (lean_verify 320+7/0), spec side coded but
  pending the combined Lean regen.** Decision recorded: rather than regen for
  finding-2 alone then regen again for finding-1 (two heavy vargo rebuilds),
  BATCH the datatype changes (task note: "Plan the datatype changes together —
  base-hash invalidation") so ONE combined regen closes finding-2 + finding-1.

  **What changed (code):**
  - `tactus-core/lib.rs`: `StmData::Assert(u64)` → `StmData::Assert(u64, u64)`
    = `Assert(oblig, hyp)`. `wp_stm` reads the ANNOTATED obligation leaf for
    the goal (`close(f, oblig)`); `frame_after` adds the BARE prop leaf as the
    forward hyp (`FHyp(hyp)`). `stm_size` unchanged (head = 1). All `decide`
    literals migrated to 2-arg; `ref_wp_add_capped_seed_spine` now
    `Assert(15, 8)` (annotated 15 / bare 8) and still expects `…(Leaf 15)`.
  - `source/lean_verify/src/sst_serialize.rs`: new `oblig_leaf(e)` — rebuilds
    production's obligation leaf via the SAME path
    (`sst_exp_to_ast_checked` → `LExpr::span_mark(format_rust_loc(&e.span),
    …, Plain, inner)` → `pp_expr`), so its interned text is byte-identical to
    the goal-side leaf (`goal_data` interns production's own `SpanMark` the
    same way) and the two cancel across the bridge. Assert arm emits
    `Assert <oblig> <hyp>` (bare interned first to keep body pre-order).
    Verified against production: `walk_obligations` (sst_to_lean.rs:1907-1936)
    renders `cond_ast` ONCE and uses it span_mark'd for the goal, bare for the
    Hyp frame; `lean_pp` (:899-909) emits only `/- @rust:<loc> -/ ` + inner
    (kind/rust_span do NOT reach the text → `Plain` is byte-safe).

  **Hand-verified this closes add_capped goals 0/1/2 (asserts) after regen:**
  goal 0 = `close(seed, 15)` = `∀0 1,∀19 2,∀3 1,∀18 4,∀17 5,∀16 6, Leaf 15` ✓;
  goal 1 (tmp__1) = `…Imp 8, Imp 8, Let 9 10, Let 11 12, Leaf 20` ✓ (the two
  `Imp 8` are the Assert(15,8) bare-hyp + the following `Assume 8`); goal 2 ✓.

  **Why the FULL add_capped bridge is not closable yet (goal 3 = postcondition):**
  production goal 3 ends `… Let 9 14, Let 23 9, Leaf 22`. Two more findings:
  1. Ret must carry ANNOTATED ensures leaves (Leaf 22 = `/- @rust:…85:13 -/
     r = x + y`, not bare 7). SERIALIZER-ONLY (no datatype change): thread a
     second, span_mark'd ens list (via `oblig_leaf` over `check.post_condition
     .ens_exps`, loc = `ens.span`) into the `Return` arm — mirror of
     WpCtx::new's postcondition SpanMark (sst_to_lean.rs:529-564). Leave
     `FnCtxData.enss` bare (refWp doesn't read it).
  2. finding-4 return-binding: the `Let 23 9` = `let r := s`. Source located:
     `check.post_condition.dest` (the return var, sst_to_lean.rs:519 `ret_name`)
     + `ret_typ` (:524); the walker writes `Done(let ret := e; ensures_goal)`
     (:311, doc :57 `… let dest := ret;`). refWp needs a `FnCtxData.return_var`
     (name leaf + value leaf) that `ref_wp`'s Ret prepends as an `FLet` before
     the postcondition. `9` here = the returned local `s` (last `Assign 9 …`
     dest), so the "value" is the ret expression rendered at the return site —
     confirm empirically whether it's `post_condition.dest`'s bound value or
     the fall-through body value before adding the field (task note: avoid
     churn). This is the ONE remaining piece for add_capped's full bridge.

  Then finding-3 (loops, for sum_to): Loop needs annotated inv-obligation
  leaves (init/maintain goals) separate from the bare inv-hyp leaves, PLUS the
  populated binders + decreases leaf + `_tactus_d_old` let. Largest; do last.

  **Batched-regen recipe (does finding-2 + finding-1 at once):**
  1. FORK vargo on PATH (`tactus-bootstrap/tools/vargo/target/release`), from
     `source/`: `vargo build --release …` to refresh the verus binary with the
     new serializer.
  2. Re-emit fixtures: `--lean-backend --emit-lean --lean-all-proofs
     --tactus-emit-cert` over `bootstrap-fixture/lib.rs`. Confirm add_capped's
     cert now shows `StmData.Assert <oblig> <hyp>` and `ParamBoundList.Bound
     <hname> <prop>` (finding-2). NB the ENTIRE leaf table renumbers — finding-2
     interns `h_x_bound` early in the param walk, so the goal-side hnames (old
     19/18/17/16) collapse to low ids. Cannot hand-author the golden.
  3. Verify `tactus-core/lib.rs` (package gate, ~30+ verified) — the spec
     change is coded but has NOT run through Lean yet.
  4. Refresh golden `source/lean_verify/src/testdata/add_capped.cert.lean` from
     the real emission + fix `assert_eq!(leaf_texts.len(), …)` in
     sst_serialize_tests.rs (id count changes). Re-run N3 acceptance
     (golden/determinism/verdict-neutral) + hand-run the add_capped goals-0/1/2
     bridge (`goals_eq (ref_wp ctx sst) prod_prefix = 1 := by decide`).

  Landed at code level; NOT yet Lean-verified end-to-end (needs the regen).

- (2026-07-14, opus-w2b-f2) **finding-4 (return binding) + Ret-annotation
  LANDED across spec + serializer; spec side PROVEN + verified (32/0), serializer
  compiles + all 320 lib tests pass.** With finding-1/2 already coded, this makes
  ALL FOUR add_capped findings code-complete → the batched regen can close the
  ENTIRE add_capped bridge (goals 0/1/2/3) in one go, per Danielle's option (b).

  **What changed (spec, tactus-core/lib.rs):**
  - NEW `RetBind` enum: `RetNone | RetLet(u64 name, u64 val)` (a small
    non-recursive datatype — chosen over reusing `FrameList` for exhaustive,
    audit-in-one-sitting valid states in the trusted SST literal; the local
    model concurred).
  - `StmData::Ret(Box<LeafList>)` → `Ret(Box<LeafList>, RetBind)`: the LeafList
    now carries ANNOTATED ensures obligation leaves (the `Return` goal), the
    RetBind the return-value `let`.
  - NEW top-level `ret_frame(f, rb)` = `f` extended by `FLet(name,val,FNil)` for
    RetLet, `f` for RetNone. Factored OUT of `wp_stm`'s Ret arm (NOT a nested
    match) because the decide-checker note (lib.rs §520-528) warns the tactus
    Lean backend flattens an inner match past the enclosing arm's siblings.
  - `wp_stm` Ret arm: `close_each(ret_frame(f, rb), *es)`. `frame_after`/`stm_size`
    Ret arms updated (RetBind adds nothing to size). All `decide` literals migrated.
  - NEW `decide` test `ref_wp_ret_return_binding` isolates it: under a pre-Ret
    frame `FLet(9,14)`, `Ret([22], RetLet(23,9))` closes to
    `Let 9 14 (Let 23 9 (Leaf 22))` = add_capped goal 3's tail EXACTLY; RetNone
    variant closes to `Let 9 14 (Leaf 22)` (no extra let).

  **What changed (serializer, sst_serialize.rs):**
  - `serialize()` interns, up front: the ANNOTATED ensures obligations (via
    `oblig_leaf` — same span_mark path as finding-1's Assert, so the goal-side
    postcondition leaf reuses the id) into `pending_ens_oblig`, and the
    `sanitize(dest)` ret-name leaf into `pending_ret_name` (`None` for unit).
  - The `Return` arm emits `StmData.Ret <annotated-enss> <retbind>`, where
    `retbind = RetLet(nleaf, exp_leaf(ret_exp))` iff BOTH a declared return var
    AND a return expr exist (matching the walker's `let_bind_synthetic` gate),
    else `RetNone`. Value via the SAME `exp_leaf` path Assign rhs uses.
  - `FnCtxData.enss` stays BARE (refWp doesn't read it). `pending_ens` field
    replaced. Module faithfulness-contract doc updated (reads: annotated enss,
    `dest`, `Return.ret_exp`; caveat: coercion/if-lifting NOT replicated →
    honest fail-to-close, never silent-pass).

  **Empirical confirmation (from the on-disk stale cert + production walker):**
  add_capped goal 3 = `… Let 9 14, Let 23 9, Leaf 22`. Verified: production's
  `emit_done_or_split` peels the `Wp::Done(let_bind_synthetic(sanitize("r"),
  <render s>, span_mark'd ensures))` leaf into a `CtxFrame::Let("r", "s")` →
  `GoalSpine::Let` → goal leaf 23=`⟦r⟧`, val leaf 9=`⟦s⟧`, obligation leaf
  22=`⟦/- @rust:…85:13 -/ r = x + y⟧`. The serializer now reproduces all three:
  ret-name "r" via `text_leaf(sanitize("r"))`, value "s" via `exp_leaf(Var s)`
  (== the interned binder id 9), obligation via `oblig_leaf(ens)` (== leaf 22).

  **Remaining = the batched regen (IN PROGRESS this turn):** vargo build of the
  verus fork (running) → re-emit fixtures → refresh golden add_capped.cert.lean +
  `leaf_texts.len()` assertion → hand-run the FULL add_capped bridge
  `goals_eq (ref_wp ctx sst) prod = 1 := by decide` (all 4 goals). tactus-core
  already re-verified (32/0). See updated recipe below.

## Writeup

_when done: findings, how the code works, assumptions made_
