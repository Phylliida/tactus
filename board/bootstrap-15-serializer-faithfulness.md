---
title: "W2b-prereq — serializer faithfulness (annotated obligations, hyp names, loop binders) so bridges CAN close"
status: in_progress
claimed_by: opus-w2b-f3
created: 2026-07-14T00:45:00Z
updated: 2026-07-14T06:30:00Z
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

- (2026-07-14, opus-w2b-f2) **BATCHED REGEN DONE — the full add_capped bridge
  CLOSES by `decide` (all 4 goals). 🐉 mission accomplished for add_capped.**
  - vargo release build of the verus fork picked up all four findings'
    serializer changes (rust_verify+verus rebuilt; vstd re-verified 1530/0).
  - Re-emitted fixtures (`--tactus-emit-cert`): **20 verified / 0 errors, 11/16
    certified** (5 rejected `call` = documented stage-A exclusion; unchanged).
  - Fresh `add_capped.cert` (leaf renumbered, count still 24):
    `Ret (LeafList.Cons 12) (RetBind.RetLet 13 16)` — annotated postcondition
    leaf 12 (`/- @rust:…85:13 -/ r = x + y`) + return binding `let r(13):=s(16)`;
    goal 3 tail = `… Let 16 23, Let 13 16, Leaf 12`. ctx shows finding-2's named
    binders + BinderList reqs; body shows finding-1's `Assert 15 14`.
  - **Hand-run (LEAN_PATH = prelude-cache + tactus-core/out/lib):**
    `goals_eq (ref_wp cert_add_capped_ctx cert_add_capped_sst)
    cert_add_capped_goals = 1 := by decide` **PASSES (exit 0).**
  - **Negative controls (mutation-kill, proving it's real):** flipping the RHS to
    `= 0` → `decide` errors; mutating the SST `RetBind.RetLet 13 16`→`13 99` →
    `decide` errors (`goals_eq` becomes 0). The return-binding value is
    load-bearing; a serializer mismatch fails the bridge, never silent-passes.
  - **max_u64 (branch-in-leaf caveat, as noted): HONEST FAILURE.** Its cert emits
    a well-formed `Ret ([9,10]) (RetLet 11 12)`, but production's ensures goals
    are the LIFTED-IF leaves 13/14 (`x<y → (let r := let m := y; m; …)` — the
    `let r` absorbed INSIDE the leaf by `lift_if_value`), so refWp ≠ production
    and the bridge `decide`s to 0. Confirms fail-loud: divergence → no close,
    never a silent pass. (sum_to also won't close yet — needs finding-3.)
  - Refreshed golden `testdata/add_capped.cert.lean` (`leaf_texts.len()` still
    24 — no assertion change). 6 serializer tests + tactus-core 32/0 green.
    `bootstrap-fixture/out` stays gitignored/regenerable.

  **REMAINING FOR THIS TASK'S "done when" = finding-3 (loop binders), the
  largest.** sum_to's Loop node still carries `binders = Nil` + no annotated
  inv-obligation leaves / decreases / `_tactus_d_old` let (N3a `modified_vars =
  None`). Its bridge will NOT close until refWp's maintain/use telescopes match
  production's loop-modified-local havoc set. See finding-3 detail in the task
  Description + DESIGN-W2-refwp.md §5(3). Findings 1/2/4 + Ret-annotation are all
  LANDED, VERIFIED, and demonstrated (add_capped). Next instance: finding-3.

- (2026-07-14, opus-w2b-f3) **finding-3 SPEC SIDE LANDED + VERIFIED (36/0) —
  the FULL sum_to loop bridge closes by `decide` against the real cert's 12
  production goals, mutation-kill confirmed. Serializer side is the one
  remaining step (recipe below).**

  **Ground truth (from `bootstrap-fixture/out/lib/cert/sum_to.cert.lean` — its
  leaf TABLE + 12 `cert_sum_to_goals` are unchanged by finding-3; only the SST
  Loop node's field layout changes).** Decoded production's `walk_loop` +
  `push_mod_var_frames` (havoc) + `split_leading_binders` (leading Binder/Hyp
  frames hoist to NAMED ∀, extraction STOPS at first Let) + `lex_decrease_
  obligation`. The maintain telescope is NOT `f ++ …`; it HAVOCS the pre-loop
  `let i:=0, let acc:=0` (modified locals) then re-quantifies i,acc as ∀ +
  re-asserts each invariant/cond as NAMED `_h_ctx_N` ∀, then a `_tactus_d_old`
  let. Init closes under the ACTUAL pre-loop frame (lets intact).

  **Spec changes (tactus-core/lib.rs, VERIFIED 36/0 under the package gate):**
  - `StmData::Loop` reshaped (10 fields): `inv_hyps: BinderList` (invariants as
    (_h_ctx name, ANNOTATED obligation leaf) — the annotated leaf serves BOTH
    the init/maintain obligation AND the ∀-hyp, unlike Assert's bare/annotated
    split), `binders: BinderList` (mod-local havoc set), `binder_bounds:
    ParamBoundList` (mod-locals' `_h_ctx` type-bound hyps, parallel to binders),
    `cond_name`/`cond_ann`/`neg_cond_ann`, `d_old_name`/`d_old_val`,
    `decrease_oblig`. Replaces old `{invs, cond, neg_cond, binders}`.
  - `wp_stm` Loop: `havoc_lets(f, binders)` drops pre-loop lets for mod locals →
    `seed_params(binders, binder_bounds)` (reused! interleaves ∀mv + ∀bound) →
    `binders_to_frame(inv_hyps)` → `FBind(cond_name, cond_ann)` → `FLet(d_old)`.
    Emits `init ++ body ++ maintain-reclose ++ decrease` (walker-synthesised
    body-end obligations, DESIGN §5 Q3). `close_each_binderprop` closes over a
    BinderList's PROP slots.
  - `frame_after` Loop (use telescope): havoc + seed_params + inv_hyps +
    `FBind(cond_name, neg_cond_ann)` — NO d_old.
  - New helpers: `binder_has_id` (returns **nat** 1/0, NOT bool — a bool spec fn
    lowers to a noncomputable Prop and `decide` gets stuck; this bit me, cost
    one gate cycle), `havoc_lets`, `close_each_binderprop`. `seed_params` moved
    ahead of frame_after/wp_stm (both use it now).
  - **HAVOC CAVEAT (documented, sound):** `havoc_lets` drops FLet for mod-local
    ids but KEEPS FHyp (leaves are opaque — refWp can't tell if a hyp mentions a
    mod var; production's `push_mod_var_frames` DOES drop such hyps). Only bites
    a fixture with a pre-loop assert OVER a modified local → honest fail-to-
    close, never silent-pass (`goals_eq` is structural). sum_to has none.
  - `stm_size` Loop arm: `1 + binder_len(inv_hyps) + binder_len(binders) +
    stm_size(body)` — binder_bounds (a ParamBoundList) is NOT counted, matching
    the serializer's `stm_size_of` token sum (counts LeafList/BinderList Cons +
    stmt heads only). So sum_to's `stm_size` example auto-recomputes 23→25 at
    regen (binders goes Nil→2); no manual sync.
  - NEW `decide` test `ref_wp_sum_to_loop`: reconstructs sum_to's ctx + SST (new
    Loop shape, cert leaf ids) and asserts `goals_eq(ref_wp …, <all 12 goals>)
    == 1`. Goals were machine-generated (balanced-paren script) + parsed back
    and diffed against a standalone Python refWp model — both match the cert
    verbatim. Mutation-kill: perturbing SST `decrease_oblig: 39→99` flips the
    gate to 35v/1err.

  **SERIALIZER RECIPE (the one remaining step — needs a vargo rebuild to test
  end-to-end; write it WITH the regen loop so `_h_ctx` names + the decrease-
  obligation text can be validated against production iteratively):**

  1. **⚠ Do NOT read `StmX::Loop.modified_vars` — production IGNORES it.**
     `build_wp` spells it `_` (sst_to_lean.rs:5084); `build_wp_loop` RE-DERIVES
     the havoc set via `collect_modifications(body)` (:6014-6017) + type lookup
     `ctx.type_map.get(id)`. The current serializer's `binder_entries` reads the
     (None at this SST stage) `modified_vars` HavocSet → that's why binders=Nil.
     FIX: make `collect_modifications` `pub(crate)` (it's private at :6192) and
     call it; build a `VarIdent→Typ` map from `fn_sst.x.pars` + `check.local_
     decls` for the types. MUST match production's mod-var ORDER (collect_
     modifications = body traversal order; sum_to = [i, acc]).
  2. **`_h_ctx_N` counter (shared, matters — `goal_eq` compares binder-name
     ids!):** mirror `split_leading_binders` (:1510). counter=0; for each mod
     var: if `type_bound_predicate(&LExpr::var(from_var_ident(vid)), typ)` is
     Some → bound name = `_h_ctx_{counter}`, counter++ (NoBound → no incr); then
     each standard invariant → `_h_ctx_{counter}`, counter++; then cond →
     `_h_ctx_{counter}`. (Mod-var bounds use `LExpr::var(name)` — NO deref,
     unlike params — per walk_loop:2532.) Distinct from params' `h_x_bound`.
  3. **inv_hyps:** per standard invariant, `(text_leaf("_h_ctx_N"),
     oblig_leaf(&li.inv))`. `oblig_leaf` already byte-matches production's
     span_mark'd `LoopInvariant` leaf (kind never reaches pp → Plain is safe).
     This REPLACES the current bare `inv_leaves`/`inv_list`.
  4. **cond_ann = `oblig_leaf(cond_exp)`** (matches `cond_marked` = span_mark
     over cond, walk_loop:2390); **neg_cond_ann** = a NEW helper interning
     `pp(LExpr::not(span_mark(loc, span, _, inner)))` (production's
     `LExpr::not(cond_marked)`, :2476). cond_name = `text_leaf("_h_ctx_N")`.
  5. **d_old:** bind `id` + `decrease` in the `StmX::Loop` match (currently
     `..`). Error on `decrease.len() != 1` (stage-A single-level, like the
     nonstandard-invariant guard). `d_old_name = text_leaf(&format!("_tactus_
     d_old_{}_0", id))` (build_wp_loop:6002). `d_old_val = exp_leaf(&decrease[0])`
     (= production's `lower_validated(&level.value)`, the maintain d_old let).
  6. **decrease_oblig:** reconstruct `lex_decrease_obligation` single-level
     (:6160) then span_mark it (:6084). inner = `LExpr::and(LExpr::le(LExpr::
     lit_int("0"), cur), LExpr::lt(cur, old))` with `cur = sst_exp_to_ast_
     checked(&decrease[0])`, `old = LExpr::var_synthetic(format!("_tactus_d_old_
     {}_0", id))`; then `span_mark(format_rust_loc(&decrease[0].span),
     Some(decrease[0].span.clone()), Obligation(LoopDecrease-or-Plain), inner)`,
     intern its pp. (All LExpr builders — le/lt/and/not/var_synthetic/lit_int/
     span_mark — are in lean_ast.rs and already reachable.)
  7. Emit `StmData.Loop <inv_hyps> <binders> <binder_bounds> <cond_name>
     <cond_ann> <neg_cond_ann> <d_old_name> <d_old_val> <decrease_oblig>
     <body>` (positional order = the amended `enum StmData.Loop` in the emitted
     `tactus-core/out/lib` defs). `binder_list`/`param_bound_list` builders
     already exist. `stm_size_of` needs NO change (already counts BinderList
     Cons generically).
  8. **Regen + validate:** vargo release build the verus fork (FORK vargo on
     PATH), re-emit fixtures (`--tactus-emit-cert`), confirm sum_to.cert's Loop
     now carries the populated fields, refresh any golden, then hand-run
     `goals_eq (ref_wp cert_sum_to_ctx cert_sum_to_sst) cert_sum_to_goals = 1
     := by decide` (LEAN_PATH = prelude-cache + tactus-core/out/lib). Negative
     control: mutate a d_old/decrease leaf → decide errors. find_square (nested
     loops) is a stretch goal — likely needs multi-level decrease + the nested-
     loop `_h_ctx` counter across two loops; keep it a documented stage-A caveat
     if it doesn't close.

## Writeup

_when done: findings, how the code works, assumptions made_
