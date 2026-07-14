---
title: "W2b follow-up — head_exec ref-param deref leaf divergence (serializer ensures render)"
status: done
claimed_by: opus-b18
created: 2026-07-14T16:30:00Z
updated: 2026-07-13T22:05:00Z
---

## Description

W2b (bootstrap-07) ran the bridge over ALL 11 fixture certs and found a NEW
honest-fail: `head_exec` (`fn head_exec(t: &Tree) -> u64 ensures r ==
tree_head(*t)`). Its bridge `goals_eq (ref_wp ctx sst) goals = 1` is FALSE — a
documented, sound honest-fail (stage A does not certify leaf rendering, §2.5),
but a real serializer faithfulness gap worth closing so `head_exec` bridges.

**Root cause (pinpoint-proved in probe-w0/probe9_bridge/REPORT.md).** The sole
divergence is the postcondition obligation leaf:

- Serializer `oblig_leaf` over `check.post_condition.ens_exps` uses an EMPTY
  `RenderCtx`, so `*t` (deref of the `&Tree` param) renders as bare `t` →
  SST ens leaf `⟦/- @rust:…196:13 -/ r = lib.tree_head t⟧`.
- Production's postcondition rendering renders `*t` → `t.deref` → goal leaf
  `⟦/- @rust:…196:13 -/ r = lib.tree_head t.deref⟧`.

`goals_eq refWp (production-goals with leaf6→leaf3) = 1` confirms the obligation
leaf (3 vs 6) is the ONLY difference; the telescope, let-chain, and RetBind all
match. So this is a pure leaf-rendering (RenderCtx-subst) gap, NOT a shape/refWp
bug. It is the reference-parameter sibling of finding-4's documented
"empty-RenderCtx does not replicate a coercion/subst → honest fail" caveat.

## Approach sketch

- Find where production's postcondition render inserts `.deref` for `&`-params
  (the `WpCtx` postcondition `RenderCtx` — likely a `value_subst` mapping the
  param `VarIdent` to its deref form, or a deref-on-ref-param pass in
  `lower_validated`/`sst_exp_to_ast_checked`). `sst_to_lean.rs` around
  `WpCtx::new`'s postcondition SpanMark (:519-564) and the param-binder deref
  handling in `build_param_binders` (:4138) are the leads.
- Make the serializer's `oblig_leaf` for the ensures use the SAME subst (thread
  the same RenderCtx production uses for the postcondition, rather than an empty
  one) so `*t` interns to `t.deref` and the leaves cancel.
- CAREFUL: this touches the trusted `oblig_leaf` path — keep the change a
  faithful mirror of production's render, not a bespoke deref hack. Any
  divergence still honest-fails (probe9 will show it), never silent-passes.
- Validate: regen fixtures, re-run `probe-w0/probe9_bridge/run.sh` — head_exec
  should move CLOSE → move it out of the runner's `honest_fail_reason` set. A
  negative control (mutate the deref leaf) must still flip.

**Scope note.** This is a stage-B-adjacent leaf-rendering fix. It is NOT a
blocker for W3 (the differential gate happily reports head_exec as a triaged
serializer divergence). Low priority relative to W3/N3-Call, but small and
well-isolated. Consider batching with any other RenderCtx-subst faithfulness
gaps W3 surfaces on tgt.

## Second site (batched here — found by W3, board bootstrap-08, 2026-07-14)

W3's differential gate over tgt found a SECOND instance of this exact class at a
DIFFERENT leaf-render site. `runtime::impl__4::clone`
(`fn clone(self: &RuntimeSymbol)`): the serializer renders the **RetBind value**
(the `let _return := *self` return-var binding) as bare `self` (leaf 0), while
production renders `self.deref` (leaf 5). Pinpoint-proved
(`probe-w0/probe11_w3_tgt/Pinpoint.lean`) it is the SOLE divergence of that
bridge. So the `*p → p.deref` `&`-param subst is missed at TWO leaf-render
sites, not one:

1. **obligation / ensures leaf** — `oblig_leaf` over `ens_exps` (head_exec, the
   original finding above).
2. **RetBind value leaf** — the return-var `let` binding (`clone`, this site).

**Both must be fixed together.** The fix should thread production's postcondition
RenderCtx (the one that maps a `&`-param `VarIdent` to its `.deref` form) through
BOTH render paths, not just `oblig_leaf`. A single deref-subst RenderCtx applied
consistently at every ensures/return leaf-render site closes both `head_exec`
and `clone`. Validate by moving BOTH out of their runners' `honest_fail_reason`
sets (`probe9_bridge` for head_exec, `probe11_w3_tgt` for clone) and confirming
a negative-control mutation still flips.

## Progress

- (2026-07-13, opus-b18) **Root-caused to the exact production mechanism and
  implemented the fix (both sites) in `sst_serialize.rs`. Build + bridge
  validation in progress.**

  **The mechanism (confirmed from source, not archaeology).** Production renders
  the postcondition ensures via
  `lower_validated_with_ctx(&Validated::check(&rewritten), &render_ctx)`
  (`sst_to_lean.rs:567`), where `render_ctx =
  RenderCtx::with_fn_map(&fn_map).with_binder_typs(&caller_param_typs)`
  (`:511`). `lower_validated_with_ctx == to_lean_sst_expr::lower_with_ctx`, whose
  body is literally `sst_exp_to_ast_checked_with_ctx(v.inner, ctx)` (`:145`) —
  the SAME lowering the serializer's `oblig_leaf` already calls, just with an
  EMPTY ctx (`sst_exp_to_ast_checked` = `_with_ctx(e, RenderCtx::empty())`).
  The `.with_binder_typs(&caller_param_typs)` is what makes a `&`-param `*p`
  render as `p.deref` (the binder-typ map says `p : &T`, so the ReadPlace lift
  derefs). `caller_param_typs` is a trivial map (`sst_to_lean.rs:930`): strip one
  ref decoration for `&mut`, else as-declared.

  **Why the fix is provably safe (no fixture regression).** The 9 fixtures that
  currently CLOSE match production's goal leaves using the serializer's EMPTY
  ctx. Production renders those SAME postconditions with
  `with_binder_typs(&caller_param_typs)`. They match ⇒ for those fns
  `with_binder_typs == empty` (no `&`-param deref to insert). So switching the
  serializer to the binder-typ ctx keeps the 9 matching AND fixes head_exec +
  clone (whose `&`-params DO deref). fn_map is NOT threaded (trait-dispatch
  coercion) → any residual divergence still HONEST-FAILS, never silent-passes.

  **Edits (all in `source/lean_verify/src/sst_serialize.rs`):**
    1. New `Serializer.caller_param_typs: HashMap<VarIdent, Typ>` field.
    2. Populated in `serialize()` before any leaf render, mirroring
       `sst_to_lean.rs:930` EXACTLY (`is_mut_ref_typ` → `strip_one_ref_decoration`).
    3. New `render_ctx()` helper = `RenderCtx::empty().with_binder_typs(&…)`.
    4. `oblig_leaf` + `neg_oblig_leaf`: `sst_exp_to_ast_checked` →
       `_with_ctx(e, &self.render_ctx())` (fixes head_exec, the obligation-leaf
       site — leaf 3→6 now cancels).
    5. RetBind value (the `StmX::Return` arm): render via `_with_ctx` in a
       scoped block so the ctx `&self` borrow ends before `intern` takes
       `&mut self` (fixes clone, the RetBind-value site — leaf 0→5 now cancels).
    6. Module-doc caveats updated: obligation + RetBind leaves now use the
       binder-aware ctx; the remaining caveat narrows to fn_map coercion +
       return-TYP coercion + if-value lifting.

  **Validation (in flight):** incremental `vargo build --release` (FORK vargo)
  running; then regen the fixture certs (`--tactus-emit-cert` over
  bootstrap-fixture) + the tgt clone cert (probe11 cold-emit recipe), then run
  `probe9_bridge/run.sh` (head_exec should flip HONEST-FAIL → the runner will
  flag it as LAX-REGRESS, i.e. the fix landed) and `probe11_w3_tgt/run.sh`
  (clone likewise). Then reclassify BOTH out of the runners' `honest_fail_reason`
  sets (they become expected-CLOSE) + confirm a negative-control mutation
  (revert the deref in one leaf) still flips. Not done until those are green.

- (2026-07-13, opus-b18 cont) **BOTH SITES FIXED, VALIDATED, DONE.** Picked up
  the previous instance's in-flight state (render_ctx + fn_map + lifetime `'a`
  already in `sst_serialize.rs`). Rebuilt (fork vargo, clean; vstd 1530/0) and
  regenerated both certs.

  **head_exec (obligation-leaf site) — fixed by the previous instance's
  render_ctx.** New cert: SST obligation leaf 3 renders `r = lib.tree_head
  t.deref` (was bare `t`); it now interns to the SAME id as the production goal
  leaf (old leaf 6 is gone), so `Ret [Leaf 3]` matches goal `... (Leaf 3)`.
  probe9 → head_exec `LAX-REGRESS` (i.e. it CLOSED). All 9 other fixtures still
  `close-ok`, max_u64 still `hfail-ok` on its distinct caveat → binder-ctx is
  provably inert where it should be, no regression.

  **clone (RetBind-value site) — the previous binder_typs approach was NOT
  enough; needed the return-typ coercion.** After the render_ctx change the
  clone cert was UNCHANGED (still `RetLet 4 0`, bare `self`). Root-caused: the
  clone return Exp is a **bare `Var(self) : &RuntimeSymbol`** — there is no
  explicit `*self` in the Exp for `binder_typs` to deref. Production's
  `self.deref` comes from a DIFFERENT mechanism: the per-leaf **return-typ
  coercion** in `lift_if_value_coerced`'s base case (`sst_to_lean.rs:4795/4802`
  → `coerce_leaf` → `coerce_lexpr(render(e), &e.typ, ret_typ)`), which coerces
  the returned value from `&RuntimeSymbol` to the declared `ret_typ`
  `RuntimeSymbol`, peeling one ref → `self.deref`. `binder_typs` (which only
  helps an EXPLICIT `*p` in the Exp) can't reach this.

  **The clone fix (this turn), all in `sst_serialize.rs`:**
    1. New `Serializer.ret_typ: Option<Typ>` field, populated in `serialize()`
       EXACTLY as production's `WpCtx.ret_typ` (`sst_to_lean.rs:524`):
       `check.post_condition.dest` looked up in `local_typs` (= production's
       `type_map` = `check.local_decls`).
    2. The `StmX::Return` arm now applies `crate::expr_shared::coerce_lexpr(
       lexpr, &e.typ, ret_typ)` to the rendered return value (mirroring
       `coerce_leaf`), inside the same scoped block so the `&self` borrows end
       before `intern` takes `&mut self`.
    3. Module-doc caveat narrowed: the RetBind return value now applies the
       return-typ coercion (closes clone); only if-value LIFTING remains
       un-replicated (a genuinely-liftable `if` return still honest-fails).

  New clone cert: `RetLet 4 5` (was `4 0`), binding `_return := leaf 5
  ⟦self.deref⟧`, matching goal `Let 4 5`. probe11 → clone `LAX-REGRESS`
  (CLOSED).

  **Why safe (same argument for both mechanisms):** the closing fixtures match
  production's coerced + binder-aware render using the serializer's OLD
  empty-ctx / un-coerced render ⟺ for them BOTH the coercion and the
  binder-deref are no-ops. So adding them keeps the 9 fixtures closing (verified:
  all still `close-ok`) AND fixes head_exec + clone (whose derefs are
  non-trivial). head_exec's coerce is u64→u64 (no-op); clone's is
  `&RuntimeSymbol`→`RuntimeSymbol` (peels a ref). Any residual divergence still
  HONEST-FAILS (fn_map is not threaded for trait-dispatch coercion; if-value
  lifting is not replicated).

  **Reclassified + re-validated:**
    - Removed head_exec from `probe9_bridge/run.sh` honest_fail set → re-run:
      head_exec `close-ok`, `ALL BRIDGES BEHAVE AS CLASSIFIED ✓`.
    - Removed clone from `probe11_w3_tgt/run.sh` honest_fail set → re-run:
      clone `close-ok`, `ALL TGT BRIDGES BEHAVE AS CLASSIFIED ✓`.
    - **Negative controls both flip:** head_exec with SST obligation leaf
      3→0 (bare t) → `decide` fails (rc≠0); clone with `RetLet 4 5`→`4 0`
      (the exact OLD bug, bare self) → `decide` fails (rc≠0). The bridge
      genuinely requires the deref to match; it is not trivially passing.

  **Scope note.** All edits are confined to the `--tactus-emit-cert` serializer
  path (`emit_cert`→`serialize`, which early-returns when the flag is off), so
  production verification is untouched (vstd 1530/0 on the rebuild). The change
  only affects emitted cert TEXT, not verdicts (`--tactus-emit-cert` is
  verdict-neutral, bootstrap-14).

## Writeup

**Outcome: DONE.** Both `&`-param deref leaf-render divergences are closed and
the two bridge runners are green with both fns reclassified expected-CLOSE.

**The two sites and their two DISTINCT mechanisms (the key finding).** The task
card assumed a single binder-aware `RenderCtx` would close both sites. That is
only half-right — the two sites need two different production mechanisms:

1. **head_exec — obligation/ensures leaf.** The ensures `r == tree_head(*t)`
   has an EXPLICIT `*t` deref in the Exp. Rendering it through the binder-aware
   `render_ctx()` (`with_binder_typs(caller_param_typs)` + `with_fn_map`) — the
   previous instance's change — makes `*t` render as `t.deref`, matching
   production's postcondition leaf. Because the SST obligation and the goal now
   render identically, they intern to the same leaf id and the bridge closes.

2. **clone — RetBind return value.** `fn clone(self: &RuntimeSymbol) ->
   RuntimeSymbol` returns a BARE `Var(self) : &RuntimeSymbol` — there is no
   explicit `*self` in the Exp. `binder_typs` therefore leaves it as bare
   `self`. Production's `self.deref` on the goal side comes instead from the
   per-leaf **return-typ coercion** (`lift_if_value_coerced` base case →
   `coerce_leaf` → `coerce_lexpr(rendered, &e.typ, ret_typ)`), which coerces the
   value from its own Exp typ (`&RuntimeSymbol`) to the declared return typ
   (`RuntimeSymbol`), peeling one ref. This turn added exactly that coercion to
   the serializer's `Return` arm (plus a `ret_typ` field derived identically to
   production's `WpCtx.ret_typ`).

**How the fix works.** The serializer's obligation leaves (`oblig_leaf` /
`neg_oblig_leaf`) and RetBind return value now render through the same
binder-aware ctx production uses, and the RetBind value additionally applies
production's return-typ `coerce_lexpr`. Both are faithful mirrors of production
code (`sst_to_lean.rs` render_ctx at :511 and the coerce at :4795/4802), not
bespoke deref hacks — the same functions production calls, so any case they
don't cover diverges VISIBLY and honest-fails the `decide` bridge rather than
silent-passing.

**Assumptions / residual caveats (unchanged, still honest-fail, never
silent-pass):**
- `fn_map` is threaded but trait-dispatch receiver coercion across crates is
  not resolved (callee not in the map) → those derefs still honest-fail.
- if-value LIFTING is not replicated: a genuinely-liftable `if` return renders
  as one leaf here vs production's lifted `And`/`Imp` structure. (head_exec's
  `let tmp := t; if …` is the UNSAFE-to-lift match-shape, which production ALSO
  renders as a single leaf, so it matches; a liftable `if` return would
  honest-fail.) max_u64 remains a documented honest-fail on this class.

**Validation evidence:** probe9 all `close-ok`/`hfail-ok` (`ALL BRIDGES BEHAVE
AS CLASSIFIED ✓`); probe11 clone `close-ok` (`ALL TGT BRIDGES BEHAVE AS
CLASSIFIED ✓`); both negative-control mutations flip the `= 1` bridge to fail;
verus rebuild clean, vstd 1530/0; fixture emit 20 verified / 11-of-16 certified
(unchanged 5-call rejections); tgt runtime emit 24 verified / 1-of-7 certified
(the clone).

**Follow-on relevance:** this closes the last known `&`-param leaf-render gap
for the current stage-A surface. The two-mechanism finding (explicit-deref via
binder_typs vs bare-value via return-typ coercion) is directly relevant to
bootstrap-02b (N3 `StmData::Call`): callee arg positions will need the SAME
`coerce_lexpr(arg, &arg.typ, callee_param_typ)` bridge that production applies
on the typed-arg path.
