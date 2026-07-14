---
title: "W2b follow-up — head_exec ref-param deref leaf divergence (serializer ensures render)"
status: todo
claimed_by:
created: 2026-07-14T16:30:00Z
updated: 2026-07-14T16:30:00Z
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

## Writeup
