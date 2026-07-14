---
title: "W7c-ref — reference def-body transcriber on the VIR ExprX surface (raw_vir_exp)"
status: todo
claimed_by:
created: 2026-07-14T23:20:00Z
updated: 2026-07-14T23:20:00Z
---

## Description

Author the **reference** def-body transcriber as a NEW function on the VIR
`vir::ast::Expr` (`ExprX`) surface — the "independent VIR lowering" DESIGN §2
calls for. This is the corrected long pole of W7c: the surface-fork finding
(`bootstrap-28` Progress, 2026-07-14 opus-w7c-2, Danielle-endorsed) established
that def bodies live on VIR `ExprX` (which keeps `Match`/`Quant`/multi-arg
`Call`), NOT SST `ExpX` (where `Match` is already desugared and the existing
`raw_exp` operates). So the reference cannot reuse SST `raw_exp` for def bodies —
it needs VIR-surface arms.

**Function** (in `source/lean_verify/src/sst_serialize.rs`, next to `raw_exp`):
`raw_vir_exp(&mut self, e: &vir::ast::Expr) -> Sr<String>` emitting `RawExp`
text. Reuse the RawExp emitter infra + `typ_data` (already `&Typ`-typed,
`sst_serialize.rs:588`) + `binop_opcode`/`text_leaf`/`call_fun_id`. Mirror the
VIR-node reading in `to_lean_expr::expr_to_node` / `expr_to_ast`.

**Arms** (census-gated, fail-loud on the rest, like `raw_exp`):
- leaves: `Const(Int/Bool)` → `Lit`/`LitBool`; `Var` → `Var` (intern
  `LeanName::from_var_ident`, matching prod);
- `If(cond, then, Some(else))` → `RawExp::Ite` (carry `e.typ` result type; note
  VIR `If` else is OPTIONAL — else-less `if` fails loud, can't be value pos);
- `Binary(op, l, r)` → `BinOp` (reuse `binop_opcode`);
- `Unary(Clip/..)` / `UnaryOpr(Box/Unbox/HasType/Field)` — mirror `raw_exp`;
- `Call(CallFun::Fun, typs, args)` multi-arg → `RawExp::CallN(fn, ret, arglist)`
  (single-arg stays `Call` for byte-parity? — no, def-body surface is separate
  from obligations; pick CallN uniformly OR match production's currying, §7 Q3);
- `Ctor(dt, variant, fields)` → a ctor RawExp (needs a vocab check — is there a
  `RawExp` ctor node, or does a bare ctor render as `CallN` of the ctor name?);
- `Match(scrutinee, arms)` → `RawExp::MatchR(scrut, RawArmList, ty)`, arms
  INLINED into the frozen `Cons(ctor_id, BinderIdList, body, tail)` list shape
  (W7b landed the inlined list, not the named `MatchArm` type). Binder-id
  discipline (§7 Q1): intern arm-pattern binder ids the SAME way production does
  so `def_eq` agrees. Need the VIR `Match` arm/pattern shape (patterns bind ctor
  fields → positional binder ids).
- `Quant(quant, binders, body)` → `ForallR/ExistsR(bid, bty, body)` — SINGLE
  binder (`bty = typ_data(binder.a)`); multi-binder → nest right-to-left into
  nested `ForallR`, or fail loud (pick, matching how production's multi-binder
  `∀` renders — check `vir_var_binders_to_ast` fold).

**Reachability check** for `Ctor`/`Match`: read the fixture `Tree`/`tree_head`/
`sum_tree` VIR bodies to confirm the exact node shapes (the `bootstrap-fixture`).

**Done when:** `raw_vir_exp` transcribes the fixture spec-fn bodies (`tri` = Ite,
`tree_head`/`sum_tree` = Match, `Tree.height` = recursive Match) → `RawExp`,
unit-tested on hand-built VIR inputs (or a small e2e over the fixture), and its
output `render_exp`s to the SAME `ExprData` the production `lexpr_to_exprdata`
produces for those bodies (co-design the two so `def_eq` agrees by construction).
Dead code (`#[allow(dead_code)]`) until W7d wires the def-body entry point →
verdict-neutral by construction.

**Blocked by:** `bootstrap-27` (W7b vocab, DONE) + the `bootstrap-28` surface
finding. **Blocks:** W7c production arms (`lexpr_to_exprdata` Match/Forall/App —
they must match this side's shapes) and W7d (def emission + bridge).

## Progress
- (2026-07-14, opus-w7c-2) Created from the surface-fork finding. Reference-first
  per Danielle: this defines the target shapes the production arms must match.
- (2026-07-14, opus-w7c-2) **Fixture body analysis (the reachability check) —
  DONE, tightens the arm set.** Read `bootstrap-fixture/lib.rs:18-49`:
  - `tri(n) = if n==0 { 0 } else { n + tri((n-1) as nat) }` → `If`, `Binary`
    (Eq/Add/Sub), `Call`(1-arg `tri`), `Clip`(`as nat`), `Const`, `Var`.
  - `sum_tree(t) = match t { Leaf(v) => v as nat, Node(l,r) => sum_tree(*l) +
    sum_tree(*r) }` → **`Match`** (2 arms; patterns bind `v` / `l,r`), `Clip`,
    Box-deref `*l` (existing `raw_exp` `Box/Unbox` peel, `sst_serialize.rs:627`),
    `Call`(1-arg), `Binary`(Add).
  - `tree_head(t) = match t { Leaf(v) => v, Node(_l,_r) => 0 }` → **`Match`**
    (2nd arm binds wildcards — still positional binder ids, unused), `Var`/`Const`.
  - `enum Tree { Leaf(u64), Node(Box<Tree>, Box<Tree>) }` → `DtData`, 2 ctors.
  - **⟹ minimal fixture-covering arm set = leaf/`If`→`Ite`/`Binary`/`Clip`/
    `Call`(1-arg)/`UnaryOpr`(Box/Unbox)/`Match`. NO quantifiers, NO multi-arg
    `Call` in the fixture** — `Forall`/`Exists`/`CallN` are TGT-SLICE-ONLY, so
    defer them (fail-loud) until a tgt def needs them. `Match` is THE new arm the
    fixture forces (both match-bodied fns) → it is the priority, not quantifiers.
  - NEXT: read the VIR `ExprX::Match` arm/pattern shape (how `Tree::Leaf(v)` /
    `Node(l,r)` patterns expose the ctor id + positional field binders) +
    how `*l` (Box field deref) appears in a VIR spec body, then write
    `raw_vir_exp` leaf→Match. Co-design the `MatchR` arm-list binder ids with the
    production `lexpr_to_exprdata` Match arm so `def_eq` agrees by construction.

## Writeup
_when done_
