---
title: "W7c-ref — reference def-body transcriber on the VIR ExprX surface (raw_vir_exp)"
status: in_progress
claimed_by: opus-w7c-ref
created: 2026-07-14T23:20:00Z
updated: 2026-07-15T02:20:00Z
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

- (2026-07-14, opus-w7c-ref) **PREMISE EMPIRICALLY VALIDATED + reference core
  landed (compiles, 345/0, verdict-neutral).**
  - **The biggest de-risk — Match genuinely survives to `f.body` (ground truth,
    not "the arm exists").** The `ast.rs:1200` note "*ast_simplify replaces Match
    with other expressions*" made this load-bearing: if the def-body VIR were
    post-simplify, `Match` would be desugared and the whole VIR-Match premise
    wrong. Checked the EMITTED fixture:
    `bootstrap-fixture/out/lib/TactusDefs_lib_exec__root.lean:14` =
    `noncomputable def lib.tree_head (t : lib.Tree) : Int := match t with |
    lib.Tree.Leaf v => v | lib.Tree.Node _l _r => 0` — a **native Lean `match`**.
    The desugared `if .isLeaf` form appears ONLY on the obligation/SST side
    (`head_exec.lean:13`, the exec-fn goal). ⟹ `spec_fn_to_ast` reads a
    PRE-simplify `f.body`; production's `expr_to_node` Match arm
    (`to_lean_expr.rs:680`) is genuinely reached. Also captured `lib.tri` =
    `if n = 0 then 0 else n + lib.tri (Int.toNat (n - 1))` (the Ite exemplar,
    `Clip`→`Int.toNat`). `sum_tree` is PRUNED (no caller) — only `sq`/`tri`/
    `tree_head` emit, `tree_head` is the reachable Match exemplar.
  - **Landed `raw_vir_exp` + 3 helpers** in `sst_serialize.rs` (next to
    `raw_exp`, `#[allow(dead_code)]`): fixture-reachable arms = Box/Unbox peel,
    `Const(Int/Bool)`, `Var`/`VarAt`/`ReadPlace(Local)`, `Clip`, `Binary` (reuses
    `binop_opcode`), `Call(CallTarget::Fun, 1-arg)`, `UnaryOpr(Field)`,
    `If(_,_,Some)`→`Ite` (else-less → fail-loud `if-noelse`, the VIR-vs-SST
    divergence), and **`Match`→`MatchR`** (the priority arm): scrutinee via
    `raw_vir_place` (`Local` only), arms right-fold into
    `RawArmList::Cons(ctor_id, BinderIdList, body, tail)`, guard fail-loud unless
    trivially-`true` (production's `expr_to_node` silently DROPS `arm.guard` — a
    real guard is a silent mistranslation the bridge must not paper over).
    Quantifiers + multi-arg `Call` stay fail-loud (`quant`/`call-nonfun`, tgt-
    slice-only). Added `vir_expr_construct_tag` (census tags, mirrors
    `exp_construct_tag`).
  - **§7 Q1 co-design ANCHOR SOLVED — single source of truth.** Extracted
    `ctor_pattern_name(dt, variant) -> Option<String>` in `to_lean_expr.rs`; BOTH
    production `pattern_to_ast` and reference `pattern_ctor_binds` call it, so the
    Match ctor id string CANNOT drift (was a duplicate-logic risk). Behavior-
    preserving refactor of the live emit path (all 342 pre-existing tests green).
    Field binder ids: reference reads the SAME VIR `fields` Vec in the SAME
    `.iter()` order production does (no sort either side) ⟹ identical ids by
    construction. (`_l`/`_r` are named `PatternX::Var`, not `Wildcard` — wildcard-
    in-ctor-field fails loud, unreached.)
  - **Verdict-neutral by construction:** `raw_vir_exp` is a NEW dead-code fn,
    never on the emit path; NO `tactus-core` edit (no olean re-emit / base-hash
    change). The only live touch is the behavior-preserving `ctor_pattern_name`
    extraction.
  - **Tests (3 new, lib suite 342→345/0):** `raw_vir_exp_ite_var_leaves`
    (the `tri` Ite shape — converges with SST `raw_exp_ite_body`),
    `raw_vir_exp_if_noelse_fails` (the OPTIONAL-else divergence),
    `raw_vir_exp_peels_box_and_reads_var` (leaf/peel parity). Added `mk_vexpr`
    (VIR `Expr` is the same `Arc<SpannedTyped<_>>` shape as SST `Exp`, so it
    mirrors `mk_exp`). **Match arm NOT unit-tested by design** — a hand-built
    ctor `Path` can render differently under `lean_name` than the compiler's, so
    a hand-built Match test would test the arm against ITSELF, not production.
    Its real validation is the e2e `def_eq` bridge (W7d) over the emitted
    `lib.tree_head`, where §7 Q1 (ctor/binder id interning agreement vs REAL
    production output) genuinely gets exercised.
  - **NEXT (hand-off):** (1) production `lexpr_to_exprdata` Match/Ite arms
    (`bootstrap-28`) — must intern the ctor id from `LPattern::Ctor.name` (=
    `ctor_pattern_name` output) + binder ids from the arm's `LPattern::Var` args,
    same order. (2) W7d def-body entry point: `raw_vir_exp(f.body)` → `RawDef` +
    `render_def`, production `DefData`, bridge `def_eq`. (3) def-header
    (`RawDef`/`DefData` params+ret) + datatype (`RawDt`/`DtData`) — separate VIR
    input surfaces, still to transcribe. (4) if W7d needs `sum_tree` (Box-deref
    inside a match arm), add a fixture caller or use the tgt slice — it's pruned
    today.

- (2026-07-15, opus-w7c-match) **Hand-off item (1) SATISFIED for `Match`** — the
  production `lexpr_to_exprdata` Match arm + `lpattern_ctor_binds`/
  `lpattern_binder_id` twins landed in `bootstrap-28` (lib suite 347/0,
  verdict-neutral). They co-design with THIS side's `MatchR`/`pattern_ctor_binds`
  exactly as the §7 Q1 anchor prescribed: shared `ctor_pattern_name` for the ctor
  id, `LeanName::from_var_ident` for the binder ids, same `.iter()` order. So the
  fixture-covering body set (leaf/Ite/Match) is now complete on BOTH transcriber
  sides. Remaining hand-off items (2) W7d def-body entry point + e2e `def_eq`
  bridge — the Match arm's REAL cross-side validation — (3) def-header/datatype,
  (4) `sum_tree` Box-deref-in-arm fixture caller, are unchanged.

- (2026-07-15, opus-w7c-quant) **`Quant`→`ForallR`/`ExistsR` arm LANDED on the
  reference `raw_vir_exp`** (paired with the production `Forall`/`Exists` arms in
  `bootstrap-28`); lib suite 347→351/0, verdict-neutral. This is the first of the
  tgt-slice-only remainders (fixture forces no quantifier — the `Quant` arm is
  reachable only from the W7d def-body entry point).
  - **Arm** (`sst_serialize.rs`, before the `rawvir-` census fallback): VIR
    `ExprX::Quant(quant, q_binders, body)` — VIR carries ALL binders of one
    quantifier in a single `Quant`, so nest them **right-to-left** into the
    single-binder `RawExp::ForallR`/`ExistsR` (W7b vocab is single-binder):
    `∀ x y, P` ⟶ `ForallR x (ForallR y P)`. `quant.quant` (an `air::ast::Quant`)
    picks the ctor. Binder-NAME ids via `binder_id` (= `from_var_ident`, prod's
    interning); binder-TYPE via `typ_data`; empty binder list → fail loud
    (`rawvir-quant-empty`); a binder type `typ_data` can't map (bare type param
    etc.) fails loud there. The nesting ORDER matches production's identical
    right-to-left fold over the SAME `q_binders.iter()` order (production's
    `ExprNode::Forall{binders}` is built by `vir_var_binders_to_ast`, an
    order-preserving map) ⟹ `def_eq` agrees by construction.
  - **§7-Q-style co-design fork RESOLVED (Danielle-endorsed, 2026-07-15):** the
    production side must invert the RENDERED binder type-`Expr` (prod
    `Binder.ty = typ_to_expr(vir)`) back to the SAME `TypData` the reference
    `typ_data` emits. Landed as `ltyp_to_typdata` (bootstrap-28). Primitive heads
    map by name; named datatype → `TyNamed(intern(pp(ty)))` and `&T` →
    `TyRef(intern(pp(inner)))` — both agree with `typ_data`'s
    `typ_leaf = intern(pp(typ_to_expr(vir)))` off the SHARED `self.leaves` table.
    **Known gap (documented, NOT unsound):** `typ_to_expr` collapses `usize`/
    `char`→`Var("Nat")` while `typ_data` maps them to `TyInt` (only true `nat`→
    `TyNat`) ⟹ a `nat` binder certifies but a `usize`/`char` binder SPURIOUSLY
    fails the bridge (uncertifiable, never wrongly passes). Same for a bare
    type-PARAM binder (indistinguishable from a nullary datatype on the prod
    side → `TyNamed`, while the ref `typ_data` fails loud on `TypParam`; the ref
    is the gate). Disambiguating needs a `typ_to_expr` change — its own turn.
  - **Tests (2 new here):** `raw_vir_exp_forall_nests_binders` (∀ i j : int,
    pins the right-to-left `ForallR` nesting + `TyInt` binder types +
    `TyBool` body), `raw_vir_exp_exists_single_binder` (pins the `ExistsR`
    ctor). Verdict-neutral: `raw_vir_exp` is still dead code (no emit-path wire).
  - **NEXT (unchanged from below + the surviving W7c remainders):** multi-arg
    `Call`→`CallN` (the `raw_vir_exp` `Call` arm's `args.len()!=1` fail-loud) —
    deferred by Danielle because a faithful `render_list` needs per-arg `TypData`
    (auto-borrow deref), a cache-churning `RawList` edit (own batch, like W7b);
    then datatype (`RawDt`/`DtData`) + def-header (`RawDef`/`DefData`), separate
    VIR input surfaces; then W7d wires the def-body entry point + e2e `def_eq`
    bridge (the real cross-side validation of Match AND the new Quant arm).

- (2026-07-15, opus-w7c-defhdr) **Reference def-HEADER `raw_vir_def` LANDED**
  (split to `bootstrap-30`, DONE; lib suite 351→354/0, verdict-neutral). Wraps
  the `raw_vir_exp` body with the header: `call_fun_id(name)` +
  `f.params`→`ParamList` (`binder_id`+`typ_data`) + `typ_data(ret)`. Decomposed
  args `(name, typ_params, params, ret, body)` so the test avoids the 33-field
  `FunctionX`; W7d passes `&f.name`/`&f.typ_params`/`&f.params`/`&f.ret.x.typ`/
  body. Poly gate `rawvir-def-poly` (production's `Def.binders` prepends
  `{A : Type}` binders `TypData` can't mirror — needs `TypData::TySort`, deferred
  like AppN) + `&mut`-param gate `rawvir-def-mutparam`. Paired with the
  production `ldef_to_defdata` (`bootstrap-28`); id agreement by construction
  (`call_fun_id`=`lean_name`, `binder_id`=`from_var_ident`,
  `typ_data`↔`ltyp_to_typdata`). Still-to-do multi-arg `Call`→`CallN` (the
  cache-churning `RawList` edit) + datatype `RawDt` are unchanged.

- (2026-07-15, opus-w7c-dt) **Reference datatype `raw_vir_dt` + `dt_field_typ_data`
  LANDED** (split to `bootstrap-31`, DONE; lib suite 354→359/0, verdict-neutral).
  A NEW input surface (VIR `DatatypeX`, not `ExprX`): decomposed args
  `(name: &Dt, typ_params, variants)` so the test avoids the ~13-field
  `DatatypeX`; W7d passes `&dt.x.{name,typ_params,variants}`. Name via
  `lean_name(path)`, per-ctor via `sanitize(&v.name)`, positional field types via
  the new `dt_field_typ_data` which KEEPS the `Box` (`Decorate(Box) → TyBox(pointee)`,
  else delegate to `typ_data`) — the W7a §7 Q4 mechanic the whole card flagged as
  the technical hurdle. Gates: `rawvir-dt-poly` (like `raw_vir_def`), `-tuple`,
  `-struct` (single-variant struct → production `structure`, a different
  transcription). Paired with production `ldt_to_dtdata` (`bootstrap-28`); id
  agreement by construction. Interning forward (name=0, ctors decl order);
  `CtorList`/`TypList` folded reversed. **Fixture-covering DEFINITIONS surface
  (def header + Ite/Match body + datatype) now complete on the reference side.**

## Writeup
_partial (reference transcriber core landed). The def-body REFERENCE transcriber
`raw_vir_exp` (+ `raw_vir_place`/`pattern_ctor_binds`/`pattern_binder_id`) is
implemented on the VIR `ExprX` surface for the fixture-reachable arms including
the priority `Match`→`MatchR`, compiles clean, and is unit-tested on the cheap
structural arms (345/0). The premise that `Match` survives to the def body was
validated against the emitted fixture (`lib.tree_head` is a native Lean `match`).
The §7 Q1 ctor-id co-design is solved via the shared `ctor_pattern_name` helper
(single source of truth, no drift). Verdict-neutral (dead code, no tactus-core
edit). Remaining before the task closes: production-side Match/Ite arms
(bootstrap-28), the W7d def-body entry point + e2e `def_eq` bridge (the Match
arm's real validation), and the def-header/datatype input surfaces. See Progress
for line refs + the guard/scrutinee/wildcard fail-loud rationale._
