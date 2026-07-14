---
title: "W6c — serializer raw-expr transcription (ExpX→RawExp) + production LExpr→ExprData"
status: in_progress
claimed_by: opus-b22
created: 2026-07-14T05:00:00Z
updated: 2026-07-14T05:00:00Z
---

## Description

Third rung of the W6 ladder (design `DESIGN-W6-stageB.md` §4/§5; shapes landed
by W6b `bootstrap-21` into `tactus-core/lib.rs`; mechanic frozen by the W6a
probe `bootstrap-20`).

Two **boring TCB transcriptions** that make the W6b types LIVE (feed the bridge
so `close`/the emitter start producing deep `LeafE(ExprData)` leaves):

1. **Reference-side input — `ExpX → RawExp`** (the NEW, independent input; the
   diversity source). Mirror the RAW SST expression tree to `lib.RawExp` text,
   reading each node's `typ` for the `TypData` tags. NOT rendered through
   production's `to_lean_sst_expr` — that independence is the whole point.
   `render_exp` (already landed, W6b) then re-derives the cast/coercion
   decisions from the type tags in Lean.
2. **Production-side — `LExpr → ExprData`** (boring 1:1). Transcribe the
   production-rendered `lean_ast::Expr` (which already has `Int.toNat`s
   materialized as `App`/`Cast` nodes) to `lib.ExprData` text: recognize
   Cast/Deref/FieldProj/BinOp/UnOp/App/SpanMark; terminal atoms → interned id.

Then an obligation leaf emits `GoalData::LeafE(prod_ExprData)` (production) and
the reference side computes `render_exp(rawExprMirror)`; the bridge `decide`s
`expr_eq` (already in `goal_eq`'s `LeafE` arm, W6b).

Census-gated fail-loud on any un-mirrored constructor (sharp `raw-<k>` /
`ed-<k>` tags), same discipline as the stm walk.

**Done when:** `raw_exp`/`typ_data` (ref side) + `lexpr_to_exprdata` (prod side)
transcribe the cast-class (`BinOp`/`App`/`Clip`/`Var`/`Lit`), compile, and are
census-gated; a targeted test pins `typ_data`/`binop_opcode`. (Wiring the two
into the obligation-leaf emit + bridge is W6d; mutation-kill is W6e.)

**Blocked by:** nothing (W6b done).
**Blocks:** W6d (bridge deepened — obligation leaf emits `LeafE`), W6e
(mutation-kill + Tier-2 If/Let/Tuple).

## Progress

- (2026-07-14, opus-b22) **Reference-side transcription STARTED + landed the
  foundational bricks.** Read both sides end-to-end (`vir::sst::ExpX`,
  `lean_ast::ExprNode`, the W6b types, the frozen probe shapes). Implemented in
  `source/lean_verify/src/sst_serialize.rs` (additive, census-gated,
  `#[allow(dead_code)]` — not yet wired into emit, so verdict-neutral by
  construction):
  - `typ_data(&Typ) -> Sr<String>` — the `Typ → lib.TypData` mapping
    (`Int(Nat)→TyNat`, other `Int(_)→TyInt`, `Bool→TyBool`, `Datatype→TyNamed`,
    `&T`/`&mut T` `Decorate(Ref/MutRef)→TyRef`, peel `Boxed`/other decorations;
    census `typ-<k>` on the rest). `TyNamed`/`TyRef` ids reuse `typ_leaf`'s
    interning so ref and prod agree by construction.
  - `binop_opcode(&BinaryOp) -> Sr<u64>` — the CANONICAL opcode table (a fixed
    small-int namespace, NOT interned — lives in `ExprData::BinOp`'s op slot,
    separate from atom ids). Both transcriptions must map into it (the prod
    side will map `lean_ast::BinOp` to the SAME table).
  - `raw_exp(&Exp) -> Sr<String>` — `ExpX → lib.RawExp` for the cast class:
    `Const(Int)→Lit`, `Var→Var`(atom id via `binder_id`, so ref/prod atom ids
    match), `Unary(Clip{range})→Clip`(target = the range's tag),
    `Binary(op)→BinOp`(2nd slot = node's result typ), single-arg
    `Call(Fun)→Call`. Everything else → sharp `raw-<k>` census tag.
  - Reproduces the probe's Case A (`Int.toNat r = lib.tri (Int.toNat n)`) and
    Case B (elided-clip `x*x`) raw shapes exactly (verified by reading the
    probe's `raw_sum_to`/`raw_arith`).
  - **Verified:** `cargo check -p lean_verify --lib` clean (only pre-existing
    warnings; dead_code is `warn` not `deny`, so the `#[allow(dead_code)]` is
    belt-and-suspenders). New tests `typ_data_base_tags`, `typ_data_peels_boxed`,
    `binop_opcode_canonical` PASS; the full `sst_serialize` module (9 tests incl.
    the `golden_add_capped_cert` regression pin) still PASS — additive changes
    don't perturb the emit output. Committed.

## Writeup

_(partial — this task is the ref-side + foundations; prod-side LExpr→ExprData
and the emit/bridge wiring are the remainder.)_

### Key design facts established this turn (for the next instance)

- **Atom-id consistency is the load-bearing invariant.** For the bridge
  `expr_eq(prodExprData, render_exp(rawExpr)) == 1`, atom ids MUST match across
  the two sides. Both intern the atom's rendered text via `self.leaves`:
  - var reads: `binder_id(vid)` = `intern(LeanName::from_var_ident(vid))`.
  - call heads (spec-fn names) / field names: intern the rendered name text.
  So atoms stay in the "reuse production's renderer" bucket (stage-A style);
  ONLY the structural cast decisions carry diversity. The prod-side
  `LExpr→ExprData` MUST intern `Var(LeanName)` → `intern(name.as_str())` and
  `App{head: Var(name), ..}` → `intern(name)` to match.
- **Opcodes are a separate fixed namespace, not interned.** `ExprData::BinOp`'s
  op field and `Atom`'s id field are compared position-wise by `expr_eq`, so a
  fixed opcode table (see `binop_opcode`) can't collide with atom ids. The
  probe used bare `eqOp=0, mulOp=1`; this matches. The prod side maps
  `lean_ast::BinOp` into the SAME table.
- **`derefField = 0`** (matches the W6b `deref_field()` spec fn); FieldProj
  field ids for real fields = interned field-name text.
- **`Span` is NOT emitted by `raw_exp`.** The raw SST has no SpanMark node —
  production's `SpanMark` obligation wrapper is added by the renderer. The
  reference `RawExp` for an OBLIGATION should be wrapped in `RawExp::Span` at
  the `oblig_leaf` level (W6d), not inside `raw_exp`. Mirror on the prod side:
  the `LExpr::SpanMark` wrapper → `ExprData::SpanMark`.

### Open questions the next instance must resolve (flagged honestly)

- **Deref (Case C) mapping is deferred.** `*t` on a `&`-param is ctx-derived in
  production (bootstrap-18: binder-aware `render_ctx`), so the RAW SST may NOT
  carry an explicit deref node — the reference might have to DERIVE `.deref`
  from the `TyRef` type, like it derives elided clips. `render_exp` currently
  inserts FieldProj only on an explicit `RawExp::Deref`. Decide in W6d whether
  (a) the raw SST does carry an explicit deref (then `raw_exp` maps it), or (b)
  `render_exp` must derive the deref from `TyRef` (a spec-fn change, re-churns
  the crate cache — avoid if possible). For now `raw_exp` census-rejects
  deref-shaped nodes (`raw-unary-*` / `raw-unaryopr-*`).
- **Multi-arg calls.** `RawExp::Call` is single-arg (matches `tri`). `lib.Point.mk
  a b` (2-arg) is census-rejected (`raw-call-arity`). Tier-2 / a curried Call
  shape decides later.
- **Bool/other literals.** `RawExp::Lit` carries only `int`. `Const(Bool)` →
  `raw-const-bool` (rejected); bools appear as comparison RESULTS, not operands
  needing coercion, so the cast class doesn't need them yet.
