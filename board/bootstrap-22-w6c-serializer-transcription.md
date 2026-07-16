---
title: "W6c — serializer raw-expr transcription (ExpX→RawExp) + production LExpr→ExprData"
status: done
claimed_by: opus-b22
created: 2026-07-14T05:00:00Z
updated: 2026-07-14T07:30:00Z
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

- (2026-07-14, opus-b22 cont.) **Production-side `LExpr → ExprData` DONE →
  W6c COMPLETE.** Landed `lexpr_to_exprdata(&mut self, &LExpr) -> Sr<String>`
  in `sst_serialize.rs` (additive, census-gated, `#[allow(dead_code)]` — still
  not wired into emit, so verdict-neutral). It transcribes the production
  `lean_ast::Expr` (whose casts are ALREADY materialized) verbatim:
  - `Var(name) → Atom(intern(name.as_str()))`; `Lit(s) → Lit s` (raw text,
    matching the ref `raw_exp`'s BigInt).
  - `App{Var("Int.toNat"), [x]} → Cast IntToNat`; `Int.ofNat → Cast NatToInt`
    (production materializes both via `coerce_lexpr`/`wrap_int_measure`).
  - single-value-arg `App → App(fn_id, arg)` via new `app_head_fn_name` helper
    that keys on the head fn NAME, peeling a type-arg `App{Var(name), typs}`
    layer (production applies the fn to type args first; the ref `RawExp::Call`
    carries none — both drop them, staying identical on generic calls).
    Multi-arg / non-Var head → `ed-app-arity` / `ed-app-head`.
  - `BinOp → BinOp(lean_binop_opcode(op), l, r)`; `FieldProj{"deref"} →
    FieldProj(_, 0)` (= ref `deref_field()`), other fields intern the name;
    `SpanMark → SpanMark(intern(rust_loc), inner)`.
  - Added `lean_binop_opcode(&lean_ast::BinOp)` — the production half of the
    canonical opcode table (`Eq→0 … Implies→13`); `Iff`/bitwise/`Prod` fail
    loud (out of the cast class, ref side rejects the vir sources too).
  - **Verified:** `cargo check -p lean_verify --lib` clean (0 errors). 4 new
    tests PASS + all 13 `sst_serialize` tests green (incl. `golden_add_capped_cert`
    — emit output unchanged, verdict-neutral):
    - `binop_opcode_alignment` — the invariant test: for every structural vir
      op, `binop_opcode(op) == lean_binop_opcode(binop_to_ast(op))`. Pins the
      two tables in lockstep THROUGH production's own lowering, so a future
      one-sided edit is a caught failure (guards against a FALSE opcode
      divergence at the bridge).
    - `lexpr_to_exprdata_case_a` — the verbatim `sum_to` leaf `Int.toNat r =
      lib.tri (Int.toNat n)` → the exact `BinOp(Eq, Cast(r), App(tri, Cast(n)))`
      ExprData `expr_mirror_kernel_computes` pins (atom ids from interning
      order).
    - `lexpr_to_exprdata_deref_fieldproj` — Case C prod side (`.deref` id 0).
    - `lexpr_to_exprdata_census_rejects` — `ed-litbool`/`ed-app-arity`/
      `ed-binop-bitand` fail-loud tags.

## Writeup

**W6c is complete: both transcription directions land, compile clean, are
census-gated, and are pinned by targeted tests.** The task is verdict-neutral
by construction — neither transcription is called by the emit path yet
(`#[allow(dead_code)]`), so `close`/the emitter still produce stage-A
`Leaf(u64)` and the `golden_add_capped_cert` regression is byte-identical.
Wiring both into the obligation-leaf `LeafE` emit + bridge is **W6d**;
mutation-kill + Tier-2 (If/Let/Tuple) is **W6e**.

### The two transcriptions and why they diverge only where they should

- **Reference (`raw_exp`/`typ_data`, prior turn):** mirrors the RAW SST
  (`vir::sst::ExpX`) into `lib.RawExp` text with per-node `TypData` tags. It
  does NOT re-render through production. `render_exp` (Lean, W6b) then
  re-derives every cast/coercion decision UNIFORMLY from the type tags.
- **Production (`lexpr_to_exprdata`, this turn):** mirrors the
  production-rendered `lean_ast::Expr` — whose casts are ALREADY materialized —
  1:1 into `lib.ExprData` text, re-making NO decision.
- The bridge (`goal_eq`'s `LeafE` arm, W6b) `decide`s
  `expr_eq(prod_ExprData, render_exp(ref_RawExp)) == 1`. Because the reference
  applies the coercion rule uniformly and the production emitter applied it
  case-by-case, a production emitter that inserts an `Int.toNat`
  INCONSISTENTLY (the Friction-2 class) diverges from the reference → the
  `decide` fails. That's the whole diversity win (DESIGN-W6-stageB.md §3.1).

### Atom-id consistency (the load-bearing invariant), verified by construction

For `expr_eq` to match on atoms (so diversity is confined to the cast layer),
the two sides MUST intern identical text for the same terminal:
- **var reads:** ref `RawExp::Var` interned `LeanName::from_var_ident(vid)`;
  production renders a var read as exactly `Var(LeanName::from_var_ident(vid))`,
  so `lexpr_to_exprdata`'s `intern(name.as_str())` yields the same id.
- **spec-fn heads:** ref `call_fun_id` interned `LeanName::from_path(&fun.path)`;
  production's App head is `Var(LeanName::from_path(&fun.path))` (confirmed at
  `to_lean_sst_expr.rs:1229`) → same id.
- **`.deref` field:** both use the fixed `deref_field()` id `0`.
- **opcodes:** a SEPARATE fixed namespace (compared position-wise by
  `expr_eq`, never against atom ids), kept in lockstep by the alignment test.

### Assumptions / honest scope limits (for W6d/W6e)

- **Type args are dropped on BOTH sides.** The ref `RawExp::Call` has no
  type-arg slot and `raw_exp` silently ignores `_typs`; `app_head_fn_name`
  mirrors that by peeling the type-arg `App` layer. So the certificate does
  NOT verify type-argument rendering (two calls to the same fn with different
  type args mirror identically). Consistent → no false divergence, but a real
  scope gap to note when Tier-2 generics land.
- **Deref (Case C) asymmetry, still open.** The prod side handles
  `FieldProj{"deref"}` fully; the ref side's `raw_exp` still census-rejects
  deref-shaped raw SST nodes (the open question: does the raw SST carry an
  explicit deref, or must `render_exp` derive it from `TyRef`?). Until W6d
  resolves it, a deref-containing fn is ref-rejected → not bridged (fail-loud,
  safe). Recommendation stands (per Danielle): keep the derivation in
  `render_exp` if possible to avoid re-churning the crate cache.
- **`TypeAnnot` is census-rejected (`ed-typeannot`).** If production wraps a
  cast-class obligation operand in `(e : T)`, the ref has no analog and the fn
  is prod-rejected. W6d's census over the fixture will reveal whether the
  `sum_to` leaf actually carries one; if so, peel it transparently (it carries
  no ExprData structure). Not handled now to avoid guessing.
- **Negative int literals** emit raw on both sides (`Lit -5`), which would need
  parenthesizing to parse in Lean — a shared open item; none arises in the
  cast class (nonneg only).
- **`Iff` / bitwise / `Prod`** fail loud on the prod side, matching the ref
  `binop_opcode`'s rejection of the vir ops that produce them.

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
