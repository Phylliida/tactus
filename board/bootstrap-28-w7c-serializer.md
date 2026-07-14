---
title: "W7c — serializer transcriptions for the def-body constructors (Ite/Match/AppN/Forall/Exists + datatype)"
status: in_progress
claimed_by: opus-w7c
created: 2026-07-14T22:10:00Z
updated: 2026-07-15T02:20:00Z
---

## Description

Extend the two W6c transcribers for the new W7 body constructors that W7b
landed in `tactus-core` (`RawExp::{Ite,MatchR,CallN,ForallR,ExistsR}` +
`ExprData::{Ite,Match,AppN,Forall,Exists}`), plus the datatype/def-header
transcriptions. Spec: `DESIGN-W7-defslayer.md` §6 (W7c row) + §3.1 table.

The two transcribers (`source/lean_verify/src/sst_serialize.rs`):
- **reference side** `raw_exp` (`ExpX → RawExp` text, the independent VIR
  lowering — the diversity that gives the bridge teeth);
- **production side** `lexpr_to_exprdata` (`lean_ast::Expr → ExprData` text, the
  boring verbatim side).

Per constructor, add BOTH arms so `expr_eq(prod, render_exp(ref))` matches.
Coercion lives on the reference `render_exp` side (already landed in W7b), so
the production side transcribes verbatim.

**Verdict-neutral discipline (load-bearing).** `raw_exp` is LIVE on the
obligation emit path via `oblig_slot` (sst_serialize.rs:485/1008/1459): a
success there deepens the obligation + records `deep_ids`. So every new arm
MUST be confirmed golden-byte-identical (fixture obligations are boolean; if/
match live in def bodies, so no fixture obligation should be If/Match-topped or
-containing). Confirm with the golden suite + probe9 after each arm; if a golden
flips, the arm made a real obligation go deep — reconsider (accept as an
improvement, or gate the body arms behind a def-body entry point).

**Done when:** all §3.1 body constructors transcribe on both sides
(census-gated, fail-loud on the deferred shapes), unit tests pin each shape,
the golden suite + probe9 stay byte-identical (verdict-neutral), and the
opcode/ctor-alignment invariant holds. AppN per-arg expected-type coercion
(the W7b-deferred §7 Q3) is folded in here or split to a follow-up.

**Blocked by:** `bootstrap-27` (W7b) — DONE. **Blocks:** W7d (wire def
emission + bridge `def_eq`/`dt_eq`), W7e (mutation-kill).

## Progress

- (2026-07-14, opus-w7c) **CLAIMED. First increment = `Ite` (the `tri`
  exemplar), both transcriber sides + tests.** Reconnaissance findings that
  shape the rest of the ladder:
  - Ground-truth shapes are the LANDED W7b `tactus-core/lib.rs` constructors
    (not the frozen `probe15` names): `RawExp::Ite(TypData ty, cond, then,
    else)` / `ExprData::Ite(cond, then, else)`; `render_exp`'s Ite arm
    (lib.rs:933) coerces each branch via `needs_nat_coercion(type_of(branch),
    ty)` — so the ref side just carries the result type and the prod side is
    verbatim (any branch cast is an `Int.toNat` App the existing Cast arm
    handles).
  - VIR SST node: `ExpX::If(Exp, Exp, Exp)` (cond, then, else — no Option; a
    body if always has both branches). Production LExpr node:
    `ExprNode::If { cond, then_, else_: Option }`. Census tags "if" already
    exist on both sides (sst_serialize.rs:2370/2482).
  - `raw_exp` is SHARED with `oblig_slot` (the live obligation path) — see the
    verdict-neutral note above. The `Ite` arm is the first live-path test of
    that property.
  - Test harness ready: `mk_exp(ExpX, Typ)` + `tvar`/`tint` build reference
    SST inputs; `LExpr::new(ExprNode::…)` builds production inputs (see the
    existing `raw_exp_*` / `lexpr_to_exprdata_*` tests, sst_serialize_tests.rs).
  - REMAINING constructors + their open questions (for the next increments):
    - **Match** (the big one): need the VIR SST shape of a spec-fn `match`
      body — is it `ExpX::Match`? or desugared? — and the binder-id discipline
      (§7 Q1: ref + prod must intern arm-binder ids identically). Targets
      `RawExp::MatchR(scrut, RawArmList, ty)` + `ExprData::Match(scrut,
      ArmList)`, arms INLINED into `Cons(ctor, BinderIdList, body, tail)`.
    - **Forall/Exists**: VIR `ExpX::Bind(BndX::Quant, body)` → binder id/type
      extraction; targets `RawExp::ForallR(bid, bty, body)`.
    - **Multi-arg App** (`CallN`/`AppN`): generalize the single-arg `Call`/`App`
      arms to an arg list; then the W7b-deferred per-arg coercion (a
      `render_list` edit in tactus-core — cache-churning, its own turn).
    - **Datatype** (`RawDt`/`DtData`) + **def header** (`RawDef`/`DefData`
      params/ret): a new input surface (VIR datatype decl + fn signature), not
      an `ExpX`; likely its own transcriber pair.

- (2026-07-14, opus-w7c-2) **⚠ SURFACE-FORK FINDING (reframes the reference
  side) — verified from source + endorsed by Danielle.** The task text assumed
  the reference def-body transcriber would EXTEND the SST-surface `raw_exp`
  (`ExpX → RawExp`). That is the wrong surface for def bodies. Chain of facts:
  1. **VIR `ExprX` HAS `Match`; SST `ExpX` does NOT** — `match` in a spec-fn
     body is desugared to `If` + variant-tests during AST→SST lowering.
     (Confirmed: `source/vir/src/sst.rs:69` `enum ExpX` has `If`/`Bind`/`Call`/
     `Ctor`/`UnaryOpr` but no `Match`; VIR `ExprX::Match` lives in
     `source/vir/src/ast.rs`.)
  2. **Def bodies emit from VIR `ExprX` directly**, NOT through SST:
     `to_lean_fn.rs:315 spec_fn_to_ast` renders `f.body` via
     `to_lean_expr::vir_expr_to_ast_with_binders` (`to_lean_fn.rs:343`), and
     `vir_expr_to_ast` **preserves** the shape:
     `to_lean_expr.rs:680  ExprX::Match(place, arms) → ExprNode::Match{..}`,
     `:583 ExprX::Quant → ExprNode::Forall/Exists`, multi-arg
     `ExprX::Call → App`. So production def-body `LExpr`s really do contain
     `Match`/`Forall`/`Exists`/multi-arg-`App` nodes (`lean_ast.rs` `ExprNode`
     has all four incl. `Match { scrutinee, arms: Vec<MatchArm> }`).
  3. **Obligations (W6) go through SST** (Match already desugared) — which is
     exactly why the SST `raw_exp` never needed `Match`/`Quant`.
  - **Conclusion (Danielle-endorsed):** the def-body REFERENCE transcriber must
    be a NEW function on the VIR `vir::ast::Expr` surface (where `Match`/`Quant`/
    multi-arg-`Call` are live), NOT an extension of SST `raw_exp`. If instead the
    reference lowered the VIR body to SST, `Match` would desugar to `If`-chains
    while production keeps `Match` nodes → `def_eq` could never match → bridge
    always fails. This is DESIGN §2 ("transcribe directly from VIR") being
    load-bearing; DESIGN §3's "reuse `expx_to_rawexp`" is the optimistic part —
    the RawExp *target vocab* + helpers (`typ_data` at `sst_serialize.rs:588`
    already takes a `&Typ` and works on VIR `Typ`; `binop_opcode`; `text_leaf`)
    ARE reusable, but the transcriber *arms* are new on the VIR surface.
  - **So the W7b `MatchR`/`RawArmList`/`ForallR`/`ExistsR`/`CallN` vocabulary IS
    reachable** — the gating "is a spec-fn match body `ExpX::Match` or desugared?"
    question is answered: **reachable, but only on the VIR def-body surface**,
    not the SST obligation surface.
  - **The landed SST `raw_exp::Ite` arm stays** (harmless, verdict-neutral) but
    it is the *obligation* surface — it does not serve def bodies. The def-body
    `Ite` belongs on the new VIR reference transcriber (note: VIR `ExprX::If` has
    an OPTIONAL else, unlike SST's 3-branch `If`).
  - **Corrected remaining-W7c plan** (Danielle: reference-first — it defines the
    target shapes the production arms must match, so production-first would be
    guessing the format):
    1. **NEW reference VIR transcriber** (`raw_vir_exp` on `vir::ast::Expr`):
       leaf/`If`→`Ite`/`Binary`/`Call`(multi)→`CallN`/`Ctor`/`Match`→`MatchR`/
       `Quant`→`ForallR`/`ExistsR`/`Field`. The real long pole → split to
       `bootstrap-29`. Mirror `to_lean_expr::expr_to_node` for the VIR-node
       reading; reuse the RawExp emitter + `typ_data`/`binop_opcode`.
    2. **Production side** = extend `lexpr_to_exprdata` for `Match`/`Forall`/
       `Exists`/multi-arg-`App` (ExprNode nodes from VIR bodies). NOTE it is now
       LIVE on the emit path (goal-side deepening, `sst_serialize.rs:1627`), so
       same verdict-neutral discipline as `raw_exp` — confirm no obligation-goal
       LExpr carries these before landing each arm (fixture analysis, like the
       Ite proof). Binder-type wrinkle: prod `Binder.ty` is a rendered type-Expr
       (`vir_var_binders_to_ast` → `typ_to_expr`, `to_lean_expr.rs:346`); the
       `ExprData::Forall(bid, bty, body)` `bty` must be recognized back to the
       SAME `TypData` the reference emits from the VIR `Typ` — a small
       type-expr→TypData recognizer, co-designed with the reference arm.
    3. W7d wires the def-body entry point (both sides).

- (2026-07-14, opus-w7c) **`Ite` increment LANDED — both transcriber sides +
  3 tests, full lib suite 342/0 (was 339), verdict-neutral CONFIRMED.**
  - `raw_exp` gained `ExpX::If(cond, then, else) → RawExp::Ite(typ_data(e.typ),
    cond, then, else)` (sst_serialize.rs, before the `raw-` census fallback).
    The leading slot is the branch RESULT type; `render_exp` (lib.rs:933) reads
    it for per-branch coercion, so the ref side only carries the type.
  - `lexpr_to_exprdata` gained `ExprNode::If { Some else } → ExprData::Ite`
    (verbatim structural transcription — any branch cast is already an
    `Int.toNat` App the `Cast` arm handles) + `{ None } → Err("ed-if-noelse")`
    (else-less if can't be value-position; census-tracked fail-loud).
  - Tests: `raw_exp_ite_body`, `lexpr_to_exprdata_ite_body`,
    `lexpr_to_exprdata_ite_no_else_fails` (sst_serialize_tests.rs). All green.
  - **Verdict-neutrality — proven, no rebuild needed.** `raw_exp` is live via
    `oblig_slot`, so this needed checking. `golden_add_capped_cert` stays
    byte-identical (it runs the serializer WITH this change on the primary
    fixture). Generalized across the WHOLE fixture by source analysis: the
    fixture's four `if`s are all UNREACHABLE by the new arm — `tri`/`count_down`
    bodies (spec/exec bodies, not serialized until W7d), `max_u64`/`count_down`
    value-position return ifs (consumed by `lift_if_raw`, which matches
    `ExpX::If` ITSELF before the leaf fallback ever calls `raw_exp` — I did NOT
    touch `lift_if_raw`), and `find_square`'s statement-level `if` (the `stm`
    walk's `StmX::If`, not `ExpX::If`). So the new arm is dead on the current
    emit path; it activates only when W7d wires the def-body entry point.
  - **probe9 end-to-end NOT re-run** — its on-disk certs are stale (pre-change)
    and regenerating them needs a full `vargo` release fork build; against stale
    certs probe9 would test the OLD emit, not this change. The byte-identical
    golden + the unreachable-arm proof are the on-point evidence. A full probe9
    rebuild is a cheap belt-and-suspenders follow-up once W7d actually reaches
    the arm.
  - **NEXT increment = quantifiers OR multi-arg App** (both mechanical, ref
    `render_exp` side already landed). Match needs the VIR-match-shape
    investigation first (is a spec-fn `match` body `ExpX::Match`, or desugared
    to nested `If`/ctor-tests? — determines whether `RawArmList` transcription
    is even reachable). Datatype/def-header is a separate input surface (W7d-ward).

- (2026-07-15, opus-w7c-match) **Production-side `Match` arm LANDED — the
  fixture-critical constructor, both sides now transcribe `match`; lib suite
  345→347/0, verdict-neutral.** This pairs with the reference `raw_vir_exp`
  `MatchR` arm (bootstrap-29, already landed), closing the "big one" the earlier
  Progress flagged as gated on the VIR-match-shape investigation (now resolved by
  the surface-fork finding).
  - **`lexpr_to_exprdata` gained `ExprNode::Match { scrutinee, arms }` →
    `ExprData::Match(scrut, ArmList)`** (`sst_serialize.rs`, after the `If` arms,
    before the census fallback). Scrutinee recurses; arms fold right-to-left into
    the inlined `ArmList::Cons(ctor_id, binder_ids, body, tail)` (the W7b inlined
    list, not the named `MatchArm`). Body transcribed VERBATIM — any branch cast
    is already an `Int.toNat` App the `Cast` arm handles, matching the reference
    `render_arms`' per-arm coercion (coercion lives on the ref side only).
  - **Two new helpers** = production twins of the reference
    `pattern_ctor_binds`/`pattern_binder_id`: `lpattern_ctor_binds(&LPattern)`
    and `lpattern_binder_id(&LPattern)`. §7 Q1 id-agreement holds BY
    CONSTRUCTION: (a) ctor id — production's `pattern_to_ast` built
    `Pattern::Ctor { name }` from the SHARED `ctor_pattern_name(dt, variant)`
    helper (the same helper the reference interns), so `text_leaf(name)` matches;
    (b) binder ids — production's `Pattern::Var(LeanName)` was built via
    `LeanName::from_var_ident(&binding.name)`, exactly what the reference
    `binder_id` interns, and both read the arg/field list in the same
    `.iter()` order (no sort either side). Non-ctor arm heads fail loud
    (`ed-arm-pat`); non-Var field patterns fail loud (`ed-field-pat`) — lockstep
    with the reference's `rawvir-arm-pat`/`rawvir-field-pat`.
  - **Tests (2 new):** `lexpr_to_exprdata_match_tree_head` pins the full
    `tree_head`-shaped output (`match t { Leaf v => v, Node _l _r => 0 }`),
    including the reversed-fold interning order (scrut=0, Node ctor=1, `_r`=2/
    `_l`=3, Leaf ctor=4, `v`=5, body reuses `v`=5) and the binder-list arg-order
    preservation. `lexpr_to_exprdata_match_nonctor_arm_fails` pins the
    `ed-arm-pat` fail-loud. (Unlike the reference Match arm — untestable in
    isolation because a hand-built ctor `Path` renders differently under
    `lean_name` — the production input is an ALREADY-rendered `Pattern::Ctor {
    name: String }`, so a hand-built prod test is honest: it pins the
    transcription shape, not the naming. Cross-side `def_eq` agreement is still
    the W7d e2e bridge's job.)
  - **Verdict-neutral — confirmed, no rebuild.** `lexpr_to_exprdata` enters the
    live emit path only via `goal_data` (`sst_serialize.rs:1952`) on obligation-
    GOAL leaves; obligations are SST-surface where `Match` is desugared to
    `If`-chains, so a goal leaf `LExpr` is NEVER `ExprNode::Match` → the new arm
    is unreachable today (same argument the `Ite` prod arm used). The full lib
    suite (incl. `golden_add_capped_cert` + the other goldens) stays byte-
    identical at 347/0. The arm activates only when W7d wires the def-body entry
    point.
  - **NEXT:** Forall/Exists (`ExprNode::Forall/Exists` → `ExprData::Forall/
    Exists`; needs the binder-type recognizer — prod `Binder.ty` is a rendered
    type-Expr, must map back to the SAME `TypData` the reference emits from the
    VIR `Typ`, per the earlier Progress note) + multi-arg AppN (+ the W7b-deferred
    per-arg coercion) + datatype (`RawDt`/`DtData`) + def-header. All are
    tgt-slice-only (the fixture forces none), so they can land incrementally as
    W7d/tgt needs them; the fixture-covering set (leaf/Ite/Match) is now COMPLETE
    on both sides.

- (2026-07-15, opus-w7c-quant) **`Forall`/`Exists` arms LANDED on the production
  `lexpr_to_exprdata`** (paired with the reference `raw_vir_exp` `Quant` arm,
  bootstrap-29); lib suite 347→351/0, verdict-neutral. First of the tgt-slice-only
  remainders after the fixture set (leaf/Ite/Match). Danielle-endorsed fork
  decision: do Forall/Exists first (no `tactus-core` edit — `render_exp`'s
  `ForallR`/`ExistsR` + `render` already landed in W7b), defer AppN (its faithful
  `render_list` needs a cache-churning `RawList` per-arg-`TypData` edit).
  - **Arms** (`sst_serialize.rs`, after the `Match` arm): `ExprNode::Forall
    {binders, body}` / `Exists{..}` → `lquant_to_exprdata("Forall"/"Exists", ..)`.
    Production emits ONE node carrying ALL binders; the helper nests them
    **right-to-left** into single-binder `ExprData::Forall`/`Exists` — the
    IDENTICAL nesting the reference `raw_vir_exp` `Quant` arm does over the SAME
    binder order (`vir_var_binders_to_ast` is order-preserving) ⟹ `def_eq` agrees
    by construction. Binder-NAME ids via `text_leaf(from_var_ident)` (= ref
    `binder_id`); a nameless (instance-bracket) binder → fail loud
    (`ed-quant-noname`); empty list → `ed-quant-empty`.
  - **`ltyp_to_typdata` — the binder-TYPE recognizer (the §7-Q3-style fork,
    RESOLVED).** Prod `Binder.ty` is a RENDERED type-`Expr` (`typ_to_expr(vir)`),
    not a `TypData`; the recognizer inverts it back to the SAME `TypData` the
    reference `typ_data` emits from the VIR `Typ`: `Var("Prop")`→TyBool,
    `Var("Int")`→TyInt, `Var("Nat")`→TyNat; `Tactus.Ref`/`MutRef` app →
    `TyRef(intern(pp(inner)))`; any other head → `TyNamed(intern(pp(whole)))`.
    **Id-agreement is BY CONSTRUCTION** — the ref's `typ_leaf`/`TyRef`/`TyNamed`
    id is `intern(pp(typ_to_expr(vir)))` off the SAME `self.leaves` table, and
    prod's `Binder.ty` IS `typ_to_expr(vir)`, so `pp` (hence the interned id)
    coincides; both peel Box/Decorate transparently. **Documented gap (NOT
    unsound):** `typ_to_expr` collapses `usize`/`char`→`Var("Nat")` while
    `typ_data` maps them to `TyInt` (only true `nat`→`TyNat`), so a `usize`/`char`
    (or bare type-param) binder SPURIOUSLY fails the bridge — uncertifiable,
    never wrongly passes. `nat`/`int`/`bool`/named-datatype binders certify (the
    common tgt-slice case). Disambiguating needs a `typ_to_expr` change (own turn).
  - **Verdict-neutral — confirmed, no rebuild.** `lexpr_to_exprdata` enters the
    live emit path only via `goal_data`'s `deep_ids` gate: a goal leaf is
    transcribed only if the matching obligation went DEEP on the reference SST
    side (`raw_exp`). But `raw_exp` has NO quantifier arm (`ExpX::Bind` ⟶
    `raw-bind` fail-loud), so a quantifier-cored obligation never enters
    `deep_ids` ⟹ the Forall/Exists arm is UNREACHABLE today (activates only at
    the W7d def-body entry point). The whole golden suite (`golden_add_capped_cert`
    et al.) stays byte-identical at 351/0. (Note this is a DIFFERENT neutrality
    mechanism than Match's: Match was unreachable because SST desugars it;
    Forall/Exists because the SST reference has no quantifier arm.)
  - **Tests (2 new here):** `lexpr_to_exprdata_forall_nests_binders` (∀ i j : Int,
    pins the right-to-left `ExprData::Forall` nesting + `Int`-binder→`TyInt`
    recognition + interning order), `ltyp_to_typdata_recognizes_types`
    (Prop/Nat/Int/named-datatype/`Tactus.Ref`/fail-loud — pins the recognizer
    contract incl. the documented `Nat`-gap boundary).
  - **NEXT (surviving W7c remainders):** multi-arg `AppN` (needs the deferred
    cache-churning `RawList` per-arg-`TypData` edit for a faithful auto-borrow
    `render_list`; single-arg `App`/`Call` already covers the fixture) + datatype
    (`RawDt`/`DtData`) + def-header — then W7d wires the def-body entry point + the
    e2e `def_eq` bridge (the real cross-side validation of Match AND Forall/Exists).

- (2026-07-15, opus-w7c-defhdr) **Production def-HEADER `ldef_to_defdata` LANDED**
  (split to `bootstrap-30`, DONE; lib suite 351→354/0, verdict-neutral).
  `lean_ast::Def → lib.DefData` — `text_leaf(name)` + `def.binders`→`ParamList`
  (`ltyp_to_typdata`) + `ltyp_to_typdata(ret_ty)` + `lexpr_to_exprdata(body)`.
  Paired with the reference `raw_vir_def` (`bootstrap-29`). Fixture-covering DEF
  surface (header + Ite/Match body) now complete on the production side for
  monomorphic defs; W7d can bridge `def_eq` on `tri`. **Fork decision recorded:**
  multi-arg AppN stays deferred (the ONLY remaining W7c piece needing the
  cache-churning `RawList` per-arg-`TypData` edit; tgt-slice-only — fixture calls
  are single-arg). Surviving remainders: AppN (batched) + datatype
  (`RawDt`/`DtData`; no `tactus-core` edit; Box→`TyBox` subtlety).

- (2026-07-15, opus-w7c-dt) **Production datatype `ldt_to_dtdata` + `ldt_field_typdata`
  LANDED** (split to `bootstrap-31`, DONE; lib suite 354→359/0, verdict-neutral).
  `lean_ast::Datatype → lib.DtData` — `text_leaf(name)` + per-variant
  `text_leaf(ctor)` + positional field types via `ldt_field_typdata`, which
  recognizes the KEPT `Box`: `App(Var "Tactus.Box", [T]) → TyBox(intern(pp(T)))`
  (else delegate to `ltyp_to_typdata`). Only multi-variant `Inductive`/
  `IndexedInductive` handled; single-variant `Structure` fails loud
  `ed-dt-struct`. Paired with the reference `raw_vir_dt` (`bootstrap-29`); id
  agreement by construction (`lean_name`/`sanitize`/`typ_to_expr`↔`ltyp_to_typdata`).
  The Box→TyBox subtlety (W7a §7 Q4) is the technical crux: the field keeps its
  box (the recursion goes through it), unlike the value-position cast layer that
  peels it. **Fixture-covering DEFINITIONS surface (def header + Ite/Match body +
  datatype) now complete on the production side.** Only surviving W7c remainder:
  multi-arg AppN (the cache-churning `RawList` edit; tgt-slice-only).

## Writeup

_partial — `Ite` + `Match` + `Forall`/`Exists` constructors landed on both
transcriber sides (verdict-neutral, tests green, lib suite 351/0). The
fixture-covering body set (leaf/Ite/Match) is complete; the first tgt-slice-only
constructor (quantifiers) is now done too, incl. the `ltyp_to_typdata` binder-type
recognizer (the §7-Q3-style fork, resolved with a documented usize/char→Nat
incompleteness that is uncertifiable-not-unsound). Remaining: multi-arg AppN
(deferred — its faithful `render_list` needs a cache-churning `RawList` per-arg
`TypData` edit), datatype (`RawDt`/`DtData`) + def-header transcription. See
Progress for the per-constructor open questions and the verdict-neutrality proof
method (Ite/Match: no obligation-position `ExpX::<new-node>`; Forall/Exists: the
SST `raw_exp` has no quantifier arm ⟹ never in `deep_ids`)._

_(superseded) partial — `Ite` constructor landed on both transcriber sides (verdict-neutral,
tests green). Remaining: Match, Forall/Exists, multi-arg AppN (+ deferred
per-arg coercion), datatype + def-header transcription. See Progress for the
per-constructor open questions and the verdict-neutrality proof method (fixture
source analysis: confirm no obligation-position `ExpX::<new-node>` before
landing each shared `raw_exp` arm)._
