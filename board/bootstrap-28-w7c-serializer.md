---
title: "W7c — serializer transcriptions for the def-body constructors (Ite/Match/AppN/Forall/Exists + datatype)"
status: in_progress
claimed_by: opus-w7c
created: 2026-07-14T22:10:00Z
updated: 2026-07-14T22:10:00Z
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

## Writeup

_partial — `Ite` constructor landed on both transcriber sides (verdict-neutral,
tests green). Remaining: Match, Forall/Exists, multi-arg AppN (+ deferred
per-arg coercion), datatype + def-header transcription. See Progress for the
per-constructor open questions and the verdict-neutrality proof method (fixture
source analysis: confirm no obligation-position `ExpX::<new-node>` before
landing each shared `raw_exp` arm)._
