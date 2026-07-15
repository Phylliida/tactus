---
title: "W5f v2 follow-on — faithful `Match` denotation: the flat-Int datatype-value-decode layer"
status: done
claimed_by: opus-bootstrap56-matchdecode
created: 2026-07-15T08:10:00Z
updated: 2026-07-16T01:30:00Z
---

## Description

Spun out of bootstrap-55 (W5f v2, probe28). v2 gave faithful `eval`/`edenote`
denotations to four of the five W7 body constructors (`App`/`AppN`, `Forall`,
`Exists`, `Ite`); **`Match` (`ExprData.Match` / `RawExp.MatchR`) is the one node
left as a sentinel** (`0` / `True`).

Why it's hard, and separate: the W5f state model is flat-Int (`St := Int → Int`);
every value — including a user-datatype value — is an `Int`. To denote
`match scrut { Ctor pats => arm … }` faithfully you must **decode the scrutinee
`Int` back to a constructor tag + field values** (the inverse of the `emb : U →
Int` embedding used at the `Forall`/`All` binder), select the matching arm, and
bind the pattern vars (`ArmList.Cons ctorId binderIds body`) into the threaded
state before recursing into the arm body. That is a genuine datatype-value-decode
layer, not a one-arm add.

**Note (why this is low-urgency):** the v2 grounding realization means a
match-*bodied* spec fn is already handled — its `match` is inside the emitted Lean
def `lib.<fn>`, reached through the pinned `E.fn`/`E.fnN` oracle, so `eval` never
interprets it. This card only matters for a `match` appearing **directly in an
obligation goal** (a `LeafE`), which is rare. Confirm the frequency on the fixture
+ tgt obligation slice before investing (a census like W6a/W7a).

## Design notes (starting points)

- The decode oracle likely lives in the `SymEnv`: e.g. `ctorTag : Int → Int`
  (scrutinee value → constructor id) + `ctorField : Int → Nat → Int` (value, field
  index → field value), pinned in the crate literal consistently with how the
  emitter encodes constructor applications. Then `eval (Match s arms)` walks
  `arms`, picks the arm whose `ctorId` matches `ctorTag (eval s)`, binds
  `binderIds` to `ctorField (eval s) i`, and recurses.
- Needs a mutual companion `evalArms`/`edenoteArms` over `ArmList` (the same
  mutual-structural pattern `eval`/`evalList` already use for `AppN` — watch the
  `:= rfl` unfold-lemma discipline: a type error in ANY mutual arm silently breaks
  every arm's `rfl` lemma, cf. bootstrap-55's `.deref` bug).
- Faithfulness bridge target: a `match`-in-obligation over a real `render_exp`
  output, `rfl`/`simp only`-closing to the user's `match`-expression Prop, all over
  `[propext, Quot.sound]`.
- Cross-check the constructor encoding against the W7 datatype mirror (`DtData` /
  `render_dt`) + the emitter's accessor emission (`Foo_val0`) so the decode oracle
  and the emitted constructor encoding agree by construction.

## Progress

- (2026-07-16, opus-bootstrap56-matchdecode) **Claimed.** Read probe28
  (`probe-w0/probe28_w5f_v2/w5f_v2_sem.lean`), the real emitted `ExprData`/
  `ArmList`/`BinderIdList` shapes + `render_exp`/`render_arms` (`tactus-core/out/lib`
  `TactusDefs_lib_exec__{base,root}.lean`), and the coercion helpers
  (`needs_nat_coercion`/`coerce_if`/`type_of`).

- **CENSUS (the card's required pre-check — "how often is `Match` DIRECTLY in an
  obligation goal / LeafE").** Grepped every emitted `.lean` in the tree for
  `MatchR`/`ExprData.Match`. Occurrences fall into exactly three buckets:
  1. the datatype/def machinery itself (`height`/`render_arms`/`expr_eq`/`expr_size`
     in `__base.lean`/`__root.lean`) — definitions, not goals.
  2. `defs_expr_vocab_kernel_computes` — the deliberate `render_exp` **vocab test**
     (exercises MatchR on purpose).
  3. `target/tactus-lean/lib/cert/tree_head.defcert.lean` — a **`DefData` BODY**
     cert (`render_def cert_tree_head_raw = cert_tree_head_defdata`), i.e. `Match`
     inside a spec-fn body reached through the pinned `E.fn` oracle — NOT a
     `GoalData.LeafE`.
  **Result: zero `Match`-directly-in-obligation on the available slice.** Confirms
  the card's low-urgency note (bodies are handled by the fn-pin). The value of this
  task is therefore *completeness* — making `eval`/`edenote` faithfully TOTAL over
  the full `ExprData` vocab (no sentinel), the last honest gap — not coverage of a
  common goal shape. Danielle's steer (clean foundation before hardening pins)
  agrees, so proceeding to implement the decode layer.

- **Decode-layer design (settled).** The flat-Int `St` model can't structurally
  decode a datatype value, so the decode is via two NEW `SymEnv` oracle fields —
  `ctorTag : Int → Int` (scrutinee value → ctor id) and `ctorField : Int → Nat →
  Int` (value, field idx → field value) — pinned by the concrete crate literal
  consistently with the emitter's constructor encoding (same P5/oracle discipline
  as `fn`/`fnN`). Then:
  - `bindArm E v bs i st` — standalone structural fold over `BinderIdList`,
    threading `upd st bᵢ (E.ctorField v i)`.
  - `evalArms` joins the `eval`/`evalList` **mutual** block (`eval (Match s arms) =
    evalArms E (eval s) arms`; `evalArms (Cons c bs body tl) = if ctorTag v = c then
    eval body (bindArm …) else evalArms … tl`).
  - `edenote`/`edenoteArms` become a mutual pair (prop-position mirror).
  - Faithfulness facts state arm-SELECTION + binder-THREADING — the same honest
    register as FACT 6 (`Forall`): the leaf reads the threaded slot via `E.av`,
    resolved at instantiation exactly like `toProp_all_embed`, NOT reduced to a
    numeric value here.
  Building as `probe-w0/probe29_w5f_v2_match/` (extends probe28).

- **DONE ✓ (probe29, rc=0, ~3.7s)** over the REAL emitted `lib.render_exp`/
  `lib.render_arms`. The decode layer landed on the first structural attempt
  (`termination_by structural` mutual triple eval/evalList/evalArms + mutual
  edenote/edenoteArms + standalone bindArm — all `:= rfl`-reducible unfold lemmas);
  the only hiccup was one missing paren on the `RawArmList.Nil` tail-box line
  (needs 5 closes to match its `ArmList.Nil` counterpart). Three new facts:
  `adequacy_leaf_match_hd` (tag→arm0 select + binder thread), `_match_tl` (miss
  arm0 → walk to arm1), `_match_prop_hd` (prop-position edenoteArms). Each closes
  over `[propext]` only — no `sorryAx`, no `Classical.choice`. All 10 carried
  probe27/28 facts unchanged. `eval`/`edenote` now faithfully TOTAL over the full
  ExprData vocab. Report: `probe-w0/probe29_w5f_v2_match/REPORT.md`.

## Writeup

**Done (probe29 `w5f_v2_match_sem.lean` + REPORT.md).** The last sentinel node of
the W5f v2 leaf denotation — `ExprData.Match` — is now faithfully denoted, over the
real `lib.render_exp`/`lib.render_arms`, closing over standard axioms only.

**Census first (the card's required pre-check).** Grepped every emitted `.lean` for
`Match`/`MatchR`: the only occurrences are (1) the datatype/def machinery, (2) the
`defs_expr_vocab` vocab test, (3) `tree_head.defcert.lean` — a `DefData` **body**
cert reached via the `E.fn` oracle, **not** a `GoalData.LeafE`. **Zero `Match`-in-
obligation on the available slice**, confirming the card's low-urgency note. So this
rung's value is *completeness* (`eval`/`edenote` faithfully total over the full
vocab — the last honest gap), not coverage; Danielle's steer (clean foundation
before hardening pins) agreed, so it was worth doing.

**How the code works.** The flat-Int `St := Int → Int` model stores every datatype
value as an `Int`, so a faithful `match` must decode that Int. Two new `SymEnv`
oracles — `ctorTag : Int → Int` (value → ctor id) and `ctorField : Int → Nat → Int`
((value, field idx) → field value) — are pinned by the concrete crate literal
consistently with the emitter's constructor encoding (same discipline as `fn`/`fnN`;
they are the flat-Int inverse of the `emb : U ↪ Int` embedding at the `Forall`
binder). `bindArm` (standalone structural fold over `BinderIdList`) threads the
matched arm's binders (`upd st bᵢ (ctorField v i)`). `evalArms` joins the
`eval`/`evalList` mutual structural block (`eval (Match s arms) = evalArms E (eval s)
arms`; the `Cons` arm is `if ctorTag v = c then eval body (bindArm …) else evalArms
… tl`). `edenote`/`edenoteArms` become a mutual pair (prop-position mirror). All the
`termination_by structural` defs reduce definitionally (the `:= rfl` unfold-lemma
discipline), so the facts close by `rw`/`simp only`/`if_pos`/`if_neg`.

**The three facts** (shape: scrutinee `Var (TyNamed 100)`; arm0 `c0 binds [xId] ⇒
xId`, arm1 `c1 binds [yId,zId] ⇒ 0`; result `TyInt` ⇒ no arm-body coercion):
- `adequacy_leaf_match_hd` (VALUE): `ctorTag v = c0 ⇒ eval(render(match)) = E.av
  xId (upd st xId (ctorField v 0))` — arm0 selected, binder bound to field-0, read
  back through the threaded state. Exercises BOTH new mechanisms at once.
- `adequacy_leaf_match_tl` (VALUE): `ctorTag v ≠ c0 ∧ = c1 ⇒ eval = 0` — the arm
  WALK past arm0 to arm1.
- `adequacy_leaf_match_prop_hd` (PROP): the `edenote`/`edenoteArms` mirror.

**Assumptions / honesty.**
- `ctorTag`/`ctorField` are **pins, not proofs** — the flat-Int inverse of the
  emitter's constructor encoding, discharged by the crate `SymEnv` literal exactly
  as `fn`/`fnN`/`av`/`opk`/`proj` are. The facts take the `ctorTag` value as a
  hypothesis (as FACT 5/8 take `hfn`/`hfnN`); the honest content is arm SELECTION +
  binder THREADING, with the body's leaf read resolved at instantiation like
  `toProp_all_embed` — NOT a re-proof of datatype semantics.
- `eval`/`edenote`/`evalArms`/`edenoteArms`/`bindArm` are definitions we wrote →
  spec-adequacy (§8.5), audited-once, not trusted.
- The no-match default (`0`/`True`) is the total-function fallback; a well-typed
  exhaustive match always hits an arm.
- Census is over the emitted slice (fixtures + one real defcert), not the full tgt
  corpus — a strong signal, not an exhaustive proof.

**Follow-on (optional, shared with FACT 5/8).** A cross-crate probe that pins the
oracles — now including `ctorTag`/`ctorField` — to a real fixture-emitted datatype
+ spec-fn encoding rather than a hypothesis, over its own `render_exp`/`render_def`
output.
