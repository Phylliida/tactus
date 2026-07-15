---
title: "W5f v2 follow-on — faithful `Match` denotation: the flat-Int datatype-value-decode layer"
status: todo
claimed_by:
created: 2026-07-15T08:10:00Z
updated: 2026-07-15T08:10:00Z
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

## Writeup
