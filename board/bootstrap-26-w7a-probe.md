---
title: "W7a — defs-layer probe: freeze the extended body vocabulary (Match/Ite/Forall/multi-arg App) + DefData/DtData on tri + Tree; zero shared-crate risk"
status: todo
claimed_by:
created: 2026-07-14T21:45:00Z
updated: 2026-07-14T21:45:00Z
---

## Description

The W7 probe — the exact analog of W6a (`bootstrap-20`). Prove the defs-layer
bridge mechanic end-to-end in a **standalone `.lean`** (no `tactus-core` edit, so
zero cache churn) and **freeze the W7b mirror shapes** so the one batched
shared-crate edit lands once. Spec + rationale: `DESIGN-W7-defslayer.md` (esp.
§3.1 the ExprData-superset, §4 the mirrors, §6 the ladder, §7 open questions).

Concretely, in a new `probe-w0/probe15_w7a_defs/` (mirror `probe12_w6a_castleaf/`):

1. **Extended expression vocabulary.** Hand-write a Lean `ExprData` + `RawExp`
   (or reuse the frozen W6 ones and *extend*) with the new body constructors:
   `Match` (scrutinee + arms, each arm = ctor id + bound-var ids + arm body),
   `Ite` (cond/then/else), `Forall`/`Exists` (binder id + typ + body), and a
   multi-arg `App` (fn id + `RawExpList` args — reuse the W6 list shape). Keep
   atoms interned `u64` (the §2.1 safety condition — a forgotten node is a shape
   diff).
2. **DefData / RawDef + render_def.** `DefData = Def(name, params, ret, body)`,
   `RawDef = RDef(name, params, ret, RawExp)`; a small independent `render_def`
   that lowers `RawDef → DefData` (structural; the diversity is that it does NOT
   share production's renderer). `def_eq` built from the frozen `expr_eq`+`typ_eq`.
   **Real fixture bodies (`bootstrap-fixture/lib.rs`), pick per constructor:**
   - `tri(n) = if n == 0 { 0 } else { n + tri((n-1) as nat) }` → the **`Ite`**
     exemplar (first-class if + recursive `Call` + `Clip` + `BinOp`); everything
     but `Ite` is already in W6's vocab, so `tri` is the minimal Ite probe.
   - `tree_head(t) = match t { Leaf(v)=>v, Node(_,_)=>0 }` → the **simplest
     `Match`** (2 arms, a binder + wildcards, no recursion).
   - `sum_tree(t) = match t { Leaf(v)=>v as nat, Node(l,r)=>sum_tree(*l)+
     sum_tree(*r) }` → the **`Match` + recursion + `Clip` + Box-`Deref`** exemplar.
   - `Tree = Leaf(u64) | Node(Box<Tree>, Box<Tree>)` → the datatype + height case.
3. **Case A — `Ite` via `tri`.** `decide` the correct `RawDef`→`render_def`
   equals the production-style `DefData`; each mutation FAILS — (a) swap the
   then/else branches, (b) drop the recursive `tri` call, (c) `+`↔`-` opcode,
   (d) drop the `Clip`(`as nat`) on `(n-1)`.
4. **Case B — `Match` via `tree_head` + `sum_tree`.** `decide` correct-closes;
   mutations FAIL — (a) wrong arm value / swapped arms, (b) a forgotten `Match`
   (bare arm / dropped scrutinee), (c) `sum_tree`: dropped recursive call or a
   swapped Box-`Deref`. Fix the arm-binder-id discipline here (design §7 Q1).
5. **Case C — `Tree` datatype + its height fn.** `DtData = Dt(name, ctors)` with
   the fixture's `Tree` ctors (positional field TypData only — no accessor names,
   design §7 Q4). Model `Tree.height` as a `DefData` whose body is `Match`→`Nat`
   (design §4 "MODEL AS A DefData"); `decide` correct-closes + a ctor-swap /
   wrong-measure mutation-kill.
6. **Definition-level census.** Enumerate the spec fns + datatypes referenced by
   the 13 fixture certs (grep the emitted `probe9`/fixture certs for `lib.<name>`
   applications and the `inductive`s in the emitted oleans) → map each to the
   body constructors it uses → the W7b coverage roadmap (N4 was statement-level;
   W6a was expression-leaf-level; this is definition-level). Record in the writeup.

Keep it pure-kernel `decide` (no `WellFounded`/`Classical` in the axiom closure —
`#print axioms` clean, as W6a did); confirm mutation-kills are non-vacuous (the
FAIL side actually reduces to `= 0`, not `stuck`).

**Answer the design §7 open questions as you go** and record the verdicts:
Match-arm binder-id discipline; whether `def_eq` over a body that *calls* a
height fn `decide`s without reducing the callee (it should — `def_eq` is
syntactic); flat-vs-curried multi-arg shape; datatype positional-vs-named fields.

**Done when:** `probe15_w7a_defs/` `lean` rc=0, axioms clean; Case A + Case B each
have a correct-closes and ≥1 non-vacuous mutation-kill; the extended vocabulary
(the exact `ExprData`/`RawExp`/`DefData`/`DtData` shapes) is written down as the
frozen W7b target; the definition-level census is recorded. **Zero `tactus-core`
edits** (standalone probe only).

**Blocked by:** nothing (W6 done, machinery in place). **Blocks:** W7b (the
batched shared-crate edit) — do not start W7b until this probe freezes the shape.

## Progress

- (2026-07-14, opus-w7) Created at W7 design landing. Probe target chosen: `tri`
  (already in the fixture as `lib.tri (Int.toNat n)` in `sum_to`'s leaf) + the
  `Tree` inductive / `tree_head` (also fixture-present). Reference probe to mirror
  structurally: `probe-w0/probe12_w6a_castleaf/`.

## Writeup

_when done: the frozen extended-vocabulary shapes (paste the final Lean
inductives), the §7 open-question verdicts, the definition-level census, and
confirmation the mutation-kills are non-vacuous._
