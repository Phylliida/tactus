---
title: "W7a — defs-layer probe: freeze the extended body vocabulary (Match/Ite/Forall/multi-arg App) + DefData/DtData on tri + Tree; zero shared-crate risk"
status: done
claimed_by: opus-w7a
created: 2026-07-14T21:45:00Z
updated: 2026-07-14T22:55:00Z
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
- (2026-07-14, opus-w7a) **DONE.** Read the REAL emitted fixture defs first
  (`TactusDefs_lib_exec__{root,base}.lean`) — `tri`/`tree_head`/`Tree`/
  `Tree.height` verbatim as ground truth (`sum_tree` is pruned — no caller).
  De-risked the two novel Lean mechanics with throwaway tests BEFORE writing the
  probe: (1) `mutual` inductive + `deriving instance DecidableEq` → `decide`/`rfl`
  reduce, axioms clean; (2) a `mutual` structural `render` recursing through the
  arm-list/expr-list → reduces under `decide`/`rfl`, **no `WellFounded.fix`**.
  Both green, so the Match/AppN nested recursion is safe. Wrote
  `probe15_w7a_defs.lean` (~30 theorems) + `run.sh` + `REPORT.md`. Probe rc=0,
  every `#print axioms` clean, non-vacuity meta-check passes. One parse snag:
  `/-- -/` doc comments can't attach to `mutual` — switched those three to plain
  `/- -/`. Zero `tactus-core` edits.

## Writeup

**Result:** `probe15_w7a_defs/` lean **rc=0**, all axioms clean, non-vacuity
meta-check passes. Case A (`Ite` via `tri`) + Case B (`Match` via
`tree_head`+`sum_tree`) + Case C (`Tree` datatype + `height`) each correct-close
(`decide`+`rfl`) with multiple non-vacuous mutation-kills; `Forall`/`AppN` frozen
+ synthetically validated. Full spec, frozen vocabulary (pasted Lean inductives),
§7 verdicts, and the definition-level census are in **`REPORT.md`**. Highlights:

- **Frozen W7b vocabulary** (additive to W6): `TypData` += `box`; `ExprData`/
  `RawExp` += `ite` / `matchE`(+`MatchArm`/`ArmList`) / `appN`(+`ExprList`) /
  `forallE` / `existsE`; new top-level `DefData`/`RawDef`/`DtData`/`CtorData`/
  `RawDt` + `render_def`/`render_dt`. `Match`/`AppN` recurse through dedicated
  list inductives (production's `RawExpList` discipline) so `render` is
  structural and kernel-reduces. No `HasType` (obligation-goal construct).

- **§7 verdicts:** (Q1) arm-binder ids are part of structural eq, ride through
  `render`, and the production nat-returning `arms_eq` (match-first-arg +
  tag/projection + recurse) `decide`s — demonstrated by `B_th_binder_kill` +
  `Q1_arms_eq_{closes,kills}`; wildcards get a canonical positional id.
  (Q2) `def_eq` is syntactic → never reduces the callee, so a body calling
  `height` (or itself) `decide`s fine (`C_height_ok_decide`) — height's
  kernel-computability is irrelevant to the bridge. (Q3) flat `appN` arg list;
  per-arg coercion at the expected param type is **deferred to W7c** (no fixture
  body is multi-arg) — flagged, not dropped. (Q4) `CtorData` = positional field
  TYPES only; **`Box<T>` gets its own `TyBox`, NOT reused `TyRef`** (Box≠Ref;
  conflation would mask a field-kind bug).

- **Census (definition-level):** `Ite`→`tri`; `Match`→`tree_head`/`sum_tree`/
  `Tree.height`; `TyBox`→`Tree`/`sum_tree`/`Tree.height`; `AppN`+`Forall`/
  `Exists`→**no fixture body** (fill_zeros' forall is goal-level), so
  tgt-slice-only (W7d). `sq`/`Point.height` are W6-vocab-complete. Full table in
  REPORT.

**Assumptions:** `sum_tree` (Case B′) is a PREDICTED shape (pruned from the
fixture — no caller), composed mechanically from the source + tree_head/height
patterns; not emitted-verified. Datatype "render" is transcription not decision
(teeth = VIR-vs-LExpr diversity, abstracted as two hand inputs). Monoculture
caveat unchanged (W5's residual). See REPORT §"Assumptions / honesty".

**Blocks:** W7b (the batched shared-crate edit) — shapes now frozen, safe to start.
