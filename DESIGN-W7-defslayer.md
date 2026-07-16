# DESIGN — W7: defs-layer certificate

Status: **design landed, ladder split** (2026-07-14, opus-w7). Parent card:
`board/bootstrap-12-w7-defs-layer.md`. Reuses the W6 stage-B machinery
(`DESIGN-W6-stageB.md`). Spec source: `DESIGN-bootstrap.md` §5 (W7 row) + §7.

## 1. What W7 certifies

W2–W6 certify **obligations** (the WP goals `refWp` produces for an exec fn).
W7 certifies **definitions** — the spec-world artifacts the emitter produces and
that everything downstream is stated *in terms of*:

- **spec-fn bodies** — `@[reducible] def <name> <params> : <ret> := <body>`
  emitted by `to_lean_fn.rs`;
- **datatype declarations** — `inductive <T> where | Ctor (f : Ty) …` emitted via
  `dep_order.rs` / `to_lean_type.rs`;
- **height / structural-measure fns** — the recursive `<T>.height` spec fns
  (`expr_shared.rs`, `dep_order.rs §495`) that W1.5's `termination_by structural`
  work makes kernel-computable.

These are **trust-inventory row 4** (the "remaining half" per §5 W7 row). Today
they are *trusted*: production renders them and nothing checks the rendering. A
**wrong-but-consistent** def translation — say the emitter lowers a spec `match`
arm to the wrong constructor, but does so uniformly so every *user* of the def
reads the same wrong thing — is a model-drift bug that no obligation-level bridge
catches, because both the obligation and the def share the same wrong denotation.

## 2. The central fork (resolved) — same lesson as W6d

**The reference definitional translation MUST be an independent second
implementation of the VIR-body→Lean-def lowering.** This is the W6d lesson
verbatim (`DESIGN-W6-stageB.md`: "if both sides call `to_lean_sst_expr` you only
verify the renderer is deterministic"). If W7's reference `render_def` just
re-invokes production's `to_lean_fn` renderer, the bridge proves determinism, not
faithfulness. So:

- **Production side** emits a `DefData` mirror by transcribing the emitted `LExpr`
  body (reuse W6c's `lexpr_to_exprdata`).
- **Reference side** (`render_def` in `tactus-core`) recomputes a `DefData` from a
  `RawDef` transcribed *directly from VIR* (`vir::sst`/`vir::ast` spec body) —
  NOT through `to_lean_sst_expr`. This is the diversity that gives the bridge
  teeth.
- **Bridge** `decide`s `def_eq(render_def(raw), def_data) = 1` per emitted def.

Honest value statement (inherited from W6): W7 catches an *inconsistent* or
*wrong* independent lowering (Friction-class), not a rule both the emitter and the
reference implement identically-wrong (monoculture) — that residual is W5.

## 3. Key reuse finding — a spec-fn body IS an expression

The body slot of a `DefData` is exactly the W6 `ExprData`/`RawExp`. So W7 reuses:
`render_exp`, `lexpr_to_exprdata` (production transcription), `expx_to_rawexp`
(reference transcription), the opcode table, `expr_eq`, and the `TypData` type
mirror — *the entire W6 stage-B core*. W7's genuinely-new surface is small: the
def **header** (name + typed params + ret type — TypData already exists), the
**datatype** decl mirror, and the **height** measure.

### 3.1 The one real cost: ExprData is a STRICT SUBSET of what bodies need

W6's `ExprData`/`RawExp` (lib.rs:282/310) covers exactly the obligation-leaf
constructors it met: `Var/Lit/LitBool/Clip(Cast)/BinOp/Call(App)/Field/HasType/
Deref/Let/Not/Span`. Spec-fn bodies use MORE:

| Body construct | In W6 vocab? | W7 action |
|---|---|---|
| `match e { Ctor pats => arm … }` | **no** | add `Match` (the big one — inductive spec fns are match-bodied) |
| `∀ / ∃` quantifiers | **no** (GoalData::All is goal-level only) | add `Forall`/`Exists` expr nodes |
| first-class `if c then a else b` | **no** (W6 G4 folded If→Let) | add real `Ite` node |
| multi-arg application `f a b c` | **partial** (`Call`/`App` single-arg; type-args dropped) | generalize to an arg *list* (reuse `RawExpList`) |
| lambda / closure body | **no** | **defer, fail-loud** (out of initial scope) |

**Discipline consequence:** each new constructor is an *additive `tactus-core`
edit* → base-hash change → whole-crate re-verify + olean re-emit (the caching
doc's "datatypes are all-or-nothing"). Therefore W7 must add **all** the
body-constructor deltas in **one batched W7b edit**, not incrementally — exactly
the W6b discipline, but with a bigger single batch. Probe (W7a) freezes the full
extended vocabulary BEFORE that edit so it lands once.

## 4. The new top-level mirrors (W7b shapes to freeze in W7a)

```
// def header + body (spec-fn definition)
enum DefData  { Def(u64 /*name*/, BinderList /*typed params*/, TypData /*ret*/, ExprData /*body*/) }
enum RawDef   { RDef(u64, RawBinderList, TypData, RawExp) }     // reference input (from VIR)

// datatype declaration
enum CtorData { Ctor(u64 /*name*/, TypDataList /*field types*/) }
enum DtData   { Dt(u64 /*type name*/, CtorDataList) }
enum RawDt    { RDt(u64, RawCtorList) }

// height / structural measure: a recursive spec fn whose body is Match→Nat.
// MODEL AS A DefData (reuse) once Match lands — no separate HeightData needed.
```

`def_eq` / `dt_eq` are the structural equalities the bridge `decide`s, built from
`expr_eq` (bodies) + `typ_eq` (headers/fields) — all already in place from W6.

## 5. Scope / defer (fail-loud, like N4/W6)

- **In scope (initial):** non-recursive + structurally-recursive spec fns whose
  bodies use the §3.1 constructor set; single-inductive datatypes + their height
  fns; the fixture spec fns (`tri` = the `Ite` exemplar; `tree_head`/`sum_tree` =
  the `Match` exemplars, `sum_tree` adding recursion + `Clip` + Box-`Deref`) + the
  `Tree` inductive, and a tgt slice.
- **Deferred, serializer fails loud:** lambdas/closures in bodies; WF-terminating
  (non-structural) recursive spec fns whose Lean form is kernel-inert (W1.5 —
  `decide` can't reduce them, so the *bridge* can't `decide` `def_eq` on a body
  that contains a call to one; treat as a scope gap, log it); trait-method /
  assoc-type-projected bodies; mutual-recursion groups (dep_order `Mutual`) —
  land single defs first, then the mutual block.
- A **definition-level census** (which spec fns / datatypes appear in the fixture
  + tgt slice, and which body constructors each uses) is a W7a deliverable — the
  analog of W6a's expression-level roadmap. N4 was statement-level; it does not
  cover def bodies.

## 6. Ladder (board sub-tasks) — mirrors W6a…e

- **W7a** (`bootstrap-26`, next) — **probe, zero shared-crate risk.** Standalone
  `.lean`: hand-write the extended `ExprData`+`Match`/`Ite`/`Forall` + `DefData` +
  a tiny `render_def`, and `decide` that (a) a correct def closes — `tri` (the
  `Ite` exemplar) and `tree_head`/`sum_tree` (the `Match` exemplars) — and (b) a
  body mutation (swapped branch / wrong match arm / dropped recursive call /
  swapped ctor) FAILS. Also probe the `DtData` shape on the fixture `Tree`
  inductive + its height fn. Produce the definition-level census. **Freezes the
  full W7b vocabulary.**
- **W7b** — the ONE batched `tactus-core/lib.rs` edit: land `Match`/`Ite`/
  `Forall`/`Exists` + multi-arg `App` on `ExprData`/`RawExp`, plus `DefData`/
  `RawDef`/`DtData`/`RawDt` + `render_def`/`render_dt` + `def_eq`/`dt_eq`. Reuse
  everything else from W6. Re-emit oleans; keep probe9/13/14 green.
- **W7c** — serializer transcriptions: production `LExpr-def → DefData` (extend
  `lexpr_to_exprdata` for the new constructors) + reference `VIR spec body →
  RawDef` (extend `expx_to_rawexp`), plus the datatype transcriptions. Additive,
  census-gated, verdict-neutral (golden byte-identical), opcode/ctor-alignment
  invariant tests.
- **W7d** — wire both into def emission: production emits `DefData` alongside each
  `@[reducible] def`, reference emits `RawDef`→`render_def`, bridge `decide`s
  `def_eq` on the fixture defs + a tgt slice.
- **W7e** — mutation-kill: perturb a def body / a datatype ctor / a height measure
  on the production side ⟹ bridge must flip 1→0 (the row-4 model-drift kill).

**Done-when (parent):** spec-world definitions bridge-checked against the
reference translation for the fixture + a tgt slice; a perturbed def fails the
bridge. (= `bootstrap-12` "Done when".)

## 7. Open questions for W7a to answer

1. **Match arm equality** — does `decide` reduce `def_eq` over a `Match` whose
   arms bind pattern vars? (binder-id discipline: reference and production must
   intern arm-binder names identically, the W6b atom-id invariant one level up.)
2. **Height-fn inertness** — a structurally-recursive height fn emitted with
   `termination_by structural` reduces (W1.5); confirm the *bridge* can `decide`
   `def_eq` on a body that *calls* it (it should — `def_eq` compares syntax, not
   denotation, so it never reduces the callee; only W5 would). Record which side
   this bites.
3. **Multi-arg lowering** — production curries (`App` chains) vs. a flat arg list;
   pick the mirror shape (flat `RawExpList` recommended) and make the reference
   match production's currying so `def_eq` agrees by construction.
4. **Datatype field-name vs positional** — production accessors use field names
   (`Foo_val0`); the ctor mirror should carry positional field *types* only
   (names are an accessor-emission concern, a separate certifiable surface).
