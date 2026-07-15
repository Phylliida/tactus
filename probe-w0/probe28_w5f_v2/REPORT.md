# probe28 — W5f v2: adequacy spine widened to the W7 body fragment (board bootstrap-55)

**Status:** PASS ✓ (rc=0, ~3.5s, `lean` against the real emitted `lib.*`).
**Axiom closures:** all v1 facts carry over unchanged; the v2 facts —
`adequacy_leaf_app_grounded` `[propext]`, `adequacy_leaf_forall` *(none)*,
`adequacy_leaf_exists` *(none)*, `adequacy_leaf_ite` `[propext]`,
`adequacy_leaf_appn_grounded` `[propext]`. No `sorryAx`, no `Classical.choice`
— `render_exp`/`edenote`/`eval`/`evalList` all kernel-reduce (mutual structural),
the Ite condition is decidable (`Int.decEq`, constructive), the quantifiers are
genuine `∀`/`∃`, the fn grounding is a plain oracle application.

Run: `probe-w0/probe28_w5f_v2/run.sh` (`LEAN=<lean>` to override). Elaborates
`w5f_v2_sem.lean` against `tactus-core/out/lib` — NO tactus-core rebuild. Extends
probe27 (the full v1 Val-level core + four v1 adequacy facts are carried verbatim).

## What v2 adds

probe27 (W5f v1) pinned a concrete leaf denotation `edenote`/`eval` covering the
**arithmetic/logical obligation fragment** (atoms, literals, arith, comparisons,
connectives, Int↔Nat casts, unary apps, field projections, goal-side let,
span-marks). The **W7 body constructors** — `Ite`, `Match`, `AppN`, `Forall`,
`Exists` (the `ExprData` nodes that appear in spec-fn *bodies* and quantified
obligations) — were stubbed to sort-error sentinels.

v2 widens `eval`/`edenote` to **faithful** denotations for **four of the five**
body constructors (`App`/`AppN`, `Forall`, `Exists`, `Ite`), leaving `Match`
scoped (see below). `eval`/`edenote`/`evalList` are now **total** over the full
`ExprData` vocabulary.

## The design decision (the card's fork) — grounding is a SymEnv fn-pin, NOT an interpreter

The card asked how `E.fn` gets "grounded in the emitted `render_def` bodies", and
whether v2 should co-locate with the W7 defs-certificate machinery. **Resolution:**

> A faithful leaf denotation does **not** interpret spec-fn bodies with an in-Lean
> `DefData` evaluator. That evaluator **can't be a structural `def`**: a recursive
> spec fn's body re-enters its own call, so `eval` would need fuel / a fixpoint.
> Instead — exactly the P5 shape (`probe5_symenv.lean`) — the concrete per-crate
> `SymEnv` literal **pins** `fn`/`fnN` to the **already-emitted Lean spec fns**
> (`crateEnv.fn | tri_id => lib.tri | …`). Recursion + termination live in the
> emitted defs (certified structural by W1.5); `eval`/`evalList` stay
> **structural** — each `App`/`AppN` arm is ONE oracle application over
> recursively-eval'd args. The rfl-bridge closes because the concrete env literal
> kernel-reduces (P5: `gdenote crateEnv … = (… myDouble x …) := by rfl`).

**Co-location is NOT required.** The denotation layer needs only that the emitted
Lean defs *exist* (W7 emits them) and are *pinned* in the crate `SymEnv` literal —
it is independent of W7's `def_eq` **syntactic** bridge (which never reduces
bodies; open question §7.2). W5f v2 is the **denotational** counterpart to W7's
syntactic one.

**A consequence that shrinks the work:** a match-bodied fn (`tri`) is grounded
through `fn tri_id = lib.tri`, so a *call* to it denotes `lib.tri (av n)`
**without `eval` ever interpreting the `Match` node** — the match is inside
`lib.tri`, which reduces on its own. So eval-level `Match`/`Ite`/`Forall`/`Exists`
interpretation is only needed for those nodes appearing **directly in obligation
goals** (a LeafE), not in bodies (bodies denote via the pinned fn oracle).

## The denotations (all over the REAL `lib.render_exp` lowerings)

- **`App` / `AppN`** (`RawExp.Call`→`App`, `RawExp.CallN`→`AppN`): value =
  `E.fn f (eval a)` / `E.fnN f (evalList args)`. `eval`/`evalList` are now a
  **mutual structural pair** (`AppN` folds its arg list). The oracle is pinned to
  the real defs in the crate literal. *(FACT 5, FACT 8.)*
- **`Forall` / `Exists`** (`RawExp.ForallR`/`ExistsR`): genuine `∀ n:Int,` /
  `∃ n:Int,` binding the var into the body denotation via `upd st x n` — for ANY
  body, so it **composes** through nesting. The Int→user-type narrowing is the
  existing `toProp_all_embed`. *(FACT 6, FACT 6b.)*
- **`Ite`** (`RawExp.Ite`): the O9 value/prop split resolved by a **decidable**
  Bool-as-Int condition — `eval (Ite c t e) = if eval c ≠ 0 then eval t else
  eval e`, with `eval c ≠ 0` decidable on `Int` ⇒ **no `Classical`**. Comparison
  / connective ops now carry a decidable Bool-as-Int value so an Ite whose
  condition is a comparison denotes faithfully (`eval c ≠ 0 ↔ edenote c`).
  *(FACT 7.)*
- **`Match`** (`RawExp.MatchR`): **scoped** for this rung (sentinel `0` / `True`).
  Picking an arm in the flat-Int `St` model requires **decoding the scrutinee Int
  back to a constructor+fields** (the inverse of the `emb : U → Int` embedding) —
  a genuine datatype-value-decode layer. It mostly lives in bodies (⇒ handled by
  the fn pin) and is rare directly in obligations, so it is a documented follow-on
  (`board/bootstrap-56-w5f-v2-match-decode.md`).

## The six new / carried facts

| # | Fact | What it pins | Axioms |
|---|---|---|---|
| 1–4 | *(v1)* `adequacy_leaf_cmp` / `_overflow` / `toProp_all_embed` / `soundness_concrete` | the arith/logical fragment + the spine | carried |
| 5 | `adequacy_leaf_app_grounded` | `edenote(render(g(n) < 10)) ↔ g(av n) < 10`, `g := E.fn fId` | `[propext]` |
| 6 | `adequacy_leaf_forall` | `edenote(render(∀i. body)) ↔ ∀n, edenote(render body)(upd st i n)` | *(none)* |
| 6b | `adequacy_leaf_exists` | the `∃` mirror | *(none)* |
| 7 | `adequacy_leaf_ite` | `eval(render(if b then x else 0)) = if av b ≠ 0 then av x else 0` | `[propext]` |
| 8 | `adequacy_leaf_appn_grounded` | `edenote(render(h(m,n) < 100)) ↔ h [av m, av n] < 100`, `h := E.fnN fId` | `[propext]` |

FACT 5 / FACT 8 are the **grounding** headline: a spec-fn call in an obligation
denotes the real fn applied to the (recursively-eval'd) arg values; instantiating
`g`/`h` to the actual `lib.<userfn>` makes it read EXACTLY as the user's Prop.
FACT 6 / 6b are the binder-threading (composes with the goal-level All arm).
FACT 7 resolves the value/prop sort split constructively.

## Honest scope / what's partial

- **`Match` is not faithfully denoted** (the one remaining body node). It needs the
  flat-Int datatype-value-decode layer — spun out as `bootstrap-56`. The fn-pin
  handles match-*bodied* fns already, so this only bites `match`-in-obligation.
- `eval`/`edenote` are **definitions we wrote** → spec-adequacy (master plan §8.5),
  audited-once, not trusted. They re-prove no Val-level math; faithfulness to the
  user Prop is the `rfl`/`simp only`-bridge, validated on the grounded-call,
  quantifier, and Ite classes.
- The grounded facts are stated with `g`/`h` as hypotheses (`E.fn fId = g`) exactly
  as v1's `adequacy_leaf_cmp` takes `hop : E.opk ltId = OpKind.lt`; the concrete
  crate `SymEnv` literal discharges them by `rfl`/`decide` (the P5 argument). A
  cross-crate probe pinning to an actual fixture-emitted `lib.<fn>` (rather than a
  hypothesis-`g`) over its own `render_exp` output is a natural strengthening.
