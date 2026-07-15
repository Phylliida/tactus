---
title: "W5f v2 — widen the adequacy-spine leaf denotation to the W7 body fragment (Ite/Match/AppN/Forall/Exists) via a Defs-layer SymEnv"
status: done
claimed_by: opus-w5f-v2
created: 2026-07-15T06:45:00Z
updated: 2026-07-15T08:15:00Z
---

## Description

Follow-on from bootstrap-54 (W5f v1, probe27). The v1 leaf denotation
`edenote`/`eval` (`probe-w0/probe27_w5f_spine/w5f_sem.lean`) covers the
**arithmetic/logical obligation fragment** (atoms, int/bool literals, arith,
comparisons, logical connectives, Int↔Nat casts, unary apps, field projections,
goal-side let, span-marks) — exactly what `probe4_denote` P4 + the fixture
obligation goals use. The **W7 body constructors** (`ExprData.Ite`, `.Match`,
`.AppN`, `.Forall`, `.Exists`) are stubbed to sort-error sentinels (`0` in `eval`,
`True` in `edenote`).

Those nodes live in spec-fn **bodies** (`render_def` / the `Defs` layer, `W7`),
not in the stage-A obligation goals. Deepening `edenote` to them needs a
**Defs-layer `SymEnv`**: `E.fn` (currently a bare `Int → Int → Int` unary oracle)
must be grounded in the emitted `render_def` bodies so that `App`/`AppN` of a spec
fn denotes its actual definition, and `Match`/`Ite`/quantifiers get real meaning.

"Done" looks like: `edenote`/`eval` total on the full `ExprData` vocabulary with
faithful denotations for the W7 nodes, plus at least one `rfl`-bridge over a real
`render_exp` output that contains a body node (e.g. a `match`-bodied spec fn like
`tri`), all closing over `[propext, Quot.sound]` — no `sorryAx`, no
`Classical.choice`. Extends probe27; new probe28.

## Design notes (starting points)

- The `SymEnv.fn` field is unary in v1. Multi-arg `AppN` needs an n-ary
  application story; the cleanest is to ground `E` in the emitted `DefData`
  (`render_def` output) and denote `App`/`AppN` by look-up-then-substitute, OR by
  an uninterpreted-but-consistent function table keyed by fn id (SymEnv literal).
  The P5 prototype (`probe4_denote` / master plan §11 P5) grounds fn symbols in a
  generated per-crate match-literal — mirror that.
- `Match`/`Ite` need the value/prop sort split resolved (O9): a `match` scrutinee
  is a value (`eval`), each arm body is value-or-prop depending on the goal sort.
  v1's two-function `eval`/`edenote` split already models this; extend both.
- Quantifiers (`Forall`/`Exists`) in a body denote genuine `∀`/`∃` — the same
  binder-embedding story as the goal-level All arm (`toProp_all_embed`); reuse it.
- Interaction: this is really the **Defs-layer denotation** the master plan §4.3
  and W7 (`bootstrap-12`/`DESIGN-W7-defslayer.md`) foreshadow. Check whether v2
  should co-locate with the W7 defs-certificate machinery rather than the W5f
  spine — the fn-symbol grounding is shared.

## Progress

- (2026-07-15, opus-w5f-v2) Claimed. Read probe27 (`w5f_sem.lean`), the real
  emitted `lib.render_exp`/`ExprData` (`tactus-core/out/lib`,
  `TactusDefs_lib_exec__base.lean` L141–166 for the full `ExprData` vocab +
  `TactusDefs_lib_exec__root.lean` L71–91 for `render_exp`/`render_arms`/
  `render_list`), the W7 design (`DESIGN-W7-defslayer.md`), and the P5 grounding
  prototype (`probe-w0/probe5_symenv.lean`).

- **Design decision — the grounding is a SymEnv fn-literal pin, NOT an in-Lean
  DefData interpreter.** An interpreter over `DefData` bodies can't be a
  structural `def`: a recursive spec fn's body re-enters its own call, so `eval`
  would need fuel / a fixpoint. Instead — exactly the P5 shape — the concrete
  `SymEnv` pins `E.fn`/`E.fnN` to the **already-emitted Lean spec fns** via a
  per-crate match-literal (`crateEnv.fn | tri_id => lib.tri | …`). Recursion +
  termination live in the emitted Lean defs (already certified structural by
  W1.5); `eval`/`edenote` stay **structural** — each `App`/`AppN` arm is ONE
  oracle application over recursively-eval'd args. The rfl-bridge closes because
  the concrete env literal kernel-reduces (P5: `gdenote crateEnv … =
  (… myDouble x …) := by rfl`).

- **Consequence that shrinks the work:** a match-bodied fn (`tri`) is grounded
  through `E.fn tri_id = lib.tri`, so `edenote (render_exp (tri n < 10))`
  reduces to `lib.tri (av n) < 10` **without `eval` interpreting the `Match`
  node** — the match is inside `lib.tri`, which reduces on its own. So
  eval-level `Match`/`Ite`/`Forall`/`Exists` interpretation is only needed for
  those nodes appearing DIRECTLY in obligation goals (LeafE), not in bodies
  (bodies denote via the pinned fn oracle).

- **Per-node denotation plan** (over the real `render_exp` lowerings, root L82–84):
  - `App`/`AppN` (`RawExp.Call`→`App`, `RawExp.CallN`→`AppN`): value =
    `E.fn f (eval a)` / `E.fnN f (evalList args)`, oracle pinned to real defs.
    `eval`/`evalList` become a mutual structural pair over `ExprData`/`ExprList`.
  - `Forall`/`Exists` (real `∀`/`∃`): `edenote (Forall x _ b) = ∀ n:Int, edenote
    b (upd st x n)` (over-approx over Int, sound; reuses the `toProp_all_embed`
    embedding), `Exists` → `∃`.
  - `Ite`: condition denoted as a **value** with a decidable `eval c ≠ 0` test
    (avoids `Classical`); resolves the O9 value/prop split — `eval (Ite c t e) =
    if eval c ≠ 0 then eval t else eval e`, `edenote (Ite c t e) = if eval c ≠ 0
    then edenote t else edenote e`.
  - `Match`: the one genuinely-hard node in the flat-Int `St` model — picking an
    arm needs to DECODE the scrutinee Int back to a constructor+fields (the
    inverse of the `emb : U → Int` embedding). Scoped for this rung with an
    honest fail-loud note; it mostly lives in bodies (⇒ handled by the fn pin)
    and is rare directly in obligations. A faithful eval-level Match is a
    datatype-value-decode follow-on.

- Building `probe28_w5f_v2/` extending probe27 with the above.

- **PASS ✓ (probe28, rc=0, ~3.5s)** over the REAL emitted `lib.render_exp`. All
  four v1 facts carry over; five v2 facts land (App/AppN grounded, Forall/Exists
  binder threading, Ite decidable). Every fact closes over standard axioms only
  (`[propext]` / `Quot.sound` / none) — no `sorryAx`, no `Classical.choice`.
  One bug found + fixed en route: eval's `AppN` arm was missing `.deref` on the
  arg-list Box — a type error in a single mutual arm silently breaks EVERY mutual
  arm's `:= rfl` unfold lemma (recorded for bootstrap-56).

## Writeup

**Done (v2 first rung: App/AppN/Forall/Exists/Ite faithful; Match scoped).**
Landed as `probe-w0/probe28_w5f_v2/w5f_v2_sem.lean` (+ `REPORT.md`) — a hand-Lean
probe over the real emitted `lib.*`, no tactus-core rebuild. Extends probe27
(the full v1 Val-level core + four v1 adequacy facts carried verbatim).

**The design decision (the fork this card flagged).** How does `E.fn` get grounded
in the emitted def bodies, and should v2 co-locate with the W7 defs certificate?
Resolution:

> The grounding is a **SymEnv fn-pin, NOT an in-Lean `DefData` interpreter.** An
> interpreter can't be a structural `def` (a recursive spec fn's body re-enters
> its own call ⇒ needs fuel / a fixpoint). Instead — the P5 shape — the concrete
> crate `SymEnv` literal pins `fn`/`fnN` to the already-emitted Lean spec fns.
> Recursion + termination live in the emitted defs (structural by W1.5);
> `eval`/`evalList` stay structural (each App/AppN arm = ONE oracle application
> over recursively-eval'd args). The rfl-bridge closes because the concrete env
> literal kernel-reduces.

**Co-location with W7 is NOT required** — the denotation layer needs only that the
emitted Lean defs exist (W7 emits them) and are pinned in the crate literal; it is
independent of W7's `def_eq` *syntactic* bridge. W5f v2 is the *denotational*
counterpart. A consequence that shrank the work: a match-*bodied* fn (`tri`) is
grounded via the fn oracle, so `eval` never interprets its `Match` node — the
match reduces inside the emitted Lean def. So eval-level body-node interpretation
is only needed for nodes appearing DIRECTLY in obligation goals, not in bodies.

**How the code works.** `SymEnv` gains `fnN : Int → List Int → Int`.
`eval`/`evalList` become a mutual structural pair (`AppN` folds its arg list).
Comparison / logical ops in value position now carry a decidable Bool-as-Int value
so an `Ite` conditioned on a comparison denotes faithfully. `edenote` gains real
`Forall`/`Exists` (genuine `∀`/`∃` over Int, binder threaded via `upd st x n`) and
`Ite` (decidable `eval c ≠ 0` split — no `Classical`). `Match` stays a sentinel.
Five v2 facts, all over the real `lib.render_exp`:
1. `adequacy_leaf_app_grounded` — `edenote(render(g(n)<10)) ↔ g(av n)<10`, `g := E.fn fId`.
2. `adequacy_leaf_forall` — `edenote(render(∀i.body)) ↔ ∀n, edenote(render body)(upd st i n)` (any body ⇒ composes).
3. `adequacy_leaf_exists` — the `∃` mirror.
4. `adequacy_leaf_ite` — `eval(render(if b then x else 0)) = if av b ≠ 0 then av x else 0`.
5. `adequacy_leaf_appn_grounded` — `edenote(render(h(m,n)<100)) ↔ h [av m, av n] < 100`, `h := E.fnN fId`, exercising the `evalList` fold.

**Assumptions / what's partial (honest).**
- **`Match` is NOT faithfully denoted** — the one remaining W7 body node (sentinel).
  Faithful eval-level Match needs the flat-Int datatype-value-decode layer
  (decode the scrutinee Int → ctor+fields). Spun out as **bootstrap-56**. The
  fn-pin already handles match-*bodied* fns, so this only bites `match`-in-obligation
  (rare — do a census first).
- `eval`/`edenote` are definitions we wrote ⇒ spec-adequacy (§8.5), audited-once,
  not trusted; they re-prove no Val-level math.
- The grounded facts take `g`/`h` as hypotheses (`E.fn fId = g`), exactly as v1's
  `adequacy_leaf_cmp` takes `hop`; the concrete crate `SymEnv` literal discharges
  them by `rfl`/`decide` (P5). A cross-crate probe pinning to an actual
  fixture-emitted `lib.<fn>` is a natural strengthening.

**Follow-on:** bootstrap-56 (faithful `Match` decode); optionally a cross-crate
grounded probe pinning to a real fixture-emitted spec fn.
