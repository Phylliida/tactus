# probe27 — W5f adequacy spine (board bootstrap-54)

**Status:** PASS ✓ (rc=0, ~3.2s, `lean` against the real emitted `lib.*`).
**Axiom closures:** `adequacy_leaf_cmp` `[propext]`, `adequacy_leaf_overflow`
`[propext]`, `toProp_all_embed` *(none)*, `soundness_concrete` `[propext,
Quot.sound]`, carried `wp_stm_sound` `[propext, Quot.sound]`. No `sorryAx`, no
`Classical.choice` — `render_exp`/`edenote`/`eval` all kernel-reduce (structural).

Run: `probe-w0/probe27_w5f_spine/run.sh` (`LEAN=<lean>` to override). Elaborates
`w5f_sem.lean` against `tactus-core/out/lib` — NO tactus-core rebuild.

## What W5f is

W5a–e (probe21–26) proved reference-WP soundness at the **Val level**: the iff
`holdsAll (ref_wp c s) st ↔ execSafeF (seed_frame c) s st`, where the goal
denotation `holds : GoalData → St → Prop` is structural and **parametric over
three opaque leaf oracles** `hp`/`he`/`lv` (valuation-parametric, option b —
`DESIGN-W5-soundness.md` §1). That is already the full drift-detector, but it
states soundness with the leaves opaque.

**W5f is the adequacy spine**: it PINS a concrete interpretation of the oracles
and shows the resulting `holds` denotes the **user-facing `Prop`** — lifting
soundness from the Val level to the theorems users actually read.

## The design decision (the fork the card flagged)

The card asked whether W5f should wait for / co-design with W6's `render_exp`
semantics, or state the spine parametrically. **W6 is now DONE**, so:

> **toProp := `holds` with the oracle triple PINNED to concrete
> interpretations.** The structural arms (Imp/All/Let) then bridge in ONE generic
> induction (definitional — `adequacy_spine` is `Iff.rfl`); ALL genuine content
> concentrates in **(a)** a concrete leaf denotation `edenote` and **(b)**
> per-user-type binder-embedding lemmas at the All arm.

This keeps the state space from exploding (Danielle's stated worry): the spine
induction is generic — proved once — and each user datatype contributes exactly
ONE embedding lemma, not a re-proof of the spine. Cross-checked with the local
model (2026-07-15), which confirmed the structure and flagged the one real trap
(below), addressed by `toProp_all_embed`.

### The SymEnv realization

A subtlety surfaced while grounding the leaf denotation: the emitted
`ExprData.BinOp` **opcode is an interned `u64` id** (the serializer's string
table), NOT a fixed enum — `render_exp` rides it straight through opaquely. So a
*faithful* leaf denotation cannot know "op 2 means `<`" globally; it must ground
the interned ids through a **`SymEnv`** — exactly the per-crate environment
literal of master plan §4.3 / `probe4_denote` P4/P5. `edenote (E : SymEnv)`
replaces W5's **opacity** (`he` a free oracle) with concrete **lookup**
(`E.opk`, `E.av`, …). The SymEnv is a concrete generated literal that
kernel-reduces, so the leaf bridge closes by `rfl`/`simp`. This is the honest
non-circular reading of "pin the oracles": opacity → env-lookup, not a second
layer of opacity.

## The four facts established (all over the REAL emitted defs)

1. **`adequacy_leaf_cmp`** — `edenote E (render_exp (x < 10))` denotes exactly
   `E.av x st < 10`. Exercises `render_exp`'s BinOp arm end-to-end (ref-deref
   balance + nat-coercion decisions — both correctly no-ops here: Int operands,
   Bool result type). `render_exp` reduces by `rfl`; the leaf denotation unfolds
   via the hand `u_edenote_binop`/`u_eval_*` rfl-lemmas + the `E.opk` hypothesis.

2. **`adequacy_leaf_overflow`** — `edenote E (render_exp (HasType 64 e))` denotes
   exactly `0 ≤ E.av e st ∧ E.av e st < 2^64`. Exercises `render_exp`'s G6
   unsigned-overflow **expansion** (`0 ≤ e ∧ e < 2^n`) + `pow2 64`. This is the
   **cast/overflow class** that `DESIGN-W6-stageB` §2 names the highest-value
   silent-unsoundness surface — now checked **denotationally**, not just
   structurally. The single rendered `e` appears in both conjuncts (as production
   reuses it) and denotes the same value both times.

3. **`toProp_all_embed`** — the per-user-type binder embedding at the All arm.
   The emitted `∀ (n : Int)` goal (the Val model quantifies over **all** of Int)
   IMPLIES the user-facing `∀ (u : U)` goal for **any** embedding `emb : U → Int`
   — sound by over-approximation. **The model-flagged trap** (a nested leaf in
   the body reads the bound value from the threaded state) is resolved here:
   instantiating `n := emb u` threads `upd st x (emb u)` into the body, so a
   nested leaf reads the correctly-decoded value. The body `t` is arbitrary, so
   it composes through nesting. Instantiated concretely at `U := Nat`,
   `emb := Int.ofNat` (a genuine non-identity embedding — the unsigned/overflow-
   refined quantifier). Depends on **no axioms**.

4. **`soundness_concrete`** — the carried Val-level `ref_wp_sound` INSTANTIATED
   at the concrete triple (`hp := E.avP`, `he := edenote E`, `lv := E.av`): "the
   emitted goals of `ref_wp c s`, read **concretely** via `edenote` (so
   `holdsAll` is literally the conjunction of the user's rendered obligations),
   hold" ⟺ "operational safety `execSafeF` of the seed-framed program". The
   Val-level drift-detector lifted to concrete user obligations — the W5f payoff.

## Scope / honesty

- **Leaf fragment covered by `edenote`/`eval` v1:** atoms, int/bool literals,
  arithmetic (add/sub/mul), comparisons (lt/le/gt/ge/eq/ne), logical connectives
  (and/or/imp/not), casts (Int↔Nat), unary spec-fn apps (`E.fn`), field
  projections (`E.proj`), goal-side `let`, span-marks (transparent). This is the
  arithmetic/logical obligation fragment — precisely what `probe4_denote` P4
  covered and what the fixture overflow/bounds/assert obligations use. The deeper
  W7 body nodes (`Ite`, `Match`, `AppN`, `Forall`, `Exists`) are stubbed to
  sort-error sentinels — a **v2** rung (they appear in spec-fn *bodies*, a
  `Defs`-layer denotation, not in the stage-A obligation goals this rung targets).
- **`edenote` is a definition we wrote** — it is part of the *statement* of
  soundness, so it lives under spec-adequacy (master plan §8.5), audited-once and
  not trusted. It does not re-prove any Val-level math; it is a thin denotational
  bridge. Its faithfulness to the user Prop is the P4 `rfl`-bridge argument
  (validated here on the two headline leaf classes).
- **The embedding lemma's direction is the sound one** (Val ∀-over-Int → user
  ∀-over-U). That is exactly what soundness needs: the user proves the emitted
  (stronger, all-Int) goal, which delivers their (weaker, typed) theorem.

## Next (W5f v2 / follow-ons)

- Widen `edenote`/`eval` to the W7 body fragment (`Ite`/`Match`/`AppN`/`Forall`/
  `Exists`) with the `Defs`-layer denotation (a spec-fn-body `SymEnv` grounding
  `E.fn` in the emitted `render_def` bodies) — needed once the goal language
  quantifies over user datatypes with real spec-fn leaves.
- Land the spine as generated tactus-core hand-Lean (the `toProp`/`SymEnv`/
  embedding-lemma generator) beside the Stmts layer, so Bridge-R can adopt it
  per goal family (master plan §4.3, W8 authority flip).
