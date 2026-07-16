---
title: "W5f — adequacy spine: Val-level `holds` → user-facing `Prop`s"
status: done
claimed_by: opus-w5f-spine
created: 2026-07-15T05:10:00Z
updated: 2026-07-15T06:40:00Z
---

## Description

Final W5 ladder rung (`DESIGN-W5-soundness.md` §4, W5f row; §2.1 note). Spun out
of bootstrap-53 now that W5a–e have all landed (probe21–26).

The hand-Lean **adequacy spine**: `TGoal.toProp` + a structural induction
relating the **Val-level** `holds` denotation (`DESIGN-W5-soundness.md` §2.1 —
the `holds : GoalData → St → Prop` used by probe21–26) to the **user-facing
`Prop`s** that appear in the theorems users actually prove, with generated
per-datatype embedding lemmas.

W5 v1 (probe21–26) states soundness at the **Val level only** — that is already
the full drift-detector (`ref_wp c s` faithfully computes the obligation
telescope, and if those goals hold the operational safety predicate holds). W5f
lifts this from the Val level to the user's `Prop`s, so that "the emitted goals
hold" ⟹ "the user's stated theorem holds".

Small, **audited-once, not trusted** — it is the *statement* of soundness, so
spec-adequacy covers it (master plan §8.5). It does NOT re-prove any Val-level
math; it is a thin denotational bridge.

**Blocked by:** none remaining — W5a–e all done (bootstrap-49..53).

## Design notes (starting points)

- The Val-level `holds` (probe26 `w5e_sem.lean`) is structural on `GoalData`:
  Leaf→`hp id st`, LeafE→`he e st`, Imp→`hp h st → holds t`, All→`∀ n, holds t
  (upd st x n)`, Let→`holds t (upd st x (lv v st))`. The three oracles
  (`hp`/`he`/`lv`) are the seam: the adequacy spine must relate a *concrete*
  interpretation of these oracles (from the real Val universe) to the user `Prop`.
- Likely shape: a `TGoal.toProp : GoalData → Prop` that reads the deep expression
  content (W6's `render_exp` deepening gives `he` a concrete meaning) and a
  theorem `holds hp he lv g st ↔ TGoal.toProp g` for the concrete oracle triple,
  by induction on `g`. Per-datatype embedding lemmas handle the leaf universe.
- Interaction with W6 (stage-B deep expressions): W5 is valuation-parametric
  (`DESIGN-W5-soundness.md` §1, option b) precisely so the oracle interpretation
  is deferred; W5f is where a concrete interpretation gets pinned. Check whether
  W5f should wait for / co-design with W6's `render_exp` semantics, or state the
  spine parametrically and specialise later.

## Progress

- (2026-07-15, opus-w5f-spine) Claimed. Read W5a–e (probe21–26), the master plan
  §4.3/§8.5 (adequacy spine + spec adequacy), `probe4_denote` (the `gdenote`/toProp
  prototype), and the emitted `lib.render_exp`/`ExprData`/`GoalData` (tactus-core
  `lib.rs`). **Key finding: W6 is DONE** (`bootstrap-11`), so the fork ("wait for /
  co-design with W6, or state parametrically") resolves toward co-design.
- Consulted Danielle's local model on the proof structure. It confirmed
  **pin-the-oracles + factor into (generic spine · leaf-denote · per-type
  embedding)** and flagged the one real trap: the per-type binder-embedding lemma
  must bridge the **quantifier → state → leaf** pipeline (a nested leaf reads the
  bound value from the threaded state), not just the quantifier.
- **The SymEnv realization** (while grounding the leaf denotation): the emitted
  `ExprData.BinOp` opcode is an interned `u64` id (not a fixed enum) — `render_exp`
  rides it through opaquely. So a faithful `edenote` must ground ids through a
  `SymEnv` (the P4/P5 shape), turning W5's oracle **opacity** into concrete
  **lookup**. Recorded in `DESIGN-W5-soundness.md` §2.1.1.
- **Authored probe27** (`probe-w0/probe27_w5f_spine/`), carrying the proven W5e
  Val-level core + the W5f layer. **PASS ✓ (rc=0, ~3.2s)**, over the REAL emitted
  `lib.*`, axiom closures `[propext]` / none / `[propext, Quot.sound]` — no
  `sorryAx`, no `Classical.choice`.
- Recorded the decision + status in `DESIGN-W5-soundness.md` (§2.1.1 + §5 status).

## Writeup

**Done (v1 first rung).** W5f is the adequacy spine that lifts the Val-level goal
denotation `holds` (proven sound at the Val level by W5a–e) up to the user-facing
`Prop`s. Landed as `probe-w0/probe27_w5f_spine/w5f_sem.lean` (see its `REPORT.md`
for the full detail) — a hand-Lean probe over the real emitted defs, no tactus-core
rebuild.

**The design decision (the fork this card flagged).** W6 (`render_exp`) is done, so
the spine co-designs with it. Resolution:

> `toProp := holds` **with the oracle triple PINNED** to concrete interpretations.
> The structural arms (Imp/All/Let) bridge in ONE generic induction (`adequacy_spine`
> is `Iff.rfl`); ALL genuine content concentrates in **(a)** a concrete leaf
> denotation `edenote` and **(b)** per-user-type binder-embedding lemmas at the All
> arm.

This is the answer to "how to structure the proof without letting the state space
explode": the spine induction is generic (proved once), and each user datatype
contributes exactly ONE embedding lemma, not a re-proof.

**How the code works.** `edenote (E : SymEnv) : ExprData → St → Prop` (+ a value-
level `eval`) is the concrete leaf denotation; `SymEnv` grounds the interned ids
(`E.opk` opcode → operator kind, `E.av`/`E.avP` atoms, `E.fn` apps, `E.proj`
fields). The concrete oracle triple pins `he := edenote E`, `hp := E.avP`,
`lv := E.av`; `toProp E g st := holds (hpOf E) (heOf E) (lvOf E) g st`. Four facts,
all over the real emitted `lib.render_exp`:
1. `adequacy_leaf_cmp` — `render_exp` of `x < 10` denotes `E.av x st < 10`.
2. `adequacy_leaf_overflow` — `render_exp` of `HasType 64 e` denotes
   `0 ≤ e ∧ e < 2^64` (the cast/overflow silent-unsoundness class, DENOTATIONALLY).
3. `toProp_all_embed` — the emitted `∀(n:Int)` goal implies the user `∀(u:U)` goal
   for any `emb : U → Int`, through `upd st x (emb u)` (the model-flagged trap;
   instantiated at `U:=Nat`).
4. `soundness_concrete` — carried `ref_wp_sound` at the concrete triple: emitted
   goals read concretely via `edenote` hold ⟺ operational safety.

**Assumptions / what's partial (honest).**
- `edenote`/`eval` cover the **arithmetic/logical obligation fragment** (atoms,
  int/bool literals, arith, comparisons, logical connectives, Int↔Nat casts, unary
  apps, field projections, goal-side let, span-marks) — exactly what `probe4` P4 +
  the fixture obligations use. The **W7 body nodes** (`Ite`/`Match`/`AppN`/`Forall`/
  `Exists`) are stubbed to sort-error sentinels → a **v2 rung**: they live in
  spec-fn *bodies* (a `Defs`-layer denotation grounding `E.fn` in `render_def`
  bodies), not in the stage-A obligation goals this rung targets.
- `edenote` is a *definition we wrote* → spec-adequacy (master plan §8.5),
  audited-once, not trusted. It re-proves no Val-level math; its faithfulness to
  the user Prop is the P4 `rfl`-bridge, validated here on the two headline classes.
- The embedding lemma's direction is the **sound** one (Val ∀-over-Int → user
  ∀-over-U): the user proves the emitted (stronger, all-Int) goal, delivering their
  (weaker, typed) theorem.
- The `soundness_concrete` iff is a direct instantiation of the carried W5e
  `ref_wp_sound`; the leaf-bridge facts are what make its LHS read as concrete user
  obligations. It is NOT a new soundness proof — it is the lift of the existing one.

**Follow-on tasks worth spinning out:** (i) W5f v2 — widen `edenote`/`eval` to the
W7 body fragment with a Defs-layer `SymEnv`; (ii) land the spine as generated
tactus-core hand-Lean (`toProp`/`SymEnv`/embedding-lemma generator) beside Stmts so
Bridge-R can adopt it per goal family (feeds the W8 authority flip, bootstrap-13).
