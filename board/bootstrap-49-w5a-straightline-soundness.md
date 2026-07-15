---
title: "W5a — reference-WP soundness, straight-line fragment (Skip/Assume/Assert/Seq → If + seed ∀-params)"
status: in_progress
claimed_by: opus-w5a-kickoff
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T21:30:00Z
---

## Description

First rung of the W5 soundness ladder (`DESIGN-W5-soundness.md` §4). Prove the
emitted reference `lib.wp_stm`/`lib.ref_wp` **sound** against a written-down
operational semantics, staged:

- **W5a-0** — fragment `{Skip, Assume, Assert, Seq}`, FHyp/FLet frames (no
  `∀`-binders). The core `close_e` / `frame_after` / `goals_append` induction.
  Proven **probe-first** as hand-Lean over the emitted `lib.*` defs
  (`probe-w0/probe21_w5a_sem/`), the analog of probe14 — no tactus-core rebuild.
- **W5a-1** — add `If` (flat two-way, matching `wp_stm`'s If arm) + the seed
  frame's `FBind`/`∀` params + `reqs` as `frameHyps`; lift `ref_wp_sound` to the
  top level over `seed_frame`.

Semantic model, proof skeleton, and the valuation-parametric decision are all in
`DESIGN-W5-soundness.md` §1–3. Oracles: `hp : Int→St→Prop` (opaque leaves),
`he : ExprData→St→Prop` (deep obligations; `render_exp` stays opaque),
`lv : Int→St→Int` (let values). Theorem (W5a-0):
`holdsAll (wp_stm f s) st → frameHyps f st → execSafe s st`.

**Done when:**
- W5a-0 probe elaborates (rc 0) against `tactus-core/out/lib` — the emitted
  `lib.wp_stm`/`lib.frame_after`/`lib.close_e`/`lib.goals_append` are proven
  sound on the fragment, with `render_exp` opaque.
- W5a-1 extends it to `If` + seed ∀-params.
- (later, its own turn) the model is authored as Rust spec/proof fns in
  tactus-core and emitted as a kernel-checked package — the loop-closure step;
  needs R0a-quality lean-only coverage on tactus-core itself.

**Blocked by:** nothing (W2 shapes are frozen and emitted). **Blocks:** the
tactus-core authoring step (loop closure) — but the probe unblocks immediately.

## Progress

- (2026-07-14, opus-w5a-kickoff) Kicked off from the B1 land (bootstrap-48),
  which closed the common-mode gap W5 was blocked on. Decision §5.5 =
  valuation-parametric (option b), recorded in `DESIGN-W5-soundness.md` §1.
  Semantic model (`St`/`hp`/`he`/`holds`/`execSafe`/`addedHyp`) authored and
  peer-reviewed (local model: honest reading, non-vacuous, oracle-independence is
  a feature).
- (2026-07-14, opus-w5a-kickoff, cont.) **W5a-0 PROBE COMPLETE — the reference WP
  is proven SOUND on the straight-line fragment.** `probe-w0/probe21_w5a_sem/`
  (`w5a_sem.lean` + `run.sh` + `REPORT.md`) elaborates against the REAL emitted
  `lib.wp_stm`/`lib.frame_after`/`lib.close_e`/`lib.goals_append`
  (`tactus-core/out/lib`) — no tactus-core rebuild — **rc=0, ~2.6s, zero
  warnings.** Proves `wp_stm_sound` (main) + `ref_wp_sound` (top-level over
  `seed_frame`) + two non-vacuity witnesses (lone-assert, assume-then-assert).
  **Axiom closure = `[propext, Quot.sound]`** — no `Classical.choice` (render_exp
  stays opaque), no `sorryAx`, no smuggled axioms. Four bridging lemmas
  (close/frame_after/frame_append/goals_append) + one induction on `s`. Elaboration
  idioms captured in REPORT (rfl-unfold lemmas since `simp [defName]` can't
  generate equational theorems for the emitted structural defs; sizeOf WF recursion
  through Box; no Mathlib → no `tauto`). **W5a-1 is next** (add If + FBind/∀ seed
  params + real All/Let denotation).

## Writeup

**W5a-0 DONE (probe, hand-Lean over the emitted reference).** The reference WP is
sound on `{Skip, Assume, Assert, Seq}`: every emitted goal true ⟹ every assert's
obligation holds under its accumulated hypothesis context, with the leaf
interpretation (`hp`/`he`) fully opaque (valuation-parametric). Full detail in
`probe-w0/probe21_w5a_sem/REPORT.md`.

- **What's proven / verified:** `wp_stm_sound`, `ref_wp_sound`, + non-vacuity
  examples C/D, all elaborating (rc=0) against the genuine emitted defs; axiom
  closure `[propext, Quot.sound]`.
- **Scope / honest partial:** W5a-0 restricts frames to `FHyp`/`FNil`
  (`isHypFrame`) — closed under the fragment's `frame_after`. `FLet`/`FBind` and
  the `If` arm are W5a-1; the `All`/`Let` `holds` arms carry a documented
  placeholder here (unreached, immaterial to the theorem). Partial correctness
  (no termination arm — that's the Loop rung W5c + its own family).
- **Assumption:** the probe proves the MATH of soundness over the emitted
  reference in Lean; it does NOT yet prove *tactus can author it* as Rust
  spec/proof fns (the loop-closure step, deferred — it forces the whole-crate
  re-verify + olean re-emit). This is the deliberate probe-first split
  (`DESIGN-W5-soundness.md` §4): prove the concept before the expensive
  integration, exactly as W0/probe14 did.
