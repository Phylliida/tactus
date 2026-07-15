---
title: "W5a — reference-WP soundness, straight-line fragment (Skip/Assume/Assert/Seq → If + seed ∀-params)"
status: done
claimed_by: opus-w5a1-if-params
created: 2026-07-14T21:30:00Z
updated: 2026-07-14T22:45:00Z
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
- (2026-07-14, opus-w5a1-if-params) **W5a-1 PROBE COMPLETE — TASK DONE.**
  `probe-w0/probe22_w5a1_sem/` (`w5a1_sem.lean` + `run.sh` + `REPORT.md`)
  elaborates against the REAL emitted `lib.wp_stm`/`lib.frame_after`/
  `lib.frame_append`/`lib.close_e`/`lib.goals_append`/`lib.diverges`/
  `lib.is_skip`/`lib.seed_frame` — no tactus-core rebuild — **rc=0, ~3.1s.**
  Three lifts over W5a-0: (1) **`If`** (flat two-way, `wp_stm`'s If arm;
  `execSafe (If c nc t e) = (hp c → execSafe t) ∧ (hp nc → execSafe e)`);
  (2) **FBind/∀ seed params + FLet lets** via a GENERAL frame telescope
  `closeSem` (FBind→∀, FHyp→→, FLet→let) that REPLACES W5a-0's
  `isHypFrame f → frameHyps f st → execSafe s st` with the restriction-free
  `closeSem f st (execSafe s ·)` — **the isHypFrame guard is gone**;
  (3) **real All/Let denotation** for `holds` (were placeholders, now reached &
  faithful). Proves `wp_stm_sound` (arbitrary telescope) + `ref_wp_sound` over
  the genuine all-FBind `lib.seed_frame` + two non-vacuity witnesses (if-branch
  obligation under `hp c`; ∀-param seed obligation for all valuations).
  **Axiom closure `[propext, Quot.sound]`** — no `Classical.choice`, no
  `sorryAx`. New lemmas: `closeSem_congr`/`_triv`/`_and` (telescope algebra) +
  Lemmas A/B/C/D generalised to the full telescope + `diverges_zero_of_inFragment`
  (kills the If fall-through in-fragment). Honest caveat: the `frame_after` If
  fall-through `¬cond`-forwarding is out-of-fragment (needs Ret/DeadEnd) → W5b.
  Detail in `probe-w0/probe22_w5a1_sem/REPORT.md`. **NEXT = W5b (bootstrap-50):
  Call + Ret/ret_frame; the If fall-through goes live there.**

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

---

**W5a-1 DONE (probe, `probe-w0/probe22_w5a1_sem/`).** The reference WP is sound on
the BRANCHING fragment `{Skip, Assume, Assert, Seq, If}` over an **arbitrary frame
telescope** — the `isHypFrame` restriction is lifted. rc=0, ~3.1s, axiom closure
`[propext, Quot.sound]`. Full detail in `probe-w0/probe22_w5a1_sem/REPORT.md`.

- **What's proven / verified:** `wp_stm_sound : inFragment s → holdsAll (wp_stm
  f s) st → closeSem f st (execSafe s ·)` (main, no frame restriction);
  `ref_wp_sound` over the genuine all-`FBind` `lib.seed_frame`; two non-vacuity
  witnesses (if-branch obligation delivered under `hp c`; ∀-param seed obligation
  for all valuations). All elaborate against the genuine emitted defs
  (`lib.wp_stm`/`frame_after`/`frame_append`/`close_e`/`goals_append`/`diverges`/
  `is_skip`/`seed_frame`).
- **The design lift:** W5a-0's `frameHyps f st → execSafe s st` (hyp-frames only)
  becomes `closeSem f st (execSafe s ·)`, a general frame-telescope
  interpretation folding `FBind → ∀ (upd)`, `FHyp → →`, `FLet → let (upd ∘ lv)`.
  The three telescope lemmas (`closeSem_congr`/`_triv`/`_and`) + the generalised
  bridging Lemmas A/B/C/D carry the DESIGN §3 skeleton to the full telescope. A
  third oracle `lv : Int→St→Int` (let values) joins `hp`/`he`.
- **Honest partial / caveats:** the `frame_after` **If fall-through**
  (`¬cond`-forwarding when the then-branch diverges & else is Skip) is
  out-of-fragment — divergence needs `Ret`/`DeadEnd`, so
  `diverges_zero_of_inFragment` collapses it to `frame_after f (If) = f`
  in-fragment (faithful, not a shortcut); it goes live at **W5b**. Guard leaves
  `hp c`/`hp nc` are independent (conservative reading). Still Val-level, partial
  correctness (adequacy spine = W5f; Loop = W5c). Still probe-first: authoring the
  model in tactus-core (loop closure) remains deferred.
- **`ref_wp_sound` now needs no `isHypFrame` hypothesis** — the genuine
  `lib.seed_frame` (all `FBind`) is handled directly by `closeSem`'s ∀ arm. This
  was the concrete blocker W5a-1 set out to remove; it is removed.
