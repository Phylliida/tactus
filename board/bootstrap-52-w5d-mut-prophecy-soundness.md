---
title: "W5d — reference-WP soundness, &mut / prophecy (∀-final-value model)"
status: done
claimed_by: opus-w5d-prophecy
created: 2026-07-14T21:30:00Z
updated: 2026-07-15T03:30:00Z
---

## Description

W5 ladder rung (`DESIGN-W5-soundness.md` §4). Model `&mut` / prophecy semantics
(`final`/resolve) in the operational semantics and prove the corresponding
`wp_stm` arms sound. Standard trick: model prophecy by **∀-quantifying the final
value** (master plan O5) — pick ∀-final-value vs two-state framing by whichever
makes the proof go through; document the choice as part of spec adequacy (§8.5).

Hardest modeling in the ladder; do last (before closures).

**Blocked by:** bootstrap-49/50/51 (the frame + call + loop machinery).

## Progress

- (2026-07-15, opus-w5d-prophecy) Claimed. Read the W5c core (probe24
  `execSafeF`/`wp_stm_sound`, an **iff TOTAL over all 10 StmData constructors
  over an arbitrary frame telescope**), `DESIGN-W5-soundness.md` §4/§1,
  `DESIGN-W2-refwp` §2.6, and the bootstrap `StmData` mirror. **Key early
  finding:** the bootstrap mirror has NO dedicated `&mut`/prophecy constructor —
  §2.6 routes it through the same `post: FrameList`/statement machinery as
  `Call`. So prophecy is a frame/statement-level model, and W5c's arbitrary-frame
  iff already covers the shape.

- (2026-07-15, opus-w5d-prophecy) **Consulted Danielle's local model** on whether
  a pure-frame ∀-final model MISSES a prophecy soundness subtlety. It flagged a
  genuine worry: modeling `resolve` as an `FHyp` could shift the pin to the WRONG
  end of the borrow ("if the final value is already correct at the *start*, safe"
  — trivial). Its premise ("resolve is a post-condition obligation") turned out
  **wrong for Verus**, but the structural instinct (placement matters, thread it
  as a statement) was right and sharpened the design.

- (2026-07-15, opus-w5d-prophecy) **Verified the model against the ACTUAL Verus
  source** (not first principles): `&mut x` → a fresh ∀-quantified final `x_fut`;
  `resolve` = `Assume(has_resolved(place))` — a HYPOTHESIS placed as a STATEMENT
  (`vir/src/ast.rs:1087`, `vir/src/resolution_inference.rs:77`), NOT an
  obligation. Confirmed the emitted `frame_after (Assume e) = frame_append f
  (FHyp e FNil)` and `frame_append`'s tail-append in
  `tactus-core/out/lib` — the load-bearing fact that `resolve` pins into the
  CONTINUATION, not the pre-body frame.

- (2026-07-15, opus-w5d-prophecy) **DONE — probe25 PASS, rc=0, zero warnings,
  ~3.0s.** `probe-w0/probe25_w5d_sem/` (`w5d_sem.lean` + `run.sh` + `REPORT.md`),
  built on probe24's proven core. Adds `prophecy_sound` (WP for `resolve; assert
  P(*x)` ↔ `∀ x_fut, resolve(x_fut) → P(x_fut)` — the ∀-final model + resolve pin
  made explicit), `prophecy_swapped_sound` (`assert P; resolve` ↔ UNGATED
  `∀ x_fut, P(x_fut)`), a ∀-final non-vacuity witness, and a temporal-placement
  witness (the two reduced forms DIFFER ⇒ the pin is placed correctly). Axiom
  closure `[propext, Quot.sound]` on all four theorems. **Negative control**
  (manual): dropping the resolve gate from `prophecy_sound`'s RHS fails
  elaboration (`unsolved goals` + `sorryAx` enters closure) ⇒ the iff bites.
  Design doc updated: §5 status + §1.1 O5 resolution (∀-final-value, as spec
  adequacy).

## Writeup

**W5d DONE (probe, `probe-w0/probe25_w5d_sem/`).** The `&mut`/prophecy
**∀-final-value model** (master plan O5) is faithfully realized by the reference
WP's frame telescope + `Assume`-resolve, with **no new `StmData` arm**. rc=0,
~3.0s, zero warnings, axiom closure `[propext, Quot.sound]` on all four theorems.
Full detail in `probe-w0/probe25_w5d_sem/REPORT.md`; O5 spec-adequacy resolution
in `DESIGN-W5-soundness.md` §1.1.

- **O5 RESOLVED = ∀-final-value** (not two-state). Grounded in the ACTUAL Verus
  encoding, read off `verus/source/vir` (not reasoned from first principles):
  `&mut x` introduces a fresh prophesied final `x_fut`, ∀-quantified (the
  standard trick); `resolve` is `Assume(has_resolved(place))` — a HYPOTHESIS
  placed as a STATEMENT at the resolution point (`ast.rs:1087`,
  `resolution_inference.rs:77`), NOT an obligation. `old(*x)` and `x_fut` are
  distinct ids in one state `St := Int → Int` (a projection of the two-state
  model), which suffices.
- **Why W5c already subsumes it:** `closeSem`'s `FBind` arm IS the ∀-final
  quantification; the emitted `frame_after (Assume e) = frame_append f (FHyp e)`
  threads the resolve pin `FHyp(x == x_fut)` into the CONTINUATION. So the W5c
  `execSafeF` iff (total over StmData, arbitrary telescope) instantiates directly
  to the prophecy shape. `DESIGN-W2-refwp` §2.6 already anticipated this (`&mut`
  post-state through the `Call`-style `post: FrameList`).
- **Main result `prophecy_sound`:** the reference WP for the canonical caller
  shape `resolve; assert P(*x)` reduces EXACTLY to `∀ x_fut, resolve(x_fut) →
  P(x_fut)` — the obligation must hold for EVERY prophesied final value, UNDER
  the resolve pin.
- **Temporal-placement subtlety, discharged** (the local model's worry):
  `prophecy_swapped_sound` shows `assert P; resolve` reduces to the UNGATED
  `∀ x_fut, P(x_fut)`. The two forms DIFFER — which is impossible if resolve were
  a pre-body `FHyp` — proving `frame_after (Assume _)` places the pin
  temporally-correctly (downstream obligations see it, upstream ones do not).
- **Honest scope / caveats:** (1) **No new proof engine** — the prophecy theorems
  are instantiations of the W5c iff at a concrete program + frame; the point of
  W5c totalizing over arbitrary frames is that the ∀-final model is subsumed. The
  non-vacuous deltas: the ∀-final reading is made explicit and matched to the
  emitted WP (negative control), and the resolve pin's placement is verified vs
  the emitted `frame_after (Assume _)` and the actual Verus encoding. (2) Model
  faithfulness rests on the Verus source read (resolve = assume, `&mut` final =
  ∀-binder); if a future Verus made resolve an obligation, the pin becomes an
  `Assert` — the machinery already supports that. (3) **Caller-side shape only**
  (where the ∀-final trick bites); the callee side is the ordinary `Ret` ensures,
  already covered by W5b/W5c. (4) Val-level, partial correctness (unchanged);
  adequacy spine to user `Prop`s is W5f. (5) Probe-first — authoring the model in
  tactus-core is deferred (`DESIGN-W5-soundness.md` §4); when the bootstrap mirror
  grows a `&mut` serializer path, the W2 `decide` bridge validates its
  prophecy-frame shape against production and this probe is the soundness half.
- **NEXT = W5e (bootstrap-53): closures.** Then W5f (adequacy spine). With
  `execSafeF` total over StmData and prophecy shown to be a frame/statement-level
  model, W5e should likewise add a value-model reading, not new frame obstacles.
