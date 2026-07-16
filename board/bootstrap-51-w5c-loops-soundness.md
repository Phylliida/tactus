---
title: "W5c — reference-WP soundness, Loop arm (init/maintain/decrease + havoc)"
status: done
claimed_by: opus-w5c-loops
created: 2026-07-14T21:30:00Z
updated: 2026-07-15T02:35:00Z
---

## Description

W5 ladder rung (`DESIGN-W5-soundness.md` §4). Extend `ref_wp_sound` to
`StmData::Loop` — the WP loop rule, **where the structured bugs live**. The
`wp_stm` Loop arm emits init + body + maintain-reclose + decrease goals under the
`loop_maintain_frame` telescope (havoc modified locals via `havoc_lets`,
re-quantify + re-assert invariants/cond, snapshot decreases in a `_tactus_d_old`
let); `frame_after` uses `loop_use_frame` (havoc + ¬cond). The operational
semantics must model the loop as: invariant holds initially (init), is preserved
across an arbitrary iteration from a havoc'd state satisfying inv+cond (maintain),
the decreases measure strictly drops (decrease), and on exit inv+¬cond hold (use).

Partial correctness first; the decrease obligation is modeled but the
well-founded termination argument is its own family (master plan O6).

**Blocked by:** bootstrap-49 (W5a) + benefits from bootstrap-50 (W5b) for the
frame machinery. The hardest structured arm after W5d.

## Progress

- (2026-07-15, opus-w5c-loops) Claimed. Read the emitted `wp_stm` Loop arm +
  `frame_after` Loop arm + `loop_maintain_frame`/`loop_use_frame`/`havoc_lets`/
  `seed_params`/`seed_binders_hyp_bounds`/`binderprops_to_hyps`/`has_let`/
  `binders_to_frame` in `tactus-core/lib.rs` (lines 232, 1881–2317), and the
  landed W5b probe (`probe-w0/probe23_w5b_sem/w5b_sem.lean`). Structure of the
  Loop arm:

  `wp_stm f (Loop L)` = `goals_append init (goals_append body_goals
  (goals_append maintain_reclose decrease_goal))`, i.e. FOUR groups:
    1. **init** = `close_each_e f inv_obligs` — each deep invariant obligation
       closed under the *pre-loop* frame `f` (invariant holds on entry).
    2. **body_goals** = `wp_stm mframe body` where
       `mframe = loop_maintain_frame(f, inv_hyps, binders, binder_bounds,
       cond_name, cond_ann, d_old_name, d_old_val)`.
    3. **maintain_reclose** = `close_each_e endf inv_obligs` where
       `endf = frame_after mframe body` (invariant re-established at body end).
    4. **decrease_goal** = `[close_e endf decrease_oblig]`.
  `frame_after f (Loop L) = loop_use_frame(f, inv_hyps, binders, binder_bounds,
  cond_name, neg_cond_ann)` (continuation frame: havoc + re-quantify + inv +
  ¬cond, no d_old).

- (2026-07-15, opus-w5c-loops) **KEY STRUCTURAL OBSTRUCTION FOUND (the fork).**
  `loop_maintain_frame`/`loop_use_frame` both begin `let hv = havoc_lets(f,
  binders); frame_append(hv, <loop tail>)`. **`havoc_lets` DROPS the FLet
  entries of modified locals from `f`** (lib.rs 1991). So
  `frame_after f (Loop) = frame_append (havoc_lets f binders) useTail` is **NOT**
  of the form `frame_append f Δ` — the Loop is the first constructor whose
  `frame_after` is not a monotone right-append to `f`. This **breaks the W5b
  design lift** `frame_after_eq_append : frame_after f s = frame_append f
  (frameDelta s)` (which every Seq-threading step depends on via
  `closeSem_frame_after`). Consequences worked out:
  - The W5b frame-free `execSafe`/`frameDelta` cannot faithfully represent the
    Loop's continuation: the havoc is a transform of `f` that a frame-free
    `execSafe` (state-only) cannot see.
  - Worse, the havoc's imprecision is *intermediate*: `closeSem f st Q ≠
    closeSem (havoc_lets f binders) st Q` even when `Q` re-quantifies all mod
    vars (the loop tail's `seed_params` ∀-overwrites them), because an
    *intermediate* `FHyp h` in `f` that mentions a mod var is evaluated with the
    mod-var let applied (in `f`) vs not (in `havoc f`) — `hp` is opaque over the
    whole state. This is the reference's OWN documented imprecision
    (`havoc_lets` keeps FHyps; honest-fail on a pre-loop assert over a mod
    local, lib.rs 1981–1989). It means no clean `closeSem f = closeSem (havoc f)`
    bridge, in either direction, without a mod-var-freshness side condition.
  - **Candidate resolutions** (to decide before coding maintain/decrease):
    - **(Opt-1) frame-explicit Loop lemma.** State Loop soundness over `f`
      directly (`holdsAll (wp_stm f (Loop L)) st ↔ init ∧ closeSem mframe … ∧
      closeSem endf …`) as a standalone theorem, NOT folded into the uniform
      `closeSem f st (execSafe s ·)`. Keeps frame-free `execSafe` for the
      non-Loop fragment; `Seq (Loop) rest` (loop-in-sequence, real production
      shape) then needs its own bridge and is scoped/deferred with the havoc
      finding documented.
    - **(Opt-2) frame-carrying `execSafeF f s st`.** Generalise `execSafe` to
      take the incoming frame; the Loop arm havocs it internally.
      `execSafeF f s st` then mirrors `wp_stm f s` structurally
      (Assert→`closeSem f st (he∘render_exp)`, Seq→`execSafeF f a st ∧
      execSafeF (frame_after f a) b st`, Loop→init ∧ body ∧ maintain ∧ decrease
      over mframe/endf). Clean, uniform, handles `Seq(Loop)` for free, and the
      soundness theorem `holdsAll (wp_stm f s) st ↔ execSafeF f s st` reduces to
      the existing bridging lemmas. Cost: `execSafeF` is closer to a paraphrase
      of `wp_stm` (frame accumulation moves inside), so the "operational
      semantics defined independently of the WP" framing (§2.2) weakens — but
      W5b's `execSafe` already mirrors `frame_after` via `frameDelta`, and the
      non-vacuity witnesses (obligation arms require the real `he(render_exp …)`)
      still bite, so the epistemic content is arguably unchanged.
  - Leaning **Opt-2** (tractable + uniform + covers loop-in-sequence), but this
    is exactly the "havoc's interaction with the frame" fork the card flags for
    Danielle. Consulting the local model, then proceeding.

- (2026-07-15, opus-w5c-loops) **Danielle's local model agreed with Opt-2** and
  crystallised WHY the havoc obstruction dissolves under it: `execSafeF` carries
  the frame, so the four Loop goal groups are each `holdsAll (close_each_e
  <frame> obligs)` for an OPAQUE frame — `holdsAll_close_each_e` handles any
  frame, `mframe`/the havoc are never decomposed. On vacuity: "not vacuous — the
  frame TRANSPORT is shared but the PREDICATES transported differ (logical
  necessity vs operational viability)."

- (2026-07-15, opus-w5c-loops) **DONE — probe PASS, first compile.**
  `probe-w0/probe24_w5c_sem/` (`w5c_sem.lean` + `run.sh` + `REPORT.md`)
  elaborates against the REAL emitted `lib.*` — **rc=0, ~2.9s, zero warnings,
  axiom closure `[propext, Quot.sound]`.** Proves `wp_stm_sound` as an **iff**
  (`holdsAll (wp_stm f s) st ↔ execSafeF f s st`) over the WHOLE StmData
  vocabulary incl. Loop, `ref_wp_sound` over the genuine `seed_frame`, + two
  Loop non-vacuity witnesses (init obligation on entry; decrease at body-end).
  Two structural payoffs of the frame-carrying `execSafeF`: (1) it is TOTAL on
  StmData ⇒ the theorem **sheds `inFragment` entirely**; (2) W5b's whole
  `frameDelta`/`frame_after_eq_append`/`closeSem_frame_after`/`frame_append_*`/
  `closeSem_append`/`closeSem_ret_frame`/`retApply`/`diverges`/`is_skip`
  machinery is DROPPED (Seq/If/Ret carry the threaded frame directly). The
  `u_wp_loop`/`u_exec_loop` `rfl` unfolds restate the emitted 11-field Loop arm
  field-for-field — that they type-check as `rfl` is a field-alignment check.
  **Negative control** (manual): weakening the init clause to `True` breaks BOTH
  the iff and witness C ⇒ the probe bites, not vacuous.

## Writeup

**W5c DONE (probe, `probe-w0/probe24_w5c_sem/`).** The reference WP is sound AND
faithful (iff) on the **entire** `StmData` vocabulary — `Skip, Assume, Assign,
Assert, Call, Ret, DeadEnd, If, Seq, Loop` — over an arbitrary frame telescope.
rc=0, ~2.9s, axiom closure `[propext, Quot.sound]`. Full detail in
`probe-w0/probe24_w5c_sem/REPORT.md`.

- **The fork this card flagged (havoc × frame) — resolved.** A Loop's
  continuation/maintain frames are `frame_append (havoc_lets f binders) tail`,
  and `havoc_lets` DROPS modified-locals' pre-loop `let`s from the middle of
  `f`. So `frame_after f (Loop) ≠ frame_append f Δ` — the Loop is the first
  constructor whose `frame_after` is not a monotone right-append, which BREAKS
  the W5b `frameDelta`/`frame_after_eq_append` design lift. And no clean
  `closeSem f ↔ closeSem (havoc f)` bridge exists (an intermediate opaque FHyp
  mentioning a mod var is evaluated with the let applied vs not). **Fix (Opt-2,
  confirmed with Danielle's local model):** the operational-safety predicate
  CARRIES the incoming frame — `execSafeF f s st` — and mirrors `wp_stm f s`'s
  frame threading. The Loop havocs `f` internally through the emitted
  `loop_maintain_frame`; the four goal groups are each `holdsAll (close_each_e
  <opaque frame> obligs)`, handled by the frame-agnostic `holdsAll_close_each_e`
  — so the havoc is never decomposed and the obstruction dissolves.
- **What's proven / verified:** `wp_stm_sound : holdsAll (wp_stm f s) st ↔
  execSafeF f s st` (iff, no `inFragment`, all 10 constructors); `ref_wp_sound`
  over the genuine `lib.seed_frame`; two Loop non-vacuity witnesses. All
  elaborate against the genuine emitted defs (`lib.wp_stm`/`frame_after`/
  `loop_maintain_frame`/`close_e`/`close_each_e`/`ret_frame`/`goals_append`/
  `render_exp`/`seed_frame`).
- **Two payoffs of the reformulation:** (1) `execSafeF` totalises over `StmData`
  ⇒ the theorem sheds the `inFragment` restriction W5a–b carried (soundness now
  over the WHOLE vocabulary, not a fragment); (2) W5b's frame-delta machinery is
  entirely dropped — the proof is a mechanical per-arm rewrite chain, ~40%
  shorter than probe23 despite covering strictly more.
- **Honest scope / caveats:** (1) `execSafeF` is a frame-CARRYING reformulation
  of W5a/b's frame-free `execSafe`; the shared frame threading IS the reference's
  own plumbing (validating it is the point), and non-vacuity lives at the leaf
  obligations (`he (render_exp …)`, never `True` — witnesses + negative control).
  On the non-Loop fragment `execSafeF` should agree with W5b's frame-free reading
  via a small conservative-extension lemma (noted for follow-up; the Loop
  genuinely needs the frame). (2) Val-level, PARTIAL correctness — the decrease
  obligation is MODELED (emitted + must hold at body-end) but the well-founded
  termination argument is its own family (master plan O6); adequacy spine to
  user Props is W5f. (3) Still probe-first: authoring the model in tactus-core
  (loop-closure step) remains deferred (`DESIGN-W5-soundness.md` §4).
- **NEXT = W5d (bootstrap-52): `&mut`/prophecy.** With `execSafeF` totalising
  over StmData, W5d/W5e add value-model arms, not new frame-threading obstacles.
