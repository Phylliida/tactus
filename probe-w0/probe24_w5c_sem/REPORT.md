# probe24 — W5c reference-WP soundness (Loop: init/body/maintain/decrease + havoc)

**Board:** bootstrap-51 (W5c) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~2.9s). Design + model: `DESIGN-W5-soundness.md` §1–4 (W5c row) + board
bootstrap-51 (the havoc fork). Extends probe23 (W5b).

## What it pins

The **fourth (and vocabulary-completing) soundness rung of the W5 loop.** Over
the REAL emitted reference WP (`lib.wp_stm` / `lib.frame_after` /
`lib.loop_maintain_frame` / `lib.close_e` / `lib.close_each_e` / `lib.ret_frame`
/ `lib.goals_append` / `lib.render_exp` / `lib.seed_frame` in
`tactus-core/out/lib`, NO tactus-core rebuild — the analog of probe14 for the
bridge) it proves the reference WP **sound AND faithful** on the **entire**
`StmData` vocabulary — `Skip, Assume, Assign, Assert, Call, Ret, DeadEnd, If,
Seq, Loop` — over an **arbitrary frame telescope**, as an **iff**:

```
wp_stm_sound : holdsAll (wp_stm f s) st ↔ execSafeF f s st
```

Plus `ref_wp_sound`, seeded through the genuine `lib.seed_frame`. Axiom closure
`[propext, Quot.sound]` — no `Classical.choice` (render_exp stays opaque), no
`sorryAx`.

## The design lift: frame-CARRYING `execSafeF` (the havoc fork, board bootstrap-51)

W5a/W5b's operational-safety predicate `execSafe : StmData → St → Prop` was
**frame-free**, and the theorem was `holdsAll (wp_stm f s) st → closeSem f st
(execSafe s ·)` with the frame telescope OUTSIDE `execSafe`. That worked because
every W5b statement's `frame_after f a = frame_append f (frameDelta a)` — a
**monotone right-append** of a per-statement delta (`frame_after_eq_append`,
probe23's load-bearing lift).

**The Loop breaks it.** `frame_after f (Loop) = loop_use_frame f = frame_append
(havoc_lets f binders) useTail`, and `havoc_lets` **DROPS the modified locals'
pre-loop `let`s from the MIDDLE of `f`** (lib.rs 1991). So `frame_after f (Loop)`
is NOT `frame_append f Δ` for any Δ — the Loop is the first constructor whose
`frame_after` is not a right-append. Worse, `closeSem f st Q ≠ closeSem
(havoc_lets f binders) st Q` even when `Q` re-quantifies all mod vars (the loop
tail's `seed_params` ∀-overwrites them), because an *intermediate* `FHyp h` in
`f` mentioning a mod var is evaluated with the let applied (in `f`) vs not (in
`havoc f`) — `hp` is opaque over the whole state. This is the reference's OWN
documented imprecision (`havoc_lets` keeps FHyps; honest-fail on a pre-loop
assert over a mod local, lib.rs 1981–1989). No clean havoc bridge exists.

**Resolution (Opt-2, agreed with Danielle's local model):** the operational
predicate CARRIES the incoming frame — `execSafeF f s st` — and mirrors `wp_stm
f s`'s frame threading structurally (Assert/Call/Ret/Loop-obligations closed
under their frame via `closeSem`; Seq threads `frame_after f a`; If carries
`frame_append f (FHyp c/nc)`; Loop havocs `f` internally via the emitted
`loop_maintain_frame`). **The obstruction dissolves:** the Loop's four goal
groups are each `holdsAll (close_each_e <frame> obligs)` for an OPAQUE frame ∈
{f, mframe, endf}, and `holdsAll_close_each_e` handles ANY frame — so `mframe` /
the havoc are **never decomposed**. The havoc lives entirely inside the emitted
`loop_maintain_frame` / `frame_after`, which `closeSem` interprets faithfully
without needing to relate it back to `f`.

### Two structural payoffs of Opt-2

1. **`execSafeF` is TOTAL on `StmData`** (all 10 constructors) ⇒ the theorem
   **sheds `inFragment` entirely**: soundness now holds over the WHOLE statement
   vocabulary, not a fragment. (W5a–b carried an `inFragment` hypothesis;
   probe24 has none.)
2. **W5b's frame-delta machinery is DROPPED**: `frameDelta`,
   `frame_after_eq_append`, `closeSem_frame_after`, `frame_append_assoc`,
   `frame_append_fnil_right`, `closeSem_append`, `closeSem_ret_frame`,
   `retApply`, `diverges`, `is_skip` are all gone. Seq/If/Ret carry the threaded
   frame directly; the proof is a mechanical rewrite chain per arm. The probe is
   ~40% shorter than probe23 despite covering strictly more.

## The Loop arm structure (mirrored exactly)

`wp_stm f (Loop L)` = `goals_append init (goals_append body (goals_append
maintain_reclose decrease))`, four groups:
1. **init** = `close_each_e f inv_obligs` — each deep invariant obligation on
   ENTRY, under the pre-loop frame `f` (mod-local lets still hold initial values).
2. **body** = `wp_stm mframe body`, `mframe = loop_maintain_frame f inv_hyps
   binders binder_bounds cond_name cond_ann d_old_name d_old_val` (havoc +
   re-quantify mod vars + re-assert each inv + the cond + the `_tactus_d_old`
   decreases snapshot).
3. **maintain_reclose** = `close_each_e endf inv_obligs`, `endf = frame_after
   mframe body` — each invariant re-established at body end.
4. **decrease** = `[close_e endf decrease_oblig]` — the `0 ≤ D ∧ D < d_old`
   obligation at body end.

`execSafeF f (Loop L) st` = the conjunction of the four groups' semantic
readings (`closeSem f (obligsSafe inv_obligs ·)` ∧ `execSafeF mframe body` ∧
`closeSem endf (obligsSafe inv_obligs ·)` ∧ `closeSem endf (he ∘ render_exp
decrease_oblig)`). The `u_wp_loop` / `u_exec_loop` `rfl` unfold lemmas restate
the emitted Loop arm field-for-field — **that they type-check as `rfl` is itself
a correctness check** (any mismatched field / cond_ann-vs-neg_cond_ann /
mframe-vs-usef error would fail the `rfl`).

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | `wp_stm_sound` (iff, arbitrary telescope, ALL 10 constructors incl. Loop) elaborates | ✓ |
| B | `ref_wp_sound` (top-level over the genuine `lib.seed_frame`) elaborates | ✓ |
| C | non-vacuity: a Loop's invariant obligation must hold on ENTRY (at the pre-loop state) | ✓ |
| D | non-vacuity: a Loop's decrease obligation must hold at the body-end state `closeSem endf` | ✓ |
| E | axiom closure = `[propext, Quot.sound]` | ✓ |

**Negative control (run manually, not in `run.sh`):** weakening `execSafeF`'s
Loop init clause from the real `closeSem f (obligsSafe inv_obligs ·)` to `True`
breaks BOTH `wp_stm_sound`'s iff (the emitted init goal can no longer be
discharged into `True`) AND witness C (type mismatch — `True` can't yield the
opaque obligation). Confirms the iff is tight and the witnesses bite.

## How it works (the proof)

Bridging lemmas (all iffs, reused/trimmed from probe22/23): `closeSem_congr` /
`_triv` / `_mono` / `_and` / `_and_iff` (telescope algebra), `holds_close_e`
(Lemma A: a frame-closed obligation ↔ the obligation under the frame's ∀/→/let
telescope), `holdsAll_append` (Lemma D: `goals_append` splits `holdsAll`),
`holdsAll_close_each_e` (a closed obligation LIST ↔ every obligation under the
telescope — the Call/Ret/Loop-init/Loop-maintain core, frame-agnostic).

**Main `wp_stm_sound`** — induction on `s`, each arm a rewrite chain:
- Skip/Assume/Assign: `wp_stm = Nil`, `execSafeF = True`. `simp`.
- Assert: `holds_close_e`.
- Call/Ret: `holdsAll_close_each_e` (Ret at the opaque frame `ret_frame f rb` —
  no `closeSem_ret_frame`/`retApply` needed, the frame is carried).
- DeadEnd: IH at the same frame.
- Seq/If: `holdsAll_append` splits, then IH on each subterm at its threaded
  frame (`frame_after f a` / `frame_append f (FHyp c/nc)`) — carried directly,
  no `closeSem_append`.
- Loop: `holdsAll_append` ×3 splits the four groups; init/maintain via
  `holdsAll_close_each_e` (frames `f` / `endf`), body via IH (frame `mframe`),
  decrease via `holds_close_e` (singleton list, `and_true`). The havoc'd
  `mframe`/`endf` are opaque frames throughout.

## Honest scope / caveats

- **`execSafeF` is a frame-CARRYING reformulation** of the W5a/b frame-free
  `execSafe`. The frame threading it mirrors (Seq→`frame_after`,
  If→`frame_append`, Loop→`loop_maintain_frame`) IS the reference's own frame
  plumbing — validating that plumbing is faithful is the point. The
  **non-vacuous** content is at the leaves: the Assert/Call/Ret/Loop-obligation
  arms require the ACTUAL obligation `he (render_exp …)`, never `True` (witnesses
  C/D + the negative control). Same epistemic status as W5a/b; the frame moved
  inside because the Loop's havoc genuinely lives in the frame and a frame-free
  predicate cannot see it.
- **Relationship to W5b's frame-free `execSafe`** (not proven here, noted for
  W5f/follow-up): on the non-Loop fragment, `execSafeF f s st ↔ closeSem f st
  (fun st' => execSafe s st')` should hold (execSafeF is a conservative
  extension) — worth a small lemma to demonstrate continuity, but the Loop
  genuinely needs the frame so the two cannot be unified at Loop.
- **`inv_obligs` / `decrease_oblig` are arbitrary** deep obligations; soundness
  holds for ANY of them (valuation-parametric). The `decide` bridge (W2) validates
  the serializer's Loop shape against production separately.
- **Val-level, partial correctness** (unchanged): soundness at the `holds` Val
  level; adequacy spine to user-facing `Prop`s is W5f. The **decrease obligation
  is modeled** (`0 ≤ D ∧ D < d_old` closed at body end) but the **well-founded
  termination argument is its own family** (master plan O6) — probe24 proves the
  decrease goal is EMITTED and must hold, not that a decreasing measure implies
  termination.
- **Probe, not yet authored in-crate.** As with probe21/22/23, this proves the
  MATH of soundness over the emitted reference in Lean; authoring the model as
  Rust spec/proof fns in tactus-core (the loop-closure step) is deferred
  (`DESIGN-W5-soundness.md` §4, probe-first split).

## Next (W5d, bootstrap-52)

`&mut` / prophecy — model `final`/resolve by ∀-quantifying the final value. Then
W5e (closures, bootstrap-53), W5f (adequacy spine), and eventually author the
whole model in tactus-core. With the frame-carrying `execSafeF` totalizing over
`StmData`, W5d/W5e add value-model arms, not new frame-threading obstacles.
