# probe23 — W5b reference-WP soundness (Call + Ret + DeadEnd; live If fall-through)

**Board:** bootstrap-50 (W5b) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~3.5s). Design + model: `DESIGN-W5-soundness.md` §1–4 (W5b row).
Extends probe22 (W5a-1).

## What it pins

The **third soundness rung of the W5 loop.** Over the REAL emitted reference WP
(`lib.wp_stm` / `lib.frame_after` / `lib.close_e` / `lib.close_each_e` /
`lib.ret_frame` / `lib.frame_append` / `lib.goals_append` / `lib.diverges` /
`lib.is_skip` in `tactus-core/out/lib`, NO tactus-core rebuild — the analog of
probe14 for the bridge) it proves the reference WP **sound** on the fragment
`{Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd}` over an
**arbitrary frame telescope**:

```
wp_stm_sound : inFragment s → holdsAll (wp_stm f s) st → closeSem f st (execSafe s ·)
```

Plus `ref_wp_sound`, seeded through the genuine `lib.seed_frame`. Axiom closure
`[propext, Quot.sound]` — no `Classical.choice` (render_exp stays opaque), no
`sorryAx`.

### The three lifts over W5a-1 (probe22)

1. **`Call { reqs, post }`** — `wp_stm f (Call reqs post) = close_each_e f reqs`
   (each requires obligation closed under the frame); `frame_after f (Call) =
   frame_append f post` (the post-call frame appended VERBATIM). The crux: `post`
   may **bind variables** (the ∀-path `FBind(dest) FHyp(ens)`, or the #128 ret-eq
   path `FHyp(E_bound) FLet(dest, E)`), which W5a-1's single-`Prop` `addedHyp`
   could not represent. So the `Seq` continuation is **generalised** from
   `addedHyp a st → body st` to `closeSem (frameDelta a) st body`, folding the
   WHOLE frame delta. `execSafe (Call reqs _) st = obligsSafe reqs st` (the
   requires obligations hold at the call site).

2. **`Ret(es, rb)`** — `wp_stm f (Ret es rb) = close_each_e (ret_frame f rb) es`
   (each ensures obligation closed under the return-binding-extended frame).
   `execSafe (Ret es rb) st = obligsSafe es (retApply rb st)` where
   `retApply RetNone = id`, `retApply (RetLet name val) st = upd st name (lv val
   st)` — on return the ret var is bound, then all ensures obligations must hold.
   `frame_after f (Ret) = f` (control does not continue → `frameDelta = FNil`).

3. **`If` fall-through goes LIVE** — `frameDelta (If c nc t e) = if diverges t =
   1 ∧ is_skip e = 1 then FHyp nc FNil else FNil`. `Ret`/`DeadEnd` now make
   `diverges = 1` **reachable in-fragment**, so `if C { ret } rest` forwards the
   annotated `¬C` leaf (`nc`) into the continuation. W5a-1 could only collapse
   this to `FNil` (via `diverges_zero_of_inFragment`, now RETIRED); here it BITES
   (non-vacuity witness 4).

Also folds in **`Assign`** (`frameDelta = FLet x rhs FNil`, `execSafe = True`) and
**`DeadEnd b`** (`wp_stm f (DeadEnd b) = wp_stm f b`, `frameDelta = FNil` — facts
discarded, `execSafe = execSafe b`).

## The design lift: `frame_after = frame_append ∘ frameDelta`

W5a-1's Lemma B (`closeSem_frame_after`) recursed on the statement and produced
`addedHyp a st' → body st'`. That shape is specific to single-`Prop` deltas.
W5b instead proves the STRUCTURAL identity

```
frame_after_eq_append : inFragment s → frame_after f s = frame_append f (frameDelta s)
```

(induction on `s`; the `Seq` arm needs a new `frame_append_assoc`, the
`Skip`/`Ret`/`DeadEnd`/`If`-else arms need a new `frame_append_fnil_right`).
**Lemma B then collapses to a one-liner**: rewrite by `frame_after_eq_append`,
then apply probe22's `closeSem_append`. This RETIRES probe22's recursive
`closeSem_frame_after`, its `addedHyp` def, and `diverges_zero_of_inFragment`.
The `Seq` continuation `closeSem (frameDelta a) st body` reproduces W5a-1's
`addedHyp a st → body st` exactly when `frameDelta a` is a single `FHyp`
(Assume/Assert), and now also covers Call's binding `post` uniformly.

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | `wp_stm_sound` (main, arbitrary telescope, 9-constructor fragment) elaborates | ✓ |
| B | `ref_wp_sound` (top-level over the genuine `lib.seed_frame`) elaborates | ✓ |
| C | non-vacuity: a `Call`'s requires obligation follows from the emitted goals | ✓ |
| D | non-vacuity: a `Ret (RetLet)`'s ensures holds in the RETURN-BOUND state | ✓ |
| E | non-vacuity: the diverging-then + Skip-else `If`'s `frameDelta = FHyp nc FNil` | ✓ |
| F | non-vacuity: `if C { ret } (assert o)` requires `o` safe only UNDER `hp nc` | ✓ |
| G | axiom closure = `[propext, Quot.sound]` | ✓ |

If any theorem failed to elaborate, `lean` errors and rc≠0.

## How it works (the proof)

New semantic pieces over probe22:
- **`obligsSafe he l st`** — the ∧ over a `RawExpList` of deep obligations
  `he (render_exp ·) st`. The semantic content of a `close_each_e` list.
- **`frameDelta s`** — the frame a statement appends (mirrors `frame_after`).
  `noncomputable` only because `lib.diverges` (in the If arm) is.
- **`retApply lv rb st`** — the state after a return binding (`RetLet` → `upd`).
- **`execSafe`** — extended: `Call → obligsSafe reqs`, `Ret → obligsSafe es
  (retApply rb ·)`, `DeadEnd b → execSafe b`, `Assign → True`, and the `Seq` arm
  now `execSafe a st ∧ closeSem (frameDelta a) st (execSafe b ·)` (the design
  lift). `addedHyp` is gone.

New bridging lemmas:
- **`frame_append_assoc`** / **`frame_append_fnil_right`** — the frame monoid laws
  `frameDelta`'s `Seq`/`FNil` arms need (right identity is NOT definitional —
  `frame_append` recurses on its first arg).
- **`frame_after_eq_append`** — the structural identity above (induction on `s`).
- **`closeSem_frame_after`** — Lemma B, now a 2-line corollary.
- **`closeSem_mono`** / **`closeSem_and_iff`** — telescope monotonicity + the ∧
  distributes-as-iff needed by the `close_each_e` bridge's Cons arm.
- **`holdsAll_close_each_e`** — `holdsAll (close_each_e f l) st ↔ closeSem f st
  (obligsSafe l ·)` (induction on `l`; Cons via Lemma A + `closeSem_and_iff`).
- **`closeSem_ret_frame`** — `closeSem (ret_frame f rb) st body ↔ closeSem f st
  (body ∘ retApply rb ·)` (cases on `rb` + `closeSem_append`).

Reused verbatim from probe22: `closeSem_congr`/`_triv`/`_and`, `holds_close_e`
(Lemma A), `closeSem_append` (Lemma C), `holdsAll_append` (Lemma D).

**Main `wp_stm_sound`** — induction on `s`: `Call`/`Ret` close via
`holdsAll_close_each_e` (+ `closeSem_ret_frame` for Ret's `ret_frame`); `DeadEnd`
via the IH under the same frame; `Seq` splits via Lemma D, rewrites the tail via
the new Lemma B, combines via `closeSem_and`; `If` unchanged from probe22;
Skip/Assume/Assign are `closeSem_triv`.

## Honest scope / caveats

- **`execSafe` mirrors the reference's frame threading by construction.** As in
  W5a (reviewed, `DESIGN-W5-soundness.md` §2.2), safety is defined as "obligations
  hold under the accumulated hypothesis/binder context", NOT assuming the WP's
  correctness. Non-circularity: the `Assert`/`Call`/`Ret` arms require the actual
  obligation (`he (render_exp …)`), not `True`; the four non-vacuity witnesses
  prove the theorem bites. The frame threading (`closeSem (frameDelta a)`) mirrors
  HOW context accumulates; the CONTENT (which obligations) is oracle-independent.
- **Independent guard/hyp leaves** (unchanged): `hp c`/`hp nc` and `hp h`/`he
  (render_exp o)` are the same oracle on independent leaf ids, never constrained
  equal — the conservative (stronger) reading.
- **Call `post` is arbitrary.** Soundness holds for ANY `post` frame (∀-path,
  #128 ret-eq path, or anything else the serializer's `push_post_call_frames`
  emits) — the valuation-parametric spirit. The `decide` bridge (W2b) separately
  validates that the serializer's `post` matches production; W5b assumes nothing
  about `post`'s shape.
- **Val-level, partial correctness** (unchanged): soundness at the `holds` Val
  level; the adequacy spine to user-facing `Prop`s is W5f. No termination arm
  (Loop = W5c). `Loop` is excluded by `inFragment`.
- **Probe, not yet authored in-crate.** As with probe21/22, this proves the MATH
  of soundness over the emitted reference in Lean; authoring the model as Rust
  spec/proof fns in tactus-core (the loop-closure step) is deferred
  (`DESIGN-W5-soundness.md` §4, probe-first split).

## Elaboration idioms (new vs probe22)

- **`execSafe`'s `Seq` arm recurses under `closeSem`'s lambda** (`closeSem
  (frameDelta a) st (fun st' => execSafe … b st')`) and `termination_by
  structural s` **accepts it** — the reader parameter `st` varies to `st'` under
  the binder, exactly as `closeSem`'s own FBind arm does. The structural
  recursion sees `b.deref` as a subterm regardless of the state argument.
- **`frameDelta` must be `noncomputable`** (it calls `lib.diverges`, which the
  emitted code marks noncomputable); this does not affect `rfl`-unfolding or
  `simp only [u_fd_*]`.
- **`frame_append f FNil = f` is NOT `rfl`** (`frame_append` recurses on the
  first arg) — `frame_append_fnil_right` by induction. The left identity
  `u_fapp_FNil` IS `rfl`.
- **The live If fall-through's `if` is reduced by `if_pos`** fed a `⟨rfl, rfl⟩`
  proof of `diverges (Ret …) = 1 ∧ is_skip Skip = 1` (both `nat` sides reduce),
  in both `frame_after_eq_append`'s If arm (`by_cases` + `if_pos`/`if_neg`) and
  witness F.
- **Deferred `inFragment` proofs** — passing `_` for the statement arg and the
  proof as `(by exact trivial)` / `(by refine ⟨⟨?_,?_⟩,?_⟩ <;> exact trivial)`
  lets the statement metavar solve from `hg` before the tactic runs.

## Next (W5c, bootstrap-51)

`Loop` + havoc (`loop_maintain_frame`/`loop_use_frame`, init/maintain/decrease
obligations); the WP loop rule. Then W5d (&mut/prophecy), W5e (closures), W5f
(adequacy spine), and eventually author the whole model in tactus-core.
