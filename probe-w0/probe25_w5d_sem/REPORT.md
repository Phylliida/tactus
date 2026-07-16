# probe25 — W5d reference-WP soundness (`&mut` / prophecy: the ∀-final-value model)

**Board:** bootstrap-52 (W5d) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~3.0s, zero warnings). Design + model: `DESIGN-W5-soundness.md` §4 (W5d
row) + §1 (O5, prophecy model as spec adequacy) + board bootstrap-52. Extends
probe24 (W5c).

## What it pins

The **fifth soundness rung of the W5 loop — `&mut` / prophecy.** Over the REAL
emitted reference WP (`lib.wp_stm` / `lib.frame_after` / `lib.frame_append` /
`lib.close_e` / `lib.render_exp` / `lib.seed_frame` in `tactus-core/out/lib`, NO
tactus-core rebuild) it proves that the **∀-final-value prophecy model** (master
plan O5) is faithfully realized by the frame telescope + `Assume`-resolve — with
no new `StmData` constructor.

```
prophecy_sound :
  holdsAll (wp_stm (FBind x_fut ty FNil) (Assume resolve; Assert P)) st
    ↔ (∀ x_fut, resolve(x_fut) → P(x_fut))
```

i.e. the reference WP for the canonical caller shape `resolve; assert P(*x)`
reduces **exactly** to "for **every** prophesied final value, **if** resolve
holds **then** the obligation holds" — the ∀-final-value model + resolve pin,
made explicit and machine-checked. Axiom closure `[propext, Quot.sound]` on all
four theorems — no `Classical.choice` (render_exp stays opaque), no `sorryAx`.

## The key realization: W5d is a frame/statement-level model, not a new arm

W5c's `execSafeF` / `wp_stm_sound` is already an **iff, TOTAL over the whole
`StmData` vocabulary, over an arbitrary frame telescope**. Prophecy adds nothing
structural to that — per `DESIGN-W2-refwp` §2.6, `&mut` post-state flows through
the same `post: FrameList` / statement machinery as `Call`. W5d's honest content
is therefore: (1) pin the **concrete** prophecy shape, (2) show the general
theorem instantiates to the ∀-final-value reading, (3) discharge the
**temporal-placement** subtlety, (4) confirm the model against the **actual
Verus encoding** (not first principles).

## How Verus actually encodes prophecy (verified from source)

Not reasoned from first principles — read off `verus/source/vir`:

- **`&mut x` → a fresh prophesied FINAL value `x_fut`, ∀-quantified** (the
  "standard trick", master plan O5). In the frame telescope this is an
  `FBind x_fut ty` (introduced at borrow creation / carried by a `Call`
  post-frame). `closeSem`'s `FBind` arm **is** that ∀-quantification
  (`∀ n, closeSem tail (upd st x_fut n) body`).
- **`resolve` is `Assume(has_resolved(place))`** — a **hypothesis** placed as a
  **statement** at the resolution point, **NOT an obligation to prove**
  (`vir/src/ast.rs:1087` "`assume(has_resolved(place))`";
  `vir/src/resolution_inference.rs:77` "insert `Assume(HasResolved(p))`"). So
  `resolve` is a `StmData.Assume`, and the emitted
  `frame_after f (Assume e) = frame_append f (FHyp e FNil)` threads the pin
  `FHyp(x == x_fut)` into the **continuation** — downstream of the mutations,
  never the pre-body frame.

## The temporal-placement subtlety (flagged by Danielle's local model, discharged)

The local model raised a genuine worry: if `resolve` is modeled as an `FHyp` in
the frame, does that shift the pin to the **wrong end** of the borrow ("if the
final value is already correct at the *start*, the program is safe" — trivial /
wrong)? Its premise ("resolve is a post-condition obligation") turned out to be
**incorrect for Verus** (resolve is an `assume`, per the source above), but its
structural instinct was right and sharpened the design: **the resolve pin's
placement is temporally meaningful, and must be threaded as a *statement*, not
hand-placed in a pre-frame.** The probe discharges this concretely:

```
prophecy_swapped_sound :        -- `assert P(*x); resolve` (resolve AFTER)
  holdsAll (wp_stm (FBind x_fut ty FNil) (Assert P; Assume resolve)) st
    ↔ (∀ x_fut, P(x_fut))       -- UNGATED — the pin never reaches the assert
```

`resolve; assert` gates the obligation with `resolve`; the swapped
`assert; resolve` demands the **ungated** obligation. The two reduced forms
**differ** — which they could not, if the reference put resolve as a pre-body
`FHyp`. So `frame_after (Assume _)` places the pin temporally-correctly:
downstream obligations see it, upstream ones do not.

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | full W5c core carries over (`wp_stm_sound` iff, TOTAL over StmData, arbitrary telescope) | ✓ |
| B | `ref_wp_sound` (top-level over the genuine `lib.seed_frame`) | ✓ |
| C | `prophecy_sound`: reference WP for `resolve; assert P` ↔ `∀ x_fut, resolve → P` | ✓ |
| D | `prophecy_swapped_sound`: `assert P; resolve` ↔ ungated `∀ x_fut, P` (placement bites) | ✓ |
| E | non-vacuity (∀-final): obligation must hold for EVERY prophesied final value | ✓ |
| F | temporal-placement witness: the two reduced forms are genuinely distinct | ✓ |
| G | axiom closure = `[propext, Quot.sound]` on all four theorems | ✓ |

**Negative control (run manually, not in `run.sh`):** dropping the `resolve →`
gate from `prophecy_sound`'s RHS (making it the ungated form) **fails to
elaborate** (`unsolved goals` at the `simp only`, plus type mismatches in the
dependent witnesses, and `sorryAx` enters the closure). Confirms the iff is
tight — the reference genuinely threads the resolve pin into the continuation
obligation; it is not a vacuous artifact.

## The reduction (how `prophecy_sound` goes through)

`prophecy_sound` is a one-shot instantiation of the W5c iff:

1. `rw [wp_stm_sound …]` — replace `holdsAll (wp_stm …)` with `execSafeF …`.
2. `simp only [...]` unfolds `execSafeF` on the concrete `Seq (Assume) (Assert)`:
   - `u_exec_seq` → `execSafeF pfr (Assume resolve) ∧ execSafeF (frame_after pfr
     (Assume resolve)) (Assert obl h)`; the first conjunct is `True`
     (`u_exec_assume`, `true_and`).
   - `u_fa_assume` + `u_fapp_fbind` + `u_fapp_fnil` compute
     `frame_after (FBind x_fut ty FNil) (Assume resolve) =
      FBind x_fut ty (FHyp resolve FNil)` — the pin lands **after** the binder.
   - `u_exec_assert` → `closeSem (FBind x_fut ty (FHyp resolve FNil)) st
     (he (render_exp obl) ·)`; `u_cs_FBind`/`u_cs_FHyp`/`u_cs_FNil` telescope it
     to `∀ n, hp resolve (upd st x_fut n) → he (render_exp obl) (upd st x_fut n)`.

The new unfold lemmas (`u_fapp_fnil`/`u_fapp_fbind`/`u_fa_assume`/`u_fa_assert`,
all `rfl`) restate the emitted `frame_append`/`frame_after` arms field-for-field
— that they type-check as `rfl` is itself a check on the emitted reference.

## Honest scope / caveats

- **No new proof engine.** W5d rides the W5c `execSafeF` iff verbatim; the
  prophecy theorems are instantiations at a concrete program + frame. That is
  the *point* of W5c totalizing over arbitrary frames — the ∀-final-value model
  is subsumed by the frame telescope. The **non-vacuous** deltas are: (i) the
  ∀-final reading is made explicit and shown to match the emitted WP
  (`prophecy_sound`, negative control), and (ii) the resolve pin's temporal
  placement is verified against the emitted `frame_after (Assume _)` and the
  actual Verus encoding (`prophecy_swapped_sound`, source citations).
- **Model faithfulness rests on the Verus source read** (`ast.rs:1087`,
  `resolution_inference.rs:77`): resolve = `assume`, `&mut` final = ∀-binder. If
  a future Verus revision changed resolve to an *obligation*, the model would
  need the pin as an `Assert` obligation instead of an `Assume` hyp — the
  frame/statement machinery already supports both (Assert emits a goal), so the
  change would be localized.
- **Caller-side shape only.** The probe models the **caller** of a `&mut`-taking
  fn (∀-final + assumed ensures + resolve pin), the site where the ∀-final trick
  bites. The **callee** side (a fn body with a `&mut` param proving its ensures
  about the actual final `*x`) is just the ordinary `Ret` ensures obligation,
  already covered by W5b/W5c — no prophecy-specific content.
- **Val-level, partial correctness** (unchanged from W5c): soundness at the
  `holds` Val level; adequacy spine to user-facing `Prop`s is W5f.
- **Probe, not yet authored in-crate.** As with probe21–24, this proves the MATH
  of the prophecy model over the emitted reference in Lean; authoring the model
  as Rust spec/proof fns in tactus-core (loop-closure step) is deferred
  (`DESIGN-W5-soundness.md` §4, probe-first split). The bootstrap `StmData`
  mirror does not yet carry a `&mut`-specific serializer path — when it lands,
  the `decide` bridge (W2) validates the serializer's prophecy-frame shape
  against production, and this probe is the soundness half it plugs into.

## Next (W5e, bootstrap-53)

Closures. Then W5f (adequacy spine, Val-level → user `Prop`s), and eventually
authoring the whole W5 model in tactus-core. With `execSafeF` total over
`StmData` and prophecy shown to be a frame/statement-level model, W5e should
likewise add a value-model reading rather than new frame-threading obstacles.
