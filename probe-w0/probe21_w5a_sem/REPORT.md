# probe21 — W5a-0 reference-WP soundness (straight-line fragment)

**Board:** bootstrap-49 (W5a) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~2.6s). Design + model: `DESIGN-W5-soundness.md` §1–3.

## What it pins

The **first soundness rung of the W5 loop.** It proves — over the REAL emitted
reference WP (`lib.wp_stm` / `lib.frame_after` / `lib.close_e` /
`lib.goals_append` in `tactus-core/out/lib`), the analog of probe14 for the
bridge, with NO tactus-core rebuild — that the reference WP is **sound** on the
straight-line fragment `{Skip, Assume, Assert, Seq}`:

```
wp_stm_sound : inFragment s → isHypFrame f → holdsAll (wp_stm f s) st
                 → frameHyps f st → execSafe s st
```

i.e. *if every emitted goal holds, then every assert's obligation holds under
its accumulated hypothesis context* — WP soundness for the fragment. Plus
`ref_wp_sound`, the top-level version seeded through `lib.seed_frame` (for
hyp-frame seeds — the no-∀-params W5a-0 scope).

**Valuation-parametric (open Q §5.5 = option b).** The semantics is parameterised
by leaf oracles `hp : Int→St→Prop` (opaque prop leaves) and
`he : ExprData→St→Prop` (deep obligation exprs), and the theorem quantifies over
ALL of them. `lib.render_exp` stays **fully opaque** (under `he`) — the proof
never evaluates rendering. Consequence: the soundness holds for any leaf
interpretation, and W6's later deepening is a *specialisation*, not a re-proof.

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | `wp_stm_sound` (main) elaborates against the emitted `lib.wp_stm` | ✓ |
| B | `ref_wp_sound` (top-level over `seed_frame`) elaborates | ✓ |
| C | non-vacuity: lone `assert o` delivers `he (render_exp o) st` from its goal | ✓ |
| D | non-vacuity: `assume e; assert o` delivers the obligation UNDER `hp e st` | ✓ |
| E | axiom closure = `[propext, Quot.sound]` — no `Classical.choice`, no `sorryAx` | ✓ |

If any theorem failed to elaborate, `lean` errors and rc≠0.

## How it works (the proof, in four bridging lemmas + one induction)

Semantic model (`DESIGN-W5-soundness.md` §2): `St := Int → Int`; goal denotation
`holds` (Val-level `toProp`); operational safety `execSafe` /`addedHyp` (an
`Assert` faults iff its obligation is false; `Seq` threads the downstream
hypothesis; `Assume` never faults). `hp` (asserted forward hyp) and `he`
(obligation) are kept INDEPENDENT — soundness needs no relation between them,
which is the honest valuation-parametric reading (peer-reviewed with Danielle's
local model).

- **Lemma A `holds_close_e`** — a hyp-frame-closed obligation holds iff, when the
  frame hyps hold, the obligation expr holds. (induction on `f`)
- **Lemma B `frameHyps_frame_after`** — `frame_after` adds exactly `addedHyp a`.
- **Lemma C `frameHyps_append`** — `frameHyps` distributes over `frame_append`.
- **Lemma D `holdsAll_append`** — `holdsAll` distributes over `goals_append`.
- **Main `wp_stm_sound`** — induction on `s`: Assert closes via Lemma A; Seq
  splits via Lemma D and threads the frame via Lemma B; Skip/Assume are trivial.

Scope: W5a-0 restricts frames to `FHyp`/`FNil` (`isHypFrame`) — the fragment's
`frame_after` only ever appends `FHyp`, so hyp-frames are closed under it
(`isHypFrame_frame_after`). `FLet` (Assign) and `FBind`/∀ (seed params) enter at
W5a-1; the `All`/`Let` goal arms of `holds` are unreached here and carry a
placeholder denotation (documented in-file), immaterial to the proven theorem.

## Elaboration idioms (for the next rung + the eventual Rust authoring)

- The emitted defs (`termination_by structural`) **reduce definitionally on
  constructors** (`rfl`), but `simp [lib.close_e]` **cannot generate their
  equational theorems** ("invalid projection x✝.2.1"). Unfold via explicit `rfl`
  lemmas (`u_*` block) + `simp only [those]`, never `simp [defName]`.
- Every recursive mirror type wraps recursive fields in `Tactus.Box`, so plain
  `induction` gives no IH through the box. Recurse by well-founded recursion:
  `termination_by <arg>` + `decreasing_by all_goals (simp_all; omega)` (the
  prelude ships `Tactus.Box.sizeOf_deref` `@[simp]` for exactly this).
- Own semantic defs use `termination_by structural` so they `rfl`-reduce too.
- The tactus prelude is **minimal Lean — no Mathlib**: `tauto` is unavailable;
  use `simp only [and_assoc]` / `[and_imp]` for the propositional shuffles.
- `match f with` (single discriminant) specialises dependent hypotheses
  (`hf : isHypFrame f`); impossible branches close with `hf.elim` (defeq `False`).

## Next (W5a-1, bootstrap-49)

Add `If` (flat two-way, matching `wp_stm`'s If arm) + `FBind`/∀ seed params +
`reqs` as `frameHyps`; give `holds` the real ∀/`upd` and `let` denotation for
`All`/`Let`; lift `ref_wp_sound` past the `isHypFrame` restriction. Then W5b
(Call/Ret), W5c (Loop), … and eventually author the whole model as Rust
spec/proof fns in tactus-core (the loop-closure step — forces the whole-crate
re-verify + olean re-emit).
