# probe22 — W5a-1 reference-WP soundness (branching fragment + ∀-params)

**Board:** bootstrap-49 (W5a) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~3.1s). Design + model: `DESIGN-W5-soundness.md` §1–3. Extends probe21
(W5a-0).

## What it pins

The **second soundness rung of the W5 loop.** Over the REAL emitted reference
WP (`lib.wp_stm` / `lib.frame_after` / `lib.frame_append` / `lib.close_e` /
`lib.goals_append` / `lib.diverges` / `lib.is_skip` / `lib.seed_frame` in
`tactus-core/out/lib`, with NO tactus-core rebuild — the analog of probe14 for
the bridge) it proves the reference WP **sound** on the branching fragment
`{Skip, Assume, Assert, Seq, If}` over an **arbitrary frame telescope**:

```
wp_stm_sound : inFragment s → holdsAll (wp_stm f s) st → closeSem f st (execSafe s ·)
```

i.e. *if every emitted goal holds, then under the frame's ∀/→/let telescope
every assert's obligation holds under its accumulated hypothesis context.* Plus
`ref_wp_sound`, the top-level version seeded through the genuine `lib.seed_frame`
(an all-`FBind` ∀-telescope: `typ_params ++ params/bounds ++ reqs`).

### The three lifts over W5a-0 (probe21)

1. **`If`** — the flat two-way branch matching `wp_stm`'s If arm
   (`goals_append` of the then-branch closed under `FHyp c` and the else-branch
   closed under `FHyp nc`). `execSafe (If c nc t e)` = each branch safe under
   its guard leaf: `(hp c → execSafe t) ∧ (hp nc → execSafe e)`.
2. **`FBind`/∀ seed params + `FLet` lets** — via the **general frame telescope
   interpretation** `closeSem : FrameList → St → (St → Prop) → Prop`, folding
   `FBind → ∀ (upd)`, `FHyp → →`, `FLet → let (upd ∘ lv)`. This **replaces**
   W5a-0's `isHypFrame f → frameHyps f st → execSafe s st` with the
   restriction-free `closeSem f st (execSafe s ·)` (the W5a-0 statement is the
   all-`FHyp` special case). The `isHypFrame` guard is **gone**.
3. **Real `All`/`Let` denotation for `holds`** — `All x _ t` → `∀ n, holds t
   (upd st x n)`, `Let x v t` → `holds t (upd st x (lv v st))` (they were
   unreached placeholders in W5a-0; now reached under `FBind`/`FLet` and
   faithful).

**Valuation-parametric (open Q §5.5 = option b).** THREE opaque leaf oracles —
`hp : Int→St→Prop` (opaque prop leaves), `he : ExprData→St→Prop` (deep
obligation exprs; `render_exp` stays **fully opaque**), `lv : Int→St→Int`
(let-value leaves) — and the theorem quantifies over ALL of them. W6's later
deepening is a *specialisation*, not a re-proof.

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | `wp_stm_sound` (main, arbitrary telescope) elaborates against emitted `lib.wp_stm` | ✓ |
| B | `ref_wp_sound` (top-level over the genuine all-`FBind` `lib.seed_frame`) elaborates | ✓ |
| C | non-vacuity: `if c { assert o }` delivers `he (render_exp o)` UNDER `hp c` | ✓ |
| D | non-vacuity: a single-`FBind` seed delivers the obligation for ALL `∀ n` valuations | ✓ |
| E | axiom closure = `[propext, Quot.sound]` — no `Classical.choice`, no `sorryAx` | ✓ |

If any theorem failed to elaborate, `lean` errors and rc≠0.

## How it works (the proof)

Semantic model (`DESIGN-W5-soundness.md` §2, generalised): `St := Int → Int`;
`upd st x n`; `holds` (Val-level `toProp`, now faithful on All/Let); the general
telescope `closeSem`; `execSafe`/`addedHyp` (an `Assert` faults iff its
obligation is false; `Seq` threads the downstream hyp; an `If` requires each
branch safe under its guard; `Assume` never faults).

**Frame telescope algebra** — three structural lemmas on `closeSem`:
- `closeSem_congr` — pointwise-iff bodies give equal `closeSem` (shuffles `True → ·`).
- `closeSem_triv` — a `fun _ => True` body closes any telescope (Skip/Assume).
- `closeSem_and` — `closeSem` distributes over `∧` (∀/→/let each preserve it) —
  the Seq/If combiner.

**Bridging lemmas** (the DESIGN §3 skeleton, generalised from FHyp-only to the
full telescope):
- **Lemma A `holds_close_e`** — `holds (close_e f o) st ↔ closeSem f st (he (render_exp o) ·)`. (induction on `f`; All→∀ arm now live)
- **Lemma C `closeSem_append`** — `closeSem (frame_append f g) st body ↔ closeSem f st (closeSem g · body)`.
- **Lemma B `closeSem_frame_after`** — `frame_after` threads exactly `addedHyp a`; the If arm uses
  `diverges_zero_of_inFragment` to kill the fall-through (see caveat).
- **Lemma D `holdsAll_append`** — `holdsAll` distributes over `goals_append`.
- **Main `wp_stm_sound`** — induction on `s`: Assert closes via Lemma A; Seq
  splits via Lemma D, rewrites the second half via Lemma B, and combines via
  `closeSem_and`; **If** splits via Lemma D, rewrites each branch via Lemma C
  (peeling the `FHyp c`/`FHyp nc`), and combines via `closeSem_and`; Skip/Assume
  are `closeSem_triv`.

## Honest scope / caveats

- **If fall-through is out-of-fragment.** `frame_after`'s If arm forwards `¬cond`
  (the `nc` leaf) into the continuation ONLY when the then-branch **diverges**
  (`diverges t = 1`, i.e. contains `Ret`/`DeadEnd`) and the else is `Skip`.
  Divergence primitives are not in `{Skip,Assume,Assert,Seq,If}`, so
  `diverges_zero_of_inFragment` shows `diverges t = 0` for any in-fragment `t`,
  hence in-fragment `frame_after f (If) = f` and `addedHyp (If) = True` — an
  in-fragment If genuinely merges nothing downstream. This is the **faithful
  in-fragment reading**, not a shortcut; the general fall-through `¬cond`
  forwarding is **W5b** (which adds `Ret`/`DeadEnd`).
- **Independent guard leaves.** `hp c` / `hp nc` (then/else guards) are the same
  oracle on independent leaf ids — NOT constrained `hp nc = ¬ hp c`. Requiring
  each branch safe under its own guard is the conservative (stronger) reading and
  matches how `wp_stm` threads `c`/`nc` as independent `FHyp`s. Same philosophy
  as W5a-0's independent `hp`/`he`.
- **Val-level, partial correctness** (unchanged from W5a-0): soundness is stated
  at the Val level (`holds`); the adequacy spine to user-facing `Prop`s is W5f.
  No termination arm (Loop = W5c).
- **Probe, not yet authored in-crate.** As with probe21, this proves the MATH of
  soundness over the emitted reference in Lean; authoring the model as Rust
  spec/proof fns in tactus-core (the loop-closure step, forcing whole-crate
  re-verify + olean re-emit) is deliberately deferred (`DESIGN-W5-soundness.md`
  §4, probe-first split).

## Elaboration idioms (new vs probe21)

- The `closeSem`/`holds` FBind/All arms recurse **under a `∀ n` binder** with
  `termination_by structural` — verified accepted (the recursive arg `t.deref`
  stays structural under the binder).
- `closeSem_congr` is the workhorse for reshaping the body function under a fixed
  telescope (e.g. `True → body ↔ body`, `closeSem (FHyp c FNil) st' body ↔
  (hp c st' → body st')`) — cheaper and more robust than `simp`-under-binder.
- Skip/Assume main arms use `funext` + `simp` to rewrite `(fun st' => execSafe
  Skip st')` to `(fun _ => True)` before `closeSem_triv` (the `funext` is a Lean
  theorem, not an axiom — closure stays `[propext, Quot.sound]`).
- The `frame_after` If `if`-reduction uses `if_neg` (instance-polymorphic), fed a
  `¬(diverges t = 1 ∧ …)` proof discharged by `omega` from `diverges t = 0` —
  robust against the emitted `if`'s Decidable-instance choice.

## Next (W5b, bootstrap-50)

`Call` (the exec call rule) + `Ret`/`ret_frame` — the post-call frame as ∀/#128
ret-eq, and the If fall-through's `¬cond` forwarding becomes live (needs
`Ret`/`DeadEnd`). Then W5c (Loop), W5d (&mut/prophecy), W5e (closures), W5f
(adequacy spine), and eventually author the whole model in tactus-core.
