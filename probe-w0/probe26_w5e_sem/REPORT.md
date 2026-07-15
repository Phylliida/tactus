# probe26 — W5e reference-WP soundness (closures: DeadEnd isolation + Assume forwarding)

**Board:** bootstrap-53 (W5e) / bootstrap-10 (W5 umbrella). **Status:** PASS ✓
(rc=0, ~3.0s, zero warnings). Design + model: `DESIGN-W5-soundness.md` §4 (W5e
row) + board bootstrap-53. Extends probe25 (W5d).

## What it pins

The **sixth soundness rung of the W5 loop — closures.** Over the REAL emitted
reference WP (`lib.wp_stm` / `lib.frame_after` / `lib.frame_append` /
`lib.close_e` / `lib.render_exp` / `lib.seed_frame` in `tactus-core/out/lib`, NO
tactus-core rebuild) it proves that a **closure needs no new `StmData`
constructor** — it is faithfully modeled by the EXISTING `DeadEnd` + `Assume`
constructors — and that the reference WP treats it soundly.

```
closure_creation_sound :
  holdsAll (wp_stm f (Seq (DeadEnd body) (Assume ext))) st  ↔  execSafeF f body st
```

i.e. the reference WP for a closure creation reduces **exactly** to the closure
body's obligation under the enclosing frame `f`; the `DeadEnd` wrapper and the
external-spec `Assume` add no obligation of their own. Axiom closure
`[propext, Quot.sound]` on all six theorems — no `Classical.choice` (render_exp
stays opaque), no `sorryAx`.

## The key realization: W5e is a DeadEnd+Assume model, not a new arm

W5c's `execSafeF` / `wp_stm_sound` is already an **iff, TOTAL over the whole
`StmData` vocabulary, over an arbitrary frame telescope** (10 constructors:
Skip/Assume/Assign/Assert/Call/Ret/DeadEnd/If/Seq/Loop). A closure adds nothing
structural — it decomposes into two constructors that are already there. W5e's
honest content is therefore, exactly as W5d (prophecy): (1) pin the **concrete**
closure shape, (2) show the general theorem instantiates to it, (3) discharge
the **isolation** subtlety, (4) confirm the model against the **actual Verus
encoding** (not first principles).

## How Verus actually encodes a closure (verified from source)

Not reasoned from first principles — read off `verus/source/vir`:

- An exec/proof closure `NonSpecClosure{params, body, requires, ensures, ret,
  external_spec}` (`ast.rs:1058`) lowers to exactly **two** SST statements
  (`ast_to_sst.rs:1964–2003`):
  1. `StmX::ClosureInner{body}` — which `sst_to_air.rs:2548–2566` compiles to
     **`StmtX::DeadEnd(body)`** (modulo prepended captured-var typ-invariant
     `Assume`s). The body itself (`exec_closure_body_stms`, `ast_to_sst.rs:3556`)
     is ordinary statements: `Assume(req)` for each requires (line 3590), the
     body, then `init_var(ret)` + `Assert(ens)` for each ensures
     (lines 3649–3661). **Pure W5a–c vocabulary.**
  2. `StmX::Assume(external_spec)` (line 1999) — the contract the surrounding
     world may assume about the closure **object** after creation
     (`∀ args, ClosureReq(c,args) → ClosureEns(c,args,ret)`; the `external_spec`
     is filled in during `ast_simplify`).
- So a closure  ≈  `Seq (DeadEnd body) (Assume ext)`. Both constructors are
  already in the vocabulary; there is **no** closure-specific `StmData`
  constructor.
- **Spec closures** (`ExprX::Closure`, `ast_to_sst.rs:1946`) lower to a pure
  `BndX::Lambda` **expression** — an opaque `he∘render_exp` leaf in the reference
  model — preceded only by ordinary spec-precondition `Assert`s. No new statement
  structure either.

## The load-bearing emitted facts (both `rfl`, restated as `u_*`)

- `frame_after f (DeadEnd b) = f` (`u_fa_deadend`) — a `DeadEnd` contributes
  **nothing** to the continuation frame: the closure body's local hypotheses (its
  `requires`, its params) are **quarantined** and never contaminate downstream
  obligations. This isolation is exactly what makes it sound to verify the body
  under its own `requires` without those requires leaking to sibling code.
- `wp_stm f (DeadEnd b) = wp_stm f b` (`u_wp_deadend`) — the body's obligations
  are emitted under the **enclosing** frame `f` (the closure captures the outer
  context).

## The isolation subtlety (flagged by Danielle's local model, discharged)

The local model raised the **"creation vs. invocation" quantification worry**:
does verifying the body at the creation-time state check the closure for only one
value of its parameters, and does relying on the enclosing frame `f` make the
closure a "time bomb" (safe at creation, unsafe at a later invocation)? Its
premise about parameters turned out **incorrect for the reference** (see the
∀-params witness below), but its structural instinct — *the body relies on
creation-time context; is that properly isolated?* — was right and sharpened the
write-up. The probe discharges it concretely:

```
closure_deadend_isolates :  Seq (DeadEnd (Assume q)) (Assert P)  ↔  he (render P) st     -- UNGATED by q
seq_assume_gates        :  Seq        (Assume q)  (Assert P)  ↔  (hp q st → he (render P) st) -- GATED by q
```

The DeadEnd-wrapped body assumption `q` does **not** reach the continuation
assert; the bare (unwrapped) assume **does** gate it. The two reduced forms
**differ** — which they could not, if the `DeadEnd` failed to quarantine the
body's hypothesis. This is the W5e analog of W5d's temporal-placement witness.

**Negative control (run manually, not in `run.sh`):** claiming the *gated* RHS
(`hp q st → he (render P) st`) for the DeadEnd-wrapped program **fails to
elaborate** (`unsolved goals` — the reduced LHS is the *ungated* `he (render P)
st`, and `he`/`hp` are opaque). Confirms the isolation is tight, not a vacuous
artifact.

## Contract forwarding (the analog of W5d's resolve pin)

```
closure_forwards_contract :
  holdsAll (wp_stm FNil (Seq (closure body ext) (Assert P))) st
    ↔  (execSafeF FNil body st  ∧  (hp ext st → he (render P) st))
```

After the closure, the continuation **does** see the external spec — the assert
`P` is gated by `hp ext` (`frame_after f (closure) = frame_after f (Assume ext) =
FHyp ext`) — while the body obligation is delivered alongside. The trailing
`Assume` threads the closure contract forward, exactly as the resolve `Assume`
did for prophecy.

## What `run.sh` proves (one `lean` elaboration, rc=0)

| # | claim | result |
|---|-------|--------|
| A | full W5c core carries over (`wp_stm_sound` iff, TOTAL over StmData, arbitrary telescope) | ✓ |
| B | `ref_wp_sound` (top-level over the genuine `lib.seed_frame`) | ✓ |
| C | `closure_creation_sound`: closure creation ↔ body obligation under enclosing `f` | ✓ |
| D | `closure_deadend_isolates`: DeadEnd-wrapped body assumption UNGATES the continuation | ✓ |
| E | `seq_assume_gates`: bare assume GATES the continuation (the differ-witness) | ✓ |
| F | `closure_forwards_contract`: external-spec Assume forwards the contract (`hp ext` gate) | ✓ |
| G | ∀-params witness: body obligation checked for EVERY param valuation `upd st p n` | ✓ |
| H | non-vacuity: body obligation must actually hold (opaque `he`) | ✓ |
| I | axiom closure = `[propext, Quot.sound]` on all six theorems | ✓ |

## Honest scope / caveats

- **No new proof engine.** W5e rides the W5c `execSafeF` iff verbatim; the closure
  theorems are instantiations at concrete programs + frames. That is the *point*
  of W5c totalizing over arbitrary frames — closures are subsumed by the existing
  `DeadEnd`/`Assume` machinery. The **non-vacuous** deltas are: (i) the
  DeadEnd+Assume reading is made explicit and matched to the emitted WP
  (`closure_creation_sound`), (ii) the DeadEnd isolation is verified against the
  emitted `frame_after (DeadEnd _) = f` (`closure_deadend_isolates` vs
  `seq_assume_gates` + negative control), and (iii) the external-spec forwarding
  is pinned (`closure_forwards_contract`).
- **∀-params is via the outer `∀ st`, faithfully.** The closure params are fresh
  distinct ids (Verus `declare_var_stm`), NOT frame `FBind` binders; the reference
  does not add them to the frame (`wp_stm f (DeadEnd b) = wp_stm f b`). Soundness
  quantifies `∀ st` over all valuations, so the params are ∀-bound by `∀ st` — the
  ∀-params witness makes this concrete (the body obligation holds at the arbitrary
  `upd st p n`, for all `n`). This matches AIR, where the params become fresh
  unconstrained constants.
- **Creation-time context reliance is sound by the frozen-environment invariant
  (spec adequacy).** The body is verified once, at creation, under the enclosing
  frame `f` — it may rely on facts about captured variables. This is sound because
  Verus **forbids closures from capturing mutable references**
  (`closures.rs::check_closure_well_formed`), freezing the captured environment,
  so a fact true at creation stays true at every invocation. The reference is
  faithful to Verus's own (sound) treatment; the frozen-environment invariant is a
  **spec-adequacy** point (§8.5), not a Val-level WP-faithfulness obligation the
  probe needs to (or can) internalize. If a future Verus allowed mutable capture,
  the model would need the captured facts re-established per invocation — the
  machinery already emits the body obligation, so the change would be localized.
- **Val-level, partial correctness** (unchanged from W5c/W5d): soundness at the
  `holds` Val level; adequacy spine to user-facing `Prop`s is W5f.
- **Probe, not yet authored in-crate.** As with probe21–25, this proves the MATH
  of the closure model over the emitted reference in Lean; authoring the model as
  Rust spec/proof fns in tactus-core (loop-closure step) is deferred
  (`DESIGN-W5-soundness.md` §4). The bootstrap `StmData` mirror does not yet carry
  a closure serializer path — when it lands (a `NonSpecClosure` → `Seq (DeadEnd
  body) (Assume ext)` transcription), the W2 `decide` bridge validates the
  serializer's DeadEnd+Assume shape against production, and this probe is the
  soundness half it plugs into.

## W5 ladder status after W5e

With W5a–e all landed, the **entire `StmData` vocabulary + prophecy + closures**
are shown sound (an iff, actually — sound + faithful) at the Val level, over an
arbitrary frame telescope. The remaining rung is **W5f — the adequacy spine**
(`TGoal.toProp` + a structural induction relating the Val-level `holds`
denotation to the user-facing `Prop`s), which lifts soundness from the Val level
(the drift-detector) to the actual theorems users prove. Then: authoring the
whole W5 model in tactus-core (the loop-closure step).
