# probe34 — Link-discharge L0 (bootstrap-73)

**Verdict: PASS.** The discharge-term shapes the Link generator will emit
are validated by hand against the current tactus-core emission
(`closed.lean`, rc=0), including the Q4/R-b wf-guarded rung. Axiom
closures: `holds_all_append_closed` and the four-arm `holds_close_e_closed`
= `[propext, Classical.choice, Quot.sound]`,
`holds_close_e_fnil_arm_closed` = `[propext, Quot.sound]` — Lean core only.

## What is frozen for the generator (L1/L2)

1. **`theorem` keyword works everywhere** (Danielle's Q3), including the
   recursive fix: `theorem … := match a with …` + `termination_by
   lib.<D>.height a` + `decreasing_by exact (<termination VC theorem
   applied>).resolve_right (fun h => h.2.elim)`.
2. **u_* clean forms are direct re-exports** — empty-body lemmas have no
   weave, so their pkg theorems are already premise-free.
3. **Positional application through the weave**: `()` per Unit binder, a
   fact proof per woven premise; interleaved lets zeta-reduce under
   application with no special handling. Statement identity across the
   weave holds — the callee's clean theorem instantiated at the recorded
   args typechecks against the woven premise verbatim (same renderer both
   sides).
4. **Discriminator premises** (`isX` / `¬isX` on a constructor) close by
   `(by simp)` terms.
5. **The emitted termination VC theorem is consumed TWICE** for a
   recursive arm: once as the woven height premise (the VC weaves the
   decrease fact before the IH premise), once in `decreasing_by`. Same
   application spine both times — the generator emits it as a `have`.
6. **IH premises are ordinary spine entries**: the fix's own recursive
   call at the recorded (smaller) args.

## F1 — THE BOUND GAP (the probe's finding; blocks 3 of 4 holds_close_e arms)

A callee with u64/scalar params gets `h_*_bound : 0 ≤ x ∧ x < 2^64`
premises on its theorem (faithful u64 emission). But the CALLER's woven
premise is the **bare** fact, instantiated at extrinsically-typed Int
projections (`tmp___0.FBind_val0`) that carry **no bounds** (O9:
datatypes are non-indexed). So the callee's theorem cannot discharge the
woven premise as stated — **the assume-guarantee chain does not compose
verbatim for scalar-projected call args.**

Today this is latent, not unsound: every such callee in tactus-core is an
`rfl`-class unfold whose proof never uses the bound (the fact is true for
all Int). But a callee whose ensures genuinely NEEDED the bound would
make the caller's woven premise unjustifiable at junk datatype members —
and the caller's clean ∀-quantified fact underivable. The discharge pass
is exactly the machine that catches this class forever; surfacing it is
the L0 payoff.

**Resolution — R-b, VALIDATED IN THIS PROBE (and an honest walk-back).**

- **R-a (weave the guard) — WITHDRAWN after deeper analysis.** It was
  initially recommended (and Danielle approved it), but tracing where the
  guard burden lands shows it BREAKS the callers: the guarded woven
  premise (`bounds → fact`) reaches the caller's VC, and the caller must
  *prove* the guard to use the fact — impossible at extrinsically-typed
  projections. The W5 proofs themselves would stop verifying. Repairing
  that requires emitting projection-bound hypotheses in match arms, whose
  justification at the top level needs wf premises anyway — R-a converges
  to R-b with extra churn.
- **R-b (wf-guarded clean forms) — VALIDATED here, and cheaper than first
  costed: ZERO changes to any VC, closer, or existing proof.** The bare
  woven premise is exactly what the callee's theorem produces once its
  bound binders are instantiated — so the generator supplies bounds at
  DISPATCH time, from a `wf` premise on the clean theorem.
  `∀ d, wf d → fact` is also the semantically faithful statement: wf is
  precisely the image of the Verus u64 typing inside the extrinsic Lean
  model (O9). Demonstrated: `flWf` (hand version of the generated
  predicate) + the FULL four-arm `holds_close_e_closed` under it —
  axiom closure `[propext, Classical.choice, Quot.sound]`. On concrete
  serialized literals wf is free (`decide` leaves).
- **R-c (tag-and-skip)**: remains the honest interim for shapes L1/L2
  don't cover yet.

**L2 design consequence (the wf family lives in tactus-core).** Dispatch
at COMPUTED datatype args (e.g. wp_stm_sound's Loop arm calling at
`loop_maintain_frame f …`) needs wf-PRESERVATION facts
(`wf f → wf (frame_append f g)` etc.). The right home for these is
tactus-core itself: wf predicates as ordinary structural spec fns
(bool, kernel-computing) and preservation lemmas as ordinary proof fns —
emitted, kernel-checked, and CONSUMED BY NAME by the generator exactly
like the termination VC theorems. The generator never synthesizes math.

**flWf emission note:** recursion through `Box.deref` gets no Lean
equational theorems (the known `rec_1` fact) — `simp [flWf]` is
unavailable; iota on literals + anonymous constructors work fine. The
generated wf in the defs family inherits the same discipline as every
other mirror fn.

## Fragility note (why the probe pins shapes, not names)

The pkg VC theorem names embed source line numbers
(`_at_lib_3514_13_3`); any tactus-core edit above them shifts the names
and this probe needs re-pinning. That fragility is precisely why
consumers get the generator's STABLE-named closed theorems, never the VC
names — the probe accepts it as scaffolding, the product does not.

## Files

- `closed.lean` — u_* re-exports, `holds_all_append_closed` (the full
  fix-synthesis demonstrator: recursive, bound-free chain),
  `holds_close_e_fnil_arm_closed` (the bound-free arm), the R-b rung
  (`flWf` + the FULL four-arm `holds_close_e_closed` under wf — the Q4
  resolution, validated), a concrete-literal wf witness, and the
  consumption smoke (`exact`/`rw` downstream use).
- `run.sh` — elaborates against tactus-core/out/lib + preludes.
