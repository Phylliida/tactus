# probe34 — Link-discharge L0 (bootstrap-73)

**Verdict: PASS, first elaboration.** The discharge-term shapes the Link
generator will emit are validated by hand against the current tactus-core
emission (`closed.lean`, rc=0). Axiom closures: `holds_all_append_closed`
= `[propext, Classical.choice, Quot.sound]`, `holds_close_e_fnil_arm_closed`
= `[propext, Quot.sound]` — Lean core only.

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

**Resolution options for L1 (Danielle's call, design §8 gains a Q4):**

- **R-a (weave the guard, recommended)**: the weave includes the callee's
  bound premises in the woven fact (`0 ≤ x ∧ x < N → <fact>`) whenever
  the callee has them — i.e. the woven premise becomes the callee's
  closed statement instantiated, verbatim. Composition then works
  unconditionally. Cost: caller VC goals gain a guard hypothesis; the
  existing closers likely absorb it (simp intro), but every affected
  proof re-verifies once (VC-shape change = cache invalidation for
  affected fns).
- **R-b (wf-guarded clean forms)**: leave the weave alone; the clean
  closed theorem for a fn whose discharge crosses the gap takes a
  well-formedness premise (`FrameList.wf f` = all scalar fields bounded)
  and dispatch supplies field bounds from it. Cost: a new wf predicate
  family per datatype + wf-threading; the clean statements are no longer
  premise-free (though the premise is honest).
- **R-c (status quo + tag)**: discharge only gap-free fns; tag the rest
  `discharge-bound-gap`. Honest but leaves wp_stm_sound/ref_wp_sound
  undischargeable (their u_* callees carry scalar params) — does NOT
  unblock bootstrap-66. Only acceptable as an interim L1 milestone.

Note for R-a: this makes the invariant "a woven premise IS the callee's
closed statement" — the same statement-identity-by-construction principle
the rest of the architecture uses, which is why it is recommended.

## Fragility note (why the probe pins shapes, not names)

The pkg VC theorem names embed source line numbers
(`_at_lib_3514_13_3`); any tactus-core edit above them shifts the names
and this probe needs re-pinning. That fragility is precisely why
consumers get the generator's STABLE-named closed theorems, never the VC
names — the probe accepts it as scaffolding, the product does not.

## Files

- `closed.lean` — u_* re-exports, `holds_all_append_closed` (the full
  fix-synthesis demonstrator: recursive, bound-free chain),
  `holds_close_e_fnil_arm_closed` (the arm that composes; the other three
  arms are F1-blocked), consumption smoke (`exact`/`rw` downstream use).
- `run.sh` — elaborates against tactus-core/out/lib + preludes.
