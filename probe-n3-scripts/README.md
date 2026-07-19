# N3 investigation probes (2026-07-19)

Hand-validated against tactus-algebra artifacts (regenerate with a bare
`--lean-backend` run of that crate; adjust LEAN_PATH to the crate's
tactus-lean/lib + prelude cache). All three elaborate clean.

**The bet these validate:** "the user's proof body is the script
skeleton" — inlined call-ensures land complete as hoisted hypotheses,
and a script transcribed from body + goal shape closes obligations the
searched rung cannot.

* `zpoly_probe.lean` — script form A (branch + axiom-call):
  `subst <hoist-eqs>; simp only [<goal spec fns>]; split;
  · <guard omega> · exact <call-ensures hyp>`.
* `zpoly_generic.lean` — the NO-provenance interim form: a
  `split <;> simp_all <;> omega` arm after the rung's simp tail closes
  the same class (spec-fn unfold exposing an omega-guarded if). Cheap
  derived-closer extension candidate.
* `pmul_conv.lean` — script form B (definitional step of a RECURSIVE
  spec fn): `intro <spine>; rw [<head fn>]; simp only [<branch hyp>,
  if_false]; rfl`. Key lessons: recursive fns can NEVER ride simp sets
  (their eq_1 rewrites loop to maxRecDepth — observed), so one-step
  `rw` is THE move; and bare `rw` suffices (first-match instantiation
  leaves the RHS's differently-instantiated recursive call alone; no
  Mathlib conv needed in the slim prelude).

Taxonomy of tactus-algebra's 171 residual failures (post-B6, all
elaboration-clean): pmul family ~100+ (forms A/B + eqv-chaining),
Rational recip/mul nonlinear (~16, genuine ring/field proof power),
divmod (9), small tail (generic split-arm food).
