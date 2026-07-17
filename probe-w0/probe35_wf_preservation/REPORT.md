# probe35 — wf-preservation lemmas (bootstrap-73, final rung)

**Verdict: PASS, first elaboration, zero axioms.**

## Question
Can spec-fn wf-preservation lemmas (`FrameListWf f → … → FrameListWf (g …)`)
be proven against the current emission, given the rec_1 gap (no equation
lemmas for Box-recursing structural defs)?

## Answer
Yes, trivially — in TERM position. Both lemmas elaborate with no tactics:
- `frame_append_wf` (the archetype: structural recursion + Box.deref):
  `match f, hf with` mirror, each arm an anonymous constructor
  `⟨h1, h2, frame_append_wf t.deref g hr hg⟩`, `termination_by structural f`.
- `ret_frame_wf` (the actual `wp_stm_sound` demand site): match on `rb`,
  compose `frame_append_wf` with a literal-tail `trivial`.

`#print axioms`: **neither depends on any axioms.** Defeq iota whnfs through
the spec fn, the wf predicate, and `Box.mk/.deref` — equation lemmas never
consulted.

## The mechanization recipe (validated by shape)
The proof term is ISOMORPHIC to the spec fn's own body: value-position
constructor `C a b t` ↦ proof `⟨bound(a), bound(b), wf(t)⟩`; recursive call ↦
recursive lemma call; other spec-fn call ↦ that fn's `_wf` lemma; `let` ↦
`let`-bound sub-proof; `if` ↦ dependent if. A synthesizer = the defs
renderer's walk emitting ⟨⟩-terms instead of values.

## Demand set for tactus-core 67/67 (~12 lemmas, all this archetype)
- Ret arm: `ret_frame` (→ `frame_append`); RetBind wf conjunct comes from
  the StmData scrut component (RetBind is scalar-carrying).
- Loop arm: `loop_maintain_frame` → `havoc_lets`, `seed_params`,
  `binders_to_frame`, `seed_binders_hyp_bounds`, `binderprops_to_hyps` (+ if).
- Seq arm: `frame_after` → `loop_use_frame`.
- ref_wp corollaries: `seed_frame` → `binders_to_frame`, `seed_params`.
