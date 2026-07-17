# probe36 — wf family: every remaining emission shape (bootstrap-73 R-c)

**Verdict: FULL PASS, all lemmas axiom-free.**

Validated on top of probe35's archetype:
1. **Mutual wf defs** over the mutual inductive family (RawExp/RawArmList/
   RawList): `mutual … end` with per-def `termination_by structural x`
   INSIDE the block. Needed because StmDataWf (wp_stm_sound's own hwf)
   carries RawExpWf conjuncts.
2. **If inside a match arm** (havoc_lets): `rw [if_pos h]` FAILS — the
   goal keeps the un-unfolded recursive application (rec_1: no equation
   lemmas). Working shape: `(congrArg FrameListWf (if_pos h)).mpr p` —
   pure defeq transport, no syntactic rewriting.
3. **Nested match on a second wf scrutinee** (seed_params over
   BinderList × ParamBoundList): `match bounds, hb with` inside an arm,
   destructuring both. Plain.
4. **Lets + top-level if + composition** (loop_maintain_frame):
   NON-recursive defs DO have equation lemmas → `by unfold …; by_cases h;
   rw [if_pos h]; exact <composition>` works directly.
5. **Conjunct granularity**: a lemma's bound hypothesis
   `(h : 0 ≤ x ∧ x < N)` is passed WHOLE as one ⟨⟩ component — never
   split into .1/.2.

Synthesis rules confirmed for the entire demand set: ret_frame,
frame_append, frame_after (same shapes), havoc_lets, seed_params,
seed_binders_hyp_bounds, binders_to_frame, binderprops_to_hyps,
loop_maintain_frame, loop_use_frame, seed_frame.
