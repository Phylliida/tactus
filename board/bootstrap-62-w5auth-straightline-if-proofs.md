---
title: "W5-auth-2 — soundness proofs, straight-line + If fragment (probe21/22 arms authored)"
status: done
claimed_by: fable-b62
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T21:30:00Z
---

## Description

First proof rung: author the probe21/probe22 theorems as tactus-core proof fns
— `wp_stm` soundness over `{Skip, Assume, Assert, Seq, If}` with an arbitrary
frame telescope:

```
holdsAll (wp_stm f s) st  ⟹  closeSem f st (execSafeF … s ·)
```

(exact statement per the frozen bootstrap-60 interface; the If fall-through
side-condition is deferred to bootstrap-63 exactly as it was in the probes —
scaffold with whatever fragment guard is cheapest, to be dropped in
bootstrap-64).

Authoring recipe (all validated by probe32 — see
`reference_tactus_proof_authoring_idioms`):

- Per-constructor `u_*` unfold lemmas as empty-body proof fns (height-recursive
  spec fns get no Lean eq-lemmas; unfolds enter each VC as hyps via calls in
  the match arms).
- Support lemma `closeSem_append` (probe22) as its own proof fn.
- `#[verifier::structural_decreases]` on the induction proof fn; the discharge
  closer string from probe32:
  `first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))`.
- Fast iteration on the emitted `out/lib/pkg/lib__*.lean` VC files with `lean`
  directly before the confirming full run.

**Done when:** tactus-core `--lean-all-proofs` 0 errors with the fragment
soundness proof fn(s) + `closeSem_append` verified; axiom closure clean; a
short progress note records which scaffolding (if any) was used for the If
fall-through.

**Blocked by:** bootstrap-61.

## Progress

- (2026-07-16, fable-b62) Scope shifted per bootstrap-61's plan note: this
  rung = the SUPPORT layer, not a fragment-guarded induction (no scaffolding
  ever existed — see bootstrap-64). Landed: 18 data-side u_* unfolds
  (close_e/close_each_e/goals_append/wp_stm, ALL arms incl. the expanded Loop
  equation) + `holds_close_e` (st-generic, the M4-at-scale goal↔semantics
  alignment through the FBind ∀-arm and FLet) + `holds_all_append`. First-try
  green: **118 verified, 0 errors**, gate 48/50 reused.

## Writeup

Support layer for the wp_stm_sound induction. The probe33 idiom carried
without modification: st-generic ensures for holds_close_e (its FrameList
induction crosses the FBind binder), st-as-param for holds_all_append (no
binder crossed). Data unfolds are probe32 empty-body shape, default closer —
including u_wp_loop's giant let-expanded equation (closed by tactus_auto).
