---
title: "W5-auth-0 — de-risk recursion-under-lambda for execSafeF + freeze the authored model shape (probe33)"
status: done
claimed_by: fable-b60
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T18:05:00Z
---

## Description

First rung of the W5 loop-closure authoring tail (umbrella bootstrap-10). Before
the batched tactus-core edit (bootstrap-61), close the one authoring-shape
question probe32 did **not** cover: the probe-side `execSafeF` Seq arm recurses
*under a continuation lambda* —

```
execSafeF f (Seq a b) st = execSafeF f a st
  ∧ closeSem (frameDelta a) st (fun st' => execSafeF (frame_after f a) b st')
```

probe32 confirmed `spec_fn` oracle *params* + recursive structural spec fns +
`structural_decreases` + the discharge closer. It did not exercise a recursive
call inside a closure body, which Verus's termination checker historically
rejects. Known candidate patterns, in preference order:

1. **Mutual recursion / defunctionalized continuation** — the
   `compspec_iterate` idiom (see memory `feedback_closure_identity`): make
   `closeSem` and `execSafeF` a mutual pair where the "continuation" is a
   defunctionalized marker (e.g. `closeSemK : FrameList → St → ContK → bool`
   with `ContK = KExecSafe(FrameList, StmData)`), so no lambda captures the
   recursive call.
2. Inline `closeSem`'s telescope walk directly into the Seq arm (fuse the two
   fns for the Seq case only).
3. If tactus/Verus happens to accept the lambda form with
   `structural_decreases`, use it directly (test this first — cheapest).

Probe: `probe-w0/probe33_w5auth_shape/` — scratch crate through the real
bootstrap binary (`--lean-backend --lean-all-proofs`, recipe in
`reference_tactus_proof_authoring_idioms`), containing a minimal
`FrameList`/`StmData` (3–4 arms incl. Seq), `closeSem`, `execSafeF`, and one
tiny induction proof over the pair to confirm the IH threads through whichever
shape wins.

**Also freeze here (so bootstrap-61 is one clean edit):** authored names +
signatures for the whole model surface — St representation, oracle spec_fn
params (`hp`, `lv`, and the W5f oracle triple if it enters the crate),
`holdsAll`, `closeSem`, `execSafeF`, `frameDelta`. Record them in the probe
REPORT.md as the frozen interface.

**Done when:** probe33 verifies + emits kernel-clean (0 errors, axiom closure
propext-class only) with the Seq-arm recursion in the winning shape, and the
frozen model interface is written down.

**Blocked by:** nothing. Spec: `DESIGN-W5-soundness.md` §2 (model), probe24
(`probe-w0/probe24_w5c_sem/`) for the exact hand-Lean equations being mirrored.

## Progress

- (2026-07-16, fable-b60) Recon against probe24 sharpened the question: the
  W5c frame-carrying lift already removed recursion-under-lambda (Seq is a
  plain conjunction; the theorem is a direct implication). The genuinely
  untested shapes were M1 spec-closure literals (`upd`), M2 nested spec_fn
  types (state-consuming oracles), M3 recursion under `forall` (FBind/All
  arms), M4 induction THROUGH the ∀ arm. Authored probe33 as a mini-W5c
  exercising all four.
- (2026-07-16, fable-b60) Run 1: 31/32 — M1/M2/M3 pass first try; the M4
  failure exposed backend fact F1 (calls inside `assert forall ... by` are
  DROPPED — render as `True`, self-calls emit no termination VC). Run 2
  (st-generic lemma, u_* still under the binder): 3 errors — F1 is general,
  not self-call-specific. Hand-tested the fix shape against the emitted defs
  olean, then re-authored: **run 3 = 32 verified, 0 errors.**

## Writeup

**DONE — PASS (`probe-w0/probe33_w5auth_shape/`, `32 verified, 0 errors`,
~65s, axiom closures ⊆ [propext, Classical.choice, Quot.sound], no sorryAx).**

All four mechanism shapes work; two backend facts discovered, and the
authoring idiom they force is frozen in REPORT.md (binding for
bootstrap-61..64):

1. **F1**: proof-fn calls inside `assert forall ... by` blocks are dropped
   from the VC (`True →`); never inject facts under a binder.
2. **F2**: ∀st-quantified equation hyps DO rewrite under inner binders via
   simp_all — so the idiom is **state-generic ensures** (`ensures forall|st|
   #[trigger] lhs == rhs`) for every state-dependent lemma; IHs and u_*
   unfolds become plain arm-body calls. st-as-param stays fine when no binder
   is crossed (both shapes coexist, validated).
3. u_* one-step unfolds close with closer `first | tactus_auto | (intros <;>
   rfl)` (definitional on constructor literals under the ∀st wrap).
4. The probe32 induction discharge closer is unchanged and suffices.

The frozen model interface for bootstrap-61 (names/types/continuation
decision — two first-order `close_sem_*` fns, NO ContK datatype, NO
higher-order continuation params) is tabulated in probe33's REPORT.md.
