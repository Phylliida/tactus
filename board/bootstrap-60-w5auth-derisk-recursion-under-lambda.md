---
title: "W5-auth-0 — de-risk recursion-under-lambda for execSafeF + freeze the authored model shape (probe33)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
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
