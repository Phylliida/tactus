---
title: "Link discharge — premise-free closed theorems per proof fn (spec: DESIGN-link-discharge.md)"
status: in_progress
claimed_by: fable-b73
created: 2026-07-16T23:30:00Z
updated: 2026-07-16T23:30:00Z
---

## Description

Complete the Link layer: discharge the weave-channel callee-fact premises
(body lemma calls — today never discharged; only tactic-referenced binder
deps are) and synthesize the structural fix for recursive proof fns, so
every eligible proof fn gets a **premise-free closed theorem under its
stable name**, kernel-checked in the Link module. Turns the package's
assume-guarantee composition from a meta-argument into an artifact object.

Danielle's steer (2026-07-16): no temporary hacks — this is the
"right way" resolution of bootstrap-66's design fork (option iii), built
as a general emit-module completion, not a W5 special.

Full spec: `DESIGN-link-discharge.md` — read it first. Ladder L0–L4:

- **L0**: probe34 — hand-write `wp_stm_sound_closed` + `ref_wp_sound_closed`
  against the current emission (validates fix shape, discriminator
  discharge, positional weave application, termination-VC consumption)
  BEFORE any codegen. Freeze the term shapes.
- **L1**: spine recording at the weave chokepoint + clean-statement
  rendering + non-recursive discharge codegen.
- **L2**: structural-fix synthesis (single-datatype-param recursion) —
  tactus-core end-to-end; this is the bootstrap-66 unblock.
- **L3**: gate-note counts + census tags + mutation-kill pins + cost
  measurement (tactus-core + tgt).
- **L4** (optional, data-driven): TactusClosed module split/caching;
  mutual-SCC arm.

**Done when:** acceptance §6 of the design doc is met — closed theorems
for all eligible tactus-core proof fns incl. `lib.ref_wp_sound_closed`
(golden-pinned, consumed by `exact` in a probe), mutation-kill pins
in-harness, counts + cost recorded, suite + gates green.

**Blocked by:** nothing. **Blocks:** bootstrap-66 (spine composition
waits for `ref_wp_sound_closed`). Open knobs Q1–Q3 in the doc §8 for
Danielle (naming / default-on / theorem-vs-def).

## Progress

- (2026-07-16, fable-b73) **L0 DONE (probe34) — PASS first elaboration,
  and it earned its keep: found the BOUND GAP (F1/Q4).**
  - Validated (shapes frozen in the probe REPORT): `theorem` + recursive
    fix (`termination_by height` + `decreasing_by` consuming the emitted
    termination VC — consumed twice, once as the woven height premise,
    once for the fix), positional application through interleaved
    Units/lets (zeta), `by simp` discriminators, u_* clean forms as
    direct re-exports, statement-identity across the weave for
    scalar-free callees. Axiom closures core-only. Consumption smoke =
    the bootstrap-66 `exact` shape.
  - **F1 (the finding)**: scalar-param callees carry `h_*_bound` premises;
    woven facts are bare and instantiated at unbounded extrinsic
    projections → the assume-guarantee chain does not compose verbatim
    there. Latent today (all such callees are rfl-class unfolds), but a
    bound-needing ensures would make the clean composed fact underivable.
    Resolution options R-a/R-b/R-c in the REPORT; **R-a (weave the
    callee's guard — woven premise IS the callee's closed statement)
    recommended; Danielle's call before L1.** wp_stm_sound/ref_wp_sound
    discharge is Q4-gated.

- (2026-07-16, fable-b73) **Q4 RESOLVED = R-b, validated in probe34 (rc=0,
  core-only axiom closures).** Walk-back: R-a (approved earlier on my
  recommendation) turns out to push an unprovable guard into caller VCs
  at extrinsic projections — withdrawn with analysis in the REPORT;
  Danielle's no-hacks steer + the honesty norm made this a walk-back, not
  a patch. R-b validated end-to-end: hand `flWf` + the FULL four-arm
  `holds_close_e_closed` under `wf f`, bounds supplied at dispatch, zero
  changes to any VC/closer/proof. New L2 ingredient: wf predicates +
  wf-preservation lemmas live IN TACTUS-CORE (spec/proof fns, consumed by
  name — generator synthesizes no math). L0 is now fully closed including
  the Q4 spike; next = L1 (spine recording + clean-statement rendering +
  non-recursive codegen, now with the wf-premise rule).
