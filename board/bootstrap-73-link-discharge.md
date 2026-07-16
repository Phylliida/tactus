---
title: "Link discharge — premise-free closed theorems per proof fn (spec: DESIGN-link-discharge.md)"
status: todo
claimed_by:
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
