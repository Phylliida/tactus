---
title: "Link discharge — premise-free closed theorems per proof fn (spec: DESIGN-link-discharge.md)"
status: in_progress
claimed_by: fable-b73
created: 2026-07-16T23:30:00Z
updated: 2026-07-17T03:30:00Z
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

- (2026-07-16/17, fable-b73) **L1 RECON COMPLETE — production touchpoint
  map** (so the implementing session starts warm):
  - **Weave chokepoint** = the exec-call machinery: `walk_call` /
    `push_post_call_frames` (`sst_to_lean.rs:~3040ff`, `_tactus_ret_N`
    gensym at :3060). Proof-body lemma calls flow through the SAME path
    (proof fns return unit → 1 Unit binder + the instantiated ensures as
    hyp frames). Spine recording hooks here: per call, record (callee
    stable name; per callee-binder: rendered arg LExpr | bound-proof
    recipe | SELF marker).
  - **Bound-proof recipes for L1 (non-recursive)**: caller's own
    `h_<param>_bound` binder when the arg IS a caller signature param
    (covers the W5 corollaries); `(by decide)` for literals; anything
    else → census tag `discharge-bound-gap` (R-c interim; L2's wf
    resolves it — wf predicates + preservation lemmas AUTHORED IN
    TACTUS-CORE, consumed by name).
  - **Clean statement** = "what callers see": the fn's ensures rendered
    by the SAME caller-side renderer that produces woven facts, ∀-closed
    over params + bound hyps. Statement identity across the weave by
    construction — no separate rendering path.
  - **Persistence**: the Link builder (`generate.rs:4027
    build_link_module`) re-derives from the krate and runs even when pkg
    emission is cache-skipped → the spine must be a SIDECAR persisted at
    emission (the existing `.manifest` pattern), read back by the Link.
    PkgEmitOutcome (`generate.rs:3246`) is the carrier to the writer.
  - **Emission point**: closed_clean theorems join `build_link_module`'s
    output after the existing eta-closed defs, in the same topo order
    (`ordered`), with `#tactus_check_axioms` each; stable names via the
    fn path (NOT the line-numbered VC names).
  - Suggested L1 slices: (a) spine recording + sidecar write/read,
    verdict-neutral; (b) clean-stmt rendering + closed_clean for the
    ZERO-SPINE class (u_* re-exports) — first green artifact; (c) the
    non-recursive discharge with bound recipes (W5 corollaries close);
    (d) census tags + gate-note counts. Mutation-kill pins land with (c).

- (2026-07-17, fable-b73) **L1 SLICE (a) LANDED — spine recording + sidecar
  persistence, verdict-neutral.**
  - `lean_ast.rs`: `GoalSpine::Imp` gains `HypProvenance` (CallFact{callee,
    is_self, args:[{text, tag}]} | Branch | HeightFact | Other); new types
    CallFactInfo/SpineArg/SpineArgTag. Provenance is documentation-plus-
    data: never affects the rendered theorem.
  - `sst_to_lean.rs`: `CtxFrame::Hyp` carries provenance; ~20 push sites
    classified honestly (if/match/loop conds + #114 cond_setup = Branch;
    passed Termination assert = HeightFact — the woven decrease fact;
    woven callee ensures = CallFact via `build_call_fact_info`, threaded
    through `push_ret_frames`; everything else Other). Args recorded in
    callee param order, COERCED TO THE PARAM'S TYP via the same
    `coerce_lexpr` bridge the ensures renderer uses (U2) — so `*t`
    records as `t.deref`, matching the woven fact verbatim. Tags:
    param:<name> (caller signature param → its h_*_bound discharges) /
    lit / expr.
  - `generate.rs`: `write_spine_sidecar` — `pkg/<leaf>.spine.json` per
    pkg module, one record per VC: ordered spine descriptors (all{name,
    ty} / let{name, v} / imp{p,...}), written best-effort next to the
    module so the Link builder can read it on cache-skipped runs.
  - Validation: vstd 1530/0; tactus-core regen 138/0 + gate green; 67
    sidecars; `holds_all_append`'s + `holds_close_e`'s sidecars match
    probe34's hand-written discharge 1:1 (incl. height-before-IH and the
    `Tactus.Box.mk tmp__2` instantiation with its defining let);
    wp_stm_sound's Loop arm at full scale = 16 VCs, 11 calls in order,
    8 discriminators, 1 height fact, SELF-marked IH.
  - NEXT: slice (b) — clean-statement rendering + closed_clean for the
    zero-spine class (u_* re-exports) in the Link builder, reading the
    sidecars.

- (2026-07-17, fable-b73) **L1 SLICE (b) LANDED — first green artifacts:
  52 per-fn closed theorems under STABLE names.**
  - `ExecLinkEntry` gains `fn_name` (stable dotted) + `is_proof`; the
    Link builder reads each proof fn's spine sidecar and, for the
    ZERO-SPINE class (exactly one postcondition VC, binders-only spine —
    the VC statement IS the clean statement), emits
    `theorem lib.<fn>_closed : <vc>_stmt := <vc>` + axiom check. True
    exec fns skipped by design; woven-premise fns counted pending.
  - Gate note: "Link discharge: 52 per-fn closed theorem(s) (zero-spine);
    15 proof fn(s) pending (woven premises — slices c/L2)". The 52 = the
    entire u_* family + friends; the 15 pending = the support lemmas +
    wp_stm_sound + ref_wp_sound + corollaries, exactly the c/L2 targets.
  - Validation: vstd 1530/0; tactus-core 138/0, gate green (the Link
    elaborates + axiom-checks all 52); consumption smoke = downstream
    `exact lib.u_holds_all_binder_closed …` in the gate's own
    elaboration environment, rc=0. `theorem` keyword throughout (Q3).
  - NEXT: slice (c) — non-recursive discharge with bound recipes (the
    prophecy/closure corollaries close; needs the positional application
    generator over the sidecar spine); then L2 (fix synthesis + wf).

- (2026-07-17, fable-b73, slice-b addendum) Suite initially FAILED 3
  (test_deadend_*): the census eprintln landed in the diagnostics stream
  as a bare line the harness flags (`[unexpected json]`). Fixed the
  right way: counts ride `PackageGateReport` (statics, the
  PKG_CACHED_VERDICTS pattern) and print via `reporter.report_now
  (note_bare(...))` — the same structured channel as the package-gate
  note. Also: the stable theorem references the per-VC `<vc>_closed`
  def (not the raw theorem) so BINDER-channel helper hyps are already
  applied — uniform across both premise channels. Suite 551/0.
  Committed `5a408af`.
- **Slice (c) lead**: the CLEAN STATEMENT for premise-carrying fns =
  "the fn's ensures as callers see it, ∀-closed over params+bounds" —
  which is exactly what the BROADCAST-LEMMA AXIOM emission already
  renders (krate_preamble's lemma-axiom path via
  collect_broadcast_lemma_funs). Reuse that renderer rather than
  building a new one — statement identity with the weave by
  construction. Then the discharge term = positional application over
  the sidecar spine (probe34 shapes): `()` per Unit binder,
  `lib.<callee>_closed <args>` per call imp, bound recipes per tag
  (param:<n> → caller's h_<n>_bound binder; lit → by decide; expr →
  census `discharge-bound-gap` until L2 wf).
