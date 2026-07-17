---
title: "Link discharge — premise-free closed theorems per proof fn (spec: DESIGN-link-discharge.md)"
status: in_progress
claimed_by: fable-b73
created: 2026-07-16T23:30:00Z
updated: 2026-07-18T09:00:00Z
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

- (2026-07-17, fable-b73) **FIX SYNTHESIS LANDED (L2 core) — the generator
  machine-writes probe34's recursive discharge and the kernel checks it.**
  Plan inverted on data: ALL nine corollaries call wp_stm_sound, so
  "slice (c) closes corollaries" was wrong — everything funnels through
  the wf rung. Today = the shared machinery:
  - **Sidecar v2**: `HypProvenance::Branch(Option<BranchTest>)` (scrut/
    dt/variant/pos from the VIR `IsVariant` at the branch push) + per-VC
    `leaf` texts + absorbed-hyp provenance (`GoalSpine::All` carries
    `Option<HypProvenance>`; `split_leading_binders` was NAMING leading
    hyps `_h_ctx_N` and dropping their CallFact — now preserved through
    the shape, fold-neutral for the W2 cert bridge).
  - **`link_discharge.rs`** (new module): sidecar parser + classifier +
    three closers — zero-spine re-export, straight-line positional
    application, and FIX SYNTHESIS (match on scrutinee resolved through
    alias lets, arm patterns from projection-let accessor names +
    BranchTest variants, per-arm `have hdec := <termination VC at
    prefix args>` (term spine = post spine prefix!), IH = self `_closed`
    call, `termination_by` parsed from the term leaf with let
    substitution, `decreasing_by · exact (...).resolve_right (fun h =>
    h.2.elim)`). Referenced lets replayed as term-mode `let`s (no text
    substitution). Fixpoint driver in `build_link_module`; census via
    `PackageGateReport.discharge_detail`.
  - **Bound recipes**: interleaved application per the callee's leading-
    All order — `param:<n>` → caller's own `h_<n>_bound`, `lit` →
    `(by omega)`, `expr`-fed bounds = the only true wf-gap. This moved
    all 9 corollaries from misc bound-gap reasons to the single honest
    blocker "awaits wp_stm_sound_closed".
  - **State**: 53 closed (52 zero-spine + 1 fix = holds_all_append —
    generated text structurally identical to probe34's hand version),
    14 pending: 9× awaits wp_stm_sound, holds_all_close_each_e awaits
    cso_nil_true, and 4 wf-rung fns (holds_close_e, cso_nil_true,
    cso_cons_split via u_cso/u_close_e bounds; wp_stm_sound via
    u_wp_assert/u_esf_*). Gate green, tactus-core 138/0, vstd 1530/0.
  - **NEXT = the wf rung (R-b)**, the single gate to +14: per-datatype
    wf predicates (probe34 flWf shape, `termination_by structural`),
    `hwf` params on the 4 fns' clean stmts + destructuring in arms +
    components at expr-fed bound sites, wf PROPAGATION to callers
    (ref_wp_sound passes own param s → needs own StmWf s; its
    tmp__1 = seed_frame c arg needs a wf-transport lemma for
    seed_frame — the one semantic (non-mechanical) piece; consider
    emitting wf-preservation obligations OR scoping transport to
    constructor-built values first).

- (2026-07-17 pm, fable-b73) **WF RUNG (R-b) LANDED — 57 closed, all five
  scrutinee-matched fixes green.** Danielle's call: option (a), explicit
  and transparent. What landed:
  - **Wf predicate generation** (generate.rs): per scalar-carrying
    datatype (transitively computed from VIR field typs — the Lean
    model erases u64→Int, so bounds come from `type_bound_predicate`
    on the VIR side), probe34's flWf shape with `termination_by
    structural`, emitted dependencies-first into the Link namespace,
    only when referenced. Named + positional accessors (`Loop_cond_ann`,
    `val0`) both handled via krate field tables.
  - **hwf threading** (link_discharge.rs): clean stmts gain
    `(hwf : {Dt}Wf scrut)` / propagated `(hwf_p : ...)` binders;
    `match scrut, hwf with | pat, ⟨comps⟩ =>` destructuring; components
    discharge expr-fed bounds (`h_wf_<field>`) and feed the IH
    (`hwf_<field>`); `ClosedMeta.wf_params` propagates demands
    caller-ward through the fixpoint.
  - **Three debugging rounds, all census-guided**: (1) inner match
    discriminators arrive as left-nested `And(IsVariant, true)` chains
    (pattern-field tests) — branch_test_of now folds true-conjuncts +
    explicit Not; (2) `need_scrut_wf` false-positive on any-deref-arg
    dragged the whole RawExp closure in (incl. the RawExp/RawArmList/
    RawList MUTUAL family — cross-dt wf cycles stay census'd/SKIPPED,
    mutual wf blocks = future rung if demanded); fixed to wf-param-
    position-only; (3) `decreasing_by` bullets can't see arm-scoped
    term lets — transitive `expand_lets` inlining (probe34's shape).
  - **State: 57 closed (5 fix + 52 zero-spine), 10 pending** = 9×
    awaits wp_stm_sound + wp_stm_sound itself on ONE remaining class:
    **wf-transport for spec-fn results** (`tmp__3 := lib.ret_frame f rb`
    feeding holds_all_close_each_e's FrameListWf; also frame_append /
    loop-frame sites). Gate green, 138/0, vstd 1530/0.
  - **NEXT (final rung to 67/67): preservation-lemma synthesis** —
    `theorem ret_frame_wf : FrameListWf f → RetBindWf rb → FrameListWf
    (ret_frame f rb)` etc., proof = structural induction mirroring the
    spec fn's own match (VIR body analysis); NOTE the rec_1 gap (no
    equation lemmas for Box-recursing defs) — structural defs should
    iota-reduce on ctor scrutinees, but PROBE FIRST (hand-write
    ret_frame_wf against the current emission before mechanizing).

- (2026-07-18 am, fable-b73) **PROBE35 PASS (`e919c3f`, probe-w0/
  probe35_wf_preservation): wf-preservation archetype VALIDATED, first
  elaboration, ZERO axioms.** `frame_append_wf` (structural recursion
  through Box.deref — rec_1 territory) + `ret_frame_wf` (the actual
  wp_stm_sound demand site) both elaborate as pure terms: match-mirror
  + anonymous constructors + `termination_by structural`. No tactics,
  no equation lemmas — defeq iota whnfs through spec fn + wf pred +
  Box.mk/.deref. **Key insight: the proof term is ISOMORPHIC to the
  spec fn's own body** — ctor ↦ ⟨comps⟩, rec call ↦ rec lemma, spec-fn
  call ↦ its _wf lemma, let ↦ let, if ↦ dependent if. Synthesizer =
  defs-renderer walk emitting ⟨⟩-terms instead of values.
  Demand set for 67/67 (~12 lemmas, one archetype): ret_frame,
  frame_append, frame_after, loop_maintain_frame, loop_use_frame,
  havoc_lets, seed_params, binders_to_frame, seed_binders_hyp_bounds,
  binderprops_to_hyps, seed_frame (+ RetBindWf conjunct via StmData
  scrut component). NEXT = R-c: the preservation synthesizer in
  generate.rs over the same IR the defs renderer consumes.

- (2026-07-18, fable-b73) **PROBE36 FULL PASS (`b781b80`): every R-c
  emission shape validated, all axiom-free.** (1) mutual wf defs =
  per-def `termination_by structural x` INSIDE `mutual…end` (StmDataWf
  needs RawExpWf conjuncts → the mutual family is demanded, mutual-
  block emission replaces the census SKIP); (2) if-in-arm: rw[if_pos]
  FAILS on rec_1-blind goals → `(congrArg DWf (if_pos h)).mpr p` defeq
  transport; (3) nested match on 2nd wf scrutinee: plain; (4) non-
  recursive comps (loop_maintain_frame): `unfold` works (equation
  lemmas exist for non-rec defs) + by_cases + rw + composition;
  (5) bound hyps pass WHOLE (⟨h_x_bound, h_y_bound, trivial⟩).
  R-c = synthesizer over lean_ast::Expr (spec_fn_to_ast gives Def
  bodies): proof term isomorphic to body; Var→hyp/comp, Ctor→⟨⟩,
  spec-call→_wf lemma, self→rec, Match→match-mirror+destructure,
  If→dite+congrArg, Let→let+have. Lemma sigs: binders from Def +
  h_*_bound per u64 param + hwf_* per scalar-carrying-dt param.
  Caller side (link_discharge): resolve wf args by text — param→hwf,
  proj.deref→comp, `lib.g …`→g_wf application (top-level token split),
  ctor→⟨⟩; bounds→(by omega).
