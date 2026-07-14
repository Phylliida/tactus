---
title: "W7 — defs-layer certificate (spec-fn bodies + datatype/height emission)"
status: in_progress
claimed_by: opus-w7
created: 2026-07-13T19:38:00Z
updated: 2026-07-15T04:15:00Z
---

## Description

Extend the certificate pattern to the DEFINITIONS layer: serialize VIR spec-fn
bodies + datatype/height emission, recompute a reference definitional
translation, bridge. A wrong-but-consistent def translation is a model-drift
bug users cannot see — this closes the remaining half of trust-inventory row 4.

Spec: `DESIGN-bootstrap.md` §5 (W7 row) + §7 (beyond R2).

- Serialize spec-fn body VIR (the same discipline as the SST serializer, new
  input surface).
- Reference definitional translation authored in tactus-core; bridge the
  emitted spec-fn defs against it.
- Datatype + height-function emission similarly certified.

**Done when:** spec-world definitions are bridge-checked against the reference
translation for the fixture + a tgt slice; a perturbed def fails the bridge.

**Blocked by:** bootstrap-11 (W6 — reuse the stage-B expression machinery for
def bodies). **UNBLOCKED** — W6 done (`bootstrap-11` closed).

## Progress

- (2026-07-14, opus-w7) **Design landed + ladder split** — full spec in
  **`DESIGN-W7-defslayer.md`**. Claimed after closing the W6 umbrella. Key
  findings this turn (grounded in the code, not just the design doc):
  - **Central fork RESOLVED (same as W6d):** the reference `render_def` MUST be an
    *independent* second lowering of VIR-body→Lean-def (transcribe from VIR, NOT
    through production's `to_lean_sst_expr`/`to_lean_fn`), else the bridge only
    proves the renderer is deterministic, not faithful. Confirmed the pattern with
    the local model (sequencing sanity-check) — it endorsed pulling W7 while the
    W6 expression machinery is hot.
  - **Big reuse win:** a spec-fn *body* IS an expression, so W7 reuses the entire
    W6 stage-B core — `render_exp`, `lexpr_to_exprdata`, `expx_to_rawexp`, the
    opcode table, `expr_eq`, `TypData`. W7's new surface is just the def *header*,
    datatype decl, and height measure.
  - **The one real cost (discovered by reading `tactus-core/lib.rs:282/310`):**
    W6's `ExprData`/`RawExp` vocabulary is a STRICT SUBSET of what bodies need.
    Bodies add `Match` (the big one — inductive spec fns are match-bodied),
    quantifiers (`∀`/`∃`; GoalData::All is goal-level only), a first-class `Ite`
    (W6 G4 folded If→Let), and multi-arg `App` (W6 was single-arg, type-args
    dropped). Each is an additive `tactus-core` edit ⟹ base-hash change ⟹
    whole-crate re-verify + olean re-emit. **So W7 must batch ALL body-constructor
    deltas into ONE W7b edit** (the W6b discipline, bigger batch), and the W7a
    probe freezes that full vocabulary first.
  - **Row-4 kill:** these emitted defs/inductives/height-fns are trusted today;
    a wrong-but-*consistent* def lowering is invisible to obligation-level
    bridges. W7 is what closes it (trust-inventory row 4's remaining half).
  - **Ladder split** into `W7a…W7e` (design §6), mirroring W6a…e:
    - **W7a** (`bootstrap-26`, **DONE 2026-07-14, opus-w7a**) = standalone
      `.lean` probe (`probe-w0/probe15_w7a_defs/`), rc=0, axioms clean. Froze
      the full extended vocabulary (`TypData`+=`box`; `ExprData`+=`ite`/`matchE`/
      `appN`/`forallE`/`existsE`; `DefData`/`RawDef`/`DtData`/`CtorData` +
      `render_def`/`render_dt`) on `tri`(Ite) + `tree_head`/`sum_tree`(Match) +
      `Tree` datatype/`height`. Correct-closes (decide+rfl) + non-vacuous
      mutation-kills each; all four §7 open questions answered (verdicts in
      `probe15_w7a_defs/REPORT.md`); definition-level census recorded. **W7b is
      now UNBLOCKED — shapes frozen, safe to land the one batched edit.**
    - Key W7a de-risk for W7b: `mutual` inductive + `deriving instance
      DecidableEq`, and a `mutual` STRUCTURAL `render` recursing through the
      arm-list/expr-list, both reduce under `decide`/`rfl` with **no
      `WellFounded.fix`** (verified standalone). So the Rust mirror's
      `#[verifier::structural_decreases]` on the arm-list-recursive
      `render_exp`/`expr_size` is expected to hold — the Match/AppN nesting is
      kernel-reducible in-crate.
    - W7b (`bootstrap-27`, **DONE 2026-07-14, opus-w7b**) = the batched
      `tactus-core` edit. Landed all new constructors + `DefData`/`RawDef`/
      `DtData`/`RawDt` + `render_def`/`render_dt`/`def_eq`/`dt_eq` + two in-crate
      kernel-computes guards. Crate 65/0, oleans re-emitted, probe9/13/14 green
      (`aa4baed`+`fde32fb`). De-risk found 4 gotchas (mutual `structural_decreases`
      DOES work; inline arms to dodge the single-variant-enum `.height` bug;
      genuine mutual `arms_eq→expr_eq`; projection idiom, no nested match) — see
      `bootstrap-27` Progress/Writeup. Frozen `MatchArm`/`CtorData` named types
      folded into inlined list `Cons` (same info, no single-variant risk).
      **W7c now unblocked.**
    - W7c (`bootstrap-28`, **IN PROGRESS 2026-07-14, opus-w7c**) = serializer
      transcriptions (extend `lexpr_to_exprdata` + `raw_exp` for the new body
      constructors + datatype transcription; target the INLINED arm/ctor shape,
      not the frozen `MatchArm` type). **`Ite` increment LANDED** (both sides +
      3 tests, lib suite 342/0, verdict-neutral proven — the new `raw_exp` arm
      is unreachable on the current emit path, so no rebuild needed;
      `golden_add_capped_cert` byte-identical). Remaining: Match (needs VIR
      match-shape investigation), Forall/Exists, multi-arg AppN (+ the W7b-
      deferred per-arg coercion), datatype + def-header. See `bootstrap-28`.
    - W7d = wire into def emission + bridge `decide`s `def_eq` on fixture + tgt slice.
    - W7e = mutation-kill (perturb body / ctor / height ⟹ bridge flips 1→0).
  - **⚠ SURFACE-FORK correction (2026-07-14 opus-w7c-2, Danielle-endorsed):** def
    bodies live on the VIR `ExprX` surface (which KEEPS `Match`/`Quant`/multi-arg
    `Call`), NOT SST `ExpX` (where `Match` is desugared and the current `raw_exp`
    operates). Production emits def bodies from VIR via `spec_fn_to_ast →
    vir_expr_to_ast` (preserves `Match`). So the reference def-body transcriber
    is a NEW function on `vir::ast::Expr` (`raw_vir_exp`, split to `bootstrap-29`),
    NOT an SST-`raw_exp` extension — else `def_eq` compares desugared-`If` vs
    `Match` and never matches. DESIGN §3's "reuse `expx_to_rawexp`" is corrected
    to "reuse the RawExp target vocab + `typ_data`/`binop_opcode`, new VIR arms."
    The W7b `MatchR`/`RawArmList` vocab is thereby confirmed REACHABLE. Full
    finding + line refs in `bootstrap-28` Progress.

- (2026-07-15, opus-w7d-settle) **W7c + W7d DONE — the fixture rung of the
  "Done when" is met.** The def-body/-header/-datatype transcription landed on
  both sides (`bootstrap-28` production, `bootstrap-29` reference, both now
  `done`), W7b vocab is in-crate (`bootstrap-27`), and W7d (`bootstrap-33`)
  wired the live emit path + cross-validated it: a real
  `verus --lean-backend --tactus-emit-cert` run over `bootstrap-fixture` writes
  `tri`/`sq`/`tree_head` `.defcert` + `Tree` `.dtcert`, and each closes its
  `def_eq`/`dt_eq` bridge by `decide` against `tactus-core/out/lib`
  (`probe17_w7d_live`, re-run green this turn; lean_verify 366/0). One real
  transcriber gap (spec-fn bodies arrive wrapped in `Block([], Some(tail))`) was
  caught by the live path and fixed (empty-block peel + regression tests).
  - **Remaining rungs of THIS umbrella's "Done when":**
    1. **tgt-slice coverage** — bridge a real tgt-slice def, not just the
       fixture. The blocker is multi-arg `Call`/`AppN` (tgt spec fns call
       ≥2-arg helpers), which is deferred as **`bootstrap-34`** (the
       cache-churning per-arg-`TypData` `RawList` edit). **This is the ONLY
       remaining rung.**
    2. ~~perturbed def fails the bridge~~ — **DONE `bootstrap-35` (W7e)**:
       `probe19_w7e_kill` perturbs the emitted `_{def,dt}data` term at 6
       positions / 5 classes (body/opcode/arm-body/ctor-id/field-type) and every
       one flips the `def_eq`/`dt_eq` bridge 1→0; positives still close.
    3. ~~height-function emission~~ — **RESOLVED (W7e)**: no separate
       `Tree.height` cert is emitted (the Lean `.height` is auto-derived by
       `render_dt` from the datatype decl, not a transcribed production def), so
       there is nothing standalone to bridge. The ctors + field types that
       determine it ARE certified via the dtcert and W7e perturbs both. The
       card-title's "height emission" is thus subsumed by the datatype cert, not
       a separate obligation.
  - So the umbrella's tail is now a single rung: **`bootstrap-34` (multi-arg
    AppN) → tgt-slice `def_eq` coverage**. The fixture heart (transcription +
    live bridge + content-kill) is done and green.

## Writeup

_when done: findings, how the code works, assumptions made_
