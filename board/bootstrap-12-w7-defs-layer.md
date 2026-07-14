---
title: "W7 — defs-layer certificate (spec-fn bodies + datatype/height emission)"
status: in_progress
claimed_by: opus-w7
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T21:40:00Z
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
    - W7c = serializer transcriptions (extend `lexpr_to_exprdata`/`expx_to_rawexp`
      for the new body constructors + datatype transcription; target the INLINED
      arm/ctor shape, not the frozen `MatchArm` type).
    - W7d = wire into def emission + bridge `decide`s `def_eq` on fixture + tgt slice.
    - W7e = mutation-kill (perturb body / ctor / height ⟹ bridge flips 1→0).

## Writeup

_when done: findings, how the code works, assumptions made_
