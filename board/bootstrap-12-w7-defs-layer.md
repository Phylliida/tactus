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
    - **W7a** (`bootstrap-26`, created) = standalone `.lean` probe, freeze the
      extended vocabulary on a `tri`-style match-bodied def + the `Tree` datatype,
      correct-closes + body-mutation-kill, produce the definition-level census.
      Zero shared-crate risk. **This is the next pickup.**
    - W7b = the one batched `tactus-core` edit (new constructors + `DefData`/
      `RawDef`/`DtData` + `render_def`/`def_eq`).
    - W7c = serializer transcriptions (extend `lexpr_to_exprdata`/`expx_to_rawexp`
      + datatype transcription).
    - W7d = wire into def emission + bridge `decide`s `def_eq` on fixture + tgt slice.
    - W7e = mutation-kill (perturb body / ctor / height ⟹ bridge flips 1→0).

## Writeup

_when done: findings, how the code works, assumptions made_
