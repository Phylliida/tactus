---
title: "W6 — stage B: deep expressions/types join the certificate"
status: in_progress
claimed_by: opus-b11
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T09:35:00Z
---

## Description

Deepen the mirror-type leaves from opaque ids to full expression/type syntax +
denotation, so the bridge now covers RENDERING — the class stage A explicitly
did not (trust-inventory row 3, the highest-value silent-unsoundness class).

Spec: `DESIGN-bootstrap.md` §5 (W6 row); `VERIFICATION-PATH.md` ladder rung 4.

- `Sst`/leaf mirror types gain expression + type constructors; the serializer
  promotes leaves from interned text to mirrored data (extends N3's leaf table
  into structure).
- Bridge equality now compares rendered expressions structurally — this is
  where the four leaf-renderer bugs of 2026-07-11 (and the cast/coercion class
  in `DECISION-cast-rendering.md`) would finally be CAUGHT by the certificate.
- The census (N4) ranked table is the coverage roadmap for which expression
  constructors to mirror first.

**Done when:** expression/type rendering is bridge-checked for the fixture +
a tgt slice; the cast-rendering class specifically is covered; a deliberately
mis-rendered leaf fails the bridge (mutation-kill at expression level).

**Blocked by:** bootstrap-09 (W4 pattern proven) + bootstrap-05 (N4 roadmap).

## Progress

- (2026-07-14, opus-b11) **Design + roadmap landed; fork resolved; ladder
  split into checkable sub-tasks.** Full detail in **`DESIGN-W6-stageB.md`**.
  Summary:
  - **Central fork RESOLVED = D2 (deepen-then-diff, Bridge-D), hybrid leaf.**
    The key realization, made explicit as a *construction fact*: stage-A leaf
    content is uncertified BY CONSTRUCTION — the serializer reuses production's
    own renderer so text byte-matches, so a rendering bug renders identically
    on both sides and the bridge silently passes. Corollary: **there is no
    cheap "just deepen the leaf" W6** — catching a renderer bug REQUIRES an
    independent second rendering (implementation diversity). Confirmed with the
    local model (127.0.0.1:8051): "if both sides call `to_lean_sst_expr`, you're
    only verifying the renderer is deterministic."
  - **Hybrid leaf** (mirror the structural cast/coerce/deref/binop DECISIONS;
    keep terminal atoms as interned `u64` string ids) chosen over full-depth —
    isolates the actual bug class (the *decision* to insert `Int.toNat`), not
    string pretty-printing. Local-model safety condition recorded: atoms MUST
    carry their interned id so a FORGOTTEN cast (`Atom(42)` vs
    `Cast(IntToNat, Atom(42))`) is caught by shape difference.
  - **Expression-level roadmap PRODUCED** (the thing N4 couldn't — it was
    statement-level). Enumerated all 164 distinct rendered leaves across the 10
    fixture certs → mapped to `lean_ast::ExprNode` (11 of 26 variants used).
    Tier 1 (cast class) = `BinOp`/`App`/`FieldProj`/`SpanMark`-wrapper, all
    present in the fixture (`sum_to`'s `Int.toNat r = lib.tri (Int.toNat n)`).
    Tier 2 = `If`/`Let`/`Tuple` (pure recursion). Atoms never deepen.
  - **The exact decision to reimplement** pinned to
    `DECISION-cast-rendering.md`: nat-typed arith `BinOp` operand →
    `Clip{Nat}` when `needs_nat_coercion(operand.typ, op.typ)`. The reference
    applies it uniformly from the type tag, so Friction-2 (inconsistent
    application) diverges → caught. Honest value statement: W6 catches
    *inconsistent application* of a coercion rule, not (alone) a rule both
    sides get wrong (monoculture, mitigated by W5).
  - **NO shared-crate edit this turn** — deliberately. `tactus-core` datatype
    churn invalidates the whole crate's verus-cache; the shape is settled +
    probe-de-risked (W6a) BEFORE the one clean W6b edit.
  - **Ladder split** into board sub-tasks W6a…W6e (see `DESIGN-W6-stageB.md`
    §5). **Next = W6a probe** (`bootstrap-20`): standalone `.lean`, hand-write
    `ExprData` + tiny `render_exp` for one cast-class expr, `decide` that a
    correct shape closes and a coercion-dropped shape FAILS. Zero risk to
    `tactus-core`.

- (2026-07-14, opus-b20) **W6a probe DONE & GREEN** (`bootstrap-20` → done).
  `probe-w0/probe12_w6a_castleaf/` proves the D2 mechanic end-to-end and freezes
  the W6b shape (`ExprData`/`TypData`/`RawExp`/`render_exp`). `lean` rc=0, axioms
  clean (pure kernel `decide`, no WellFounded/Classical), mutation-kills verified
  non-vacuous. Covered the verbatim `sum_to` leaf `Int.toNat r = lib.tri
  (Int.toNat n)` (Case A), the DERIVED arith Friction-2 case `(x as nat)*x` (Case
  B, the load-bearing diversity win), and the `.deref`/FieldProj class (Case C),
  each with a correct-closes + mutation-kill; plus a cmp negative control (D).
  **Next = W6b** (`bootstrap-12`?-no: needs a board file): land the frozen mirror
  types + `render_exp`/`render_typ` + sizes in `tactus-core/lib.rs` as one clean
  cache-churning edit; pick the `GoalData::Leaf(u64) → additive LeafE(ExprData)`
  migration (§6). W6b has no board file yet — create it when picking up.

- (2026-07-14, opus-b22) **W6b DONE** (`bootstrap-21` → done, commit `3f92ae9`).
  **W6c STARTED** (`bootstrap-22`, in_progress): the reference-side
  `ExpX → RawExp` transcription + `typ_data`/`binop_opcode` foundations landed
  in `source/lean_verify/src/sst_serialize.rs` (additive, census-gated,
  compile+test green; commit `cca5492`). Remaining W6c = the production-side
  `LExpr → ExprData` transcription, then W6d wires both into the obligation-leaf
  emit + bridge (`close`/emitter start producing `LeafE`). See `bootstrap-22`
  for the atom-id-consistency invariant and the deref/multi-arg open questions.

- (2026-07-14, opus-b22 cont.) **W6c DONE** (`bootstrap-22` → done). Landed the
  production-side `lexpr_to_exprdata` (`LExpr → lib.ExprData`) + the production
  half of the opcode table (`lean_binop_opcode`), completing BOTH W6c
  transcriptions. Additive/census-gated/`#[allow(dead_code)]` → verdict-neutral
  (`golden_add_capped_cert` byte-identical). 4 new tests green incl. the
  **`binop_opcode_alignment`** invariant test (ref `binop_opcode(op) ==` prod
  `lean_binop_opcode(binop_to_ast(op))` for every structural op — guards the
  bridge against a FALSE opcode divergence) and `lexpr_to_exprdata_case_a` (the
  verbatim `sum_to` leaf → the exact `expr_mirror_kernel_computes` shape). Full
  writeup + honest scope limits (type-args dropped both sides; Case-C deref
  ref-side still open; `TypeAnnot`/neg-lit census-deferred) in `bootstrap-22`.
  **Next = W6d** (`bootstrap-??`, needs a board file): wire both transcriptions
  into the obligation-leaf emit so `close`/the emitter produce `LeafE(ExprData)`
  and the bridge `decide`s `expr_eq` on live fixtures; the fixture census will
  surface any `ed-typeannot`/deref gaps to resolve there.

- (2026-07-14, opus-b23) **W6d opened as `bootstrap-23`** (board file created).
  Extracted the obligation-leaf coverage map for all 13 fixture certs from disk
  (the expression-level roadmap) and confirmed the symmetric-deepen architecture
  is forced (both sides must emit `LeafE`; local model concurs). Surfaced five
  gap classes — two the design docs missed (**G1** `True`/`False` bool literals,
  **G3** struct/tuple field projection) plus **G2** which CORRECTS the frozen
  W6b shape (the ref-side `.deref` is a DERIVED decoration-coercion, not the
  explicit `RawExp::Deref` node the W6a probe/`render_exp` assume — see
  `expr_shared.rs:1038-1051`). G4 (`max_u64` If-fallthrough `Let`-in-leaf)
  deferred to W6e. Full map + phased plan (W6d.0 SST-shape confirm → W6d.1
  shared-crate batch → W6d.2 wiring → W6d.3 bridge) in `bootstrap-23`.

- (2026-07-14, opus-b27) **W6d COMPLETE (`bootstrap-23`) — the deep bridge is
  LIVE end-to-end.** Rebuilt the binary + re-emitted all fixtures + probe9 green
  (12/13 close-ok DEEP, max_u64 hfail-ok/G4), verdict-neutral (flag-off ==
  flag-on), golden regenerated (338 tests), deep-mutation non-vacuity confirmed.
  `GoalData::LeafE(ExprData)` on both sides, `refWp` closing via
  `render_exp(RawExp)`, bridge `decide`s `expr_eq` — the Friction-2
  inconsistent-coercion class is caught at expression granularity across the
  whole coverable corpus (head_exec G2 deref, mk_point/swap_pair G3 field,
  add_capped G6 HasType, sum_to cast class). **Only remaining rung = W6e**
  (`bootstrap-24`, created this turn): the systematic expression-level
  mutation-kill (drop `Int.toNat`/`.deref`/accessor/width on the prod side ⟹
  bridge must FLIP) + G4 `If`/`Let`/`Not` fold-in (flips max_u64 to close-ok).
  This umbrella stays in_progress until W6e closes.

- (2026-07-14, opus-b30) **W6e COMPLETE (`bootstrap-24`) — the whole W6 ladder is
  correctness-closed.** G4 value-if-lift wired (`lift_if_raw` recompute +
  `lexpr_to_exprdata` Let/Not + deep_ids seeding from goal_shapes); max_u64
  flipped `hfail-ok → close-ok`, so **probe9 is 13/13 close-ok — no honest-fails
  remaining**. Validated 5 ways (probe9 both decide+rfl, probe13 4/4, probe14
  green, add_capped golden byte-identical, `cargo test -p lean_verify --lib`
  339/0); verdict-neutral (13v/11e unchanged). Two optional G4.3 hardenings
  (in-crate ref_wp guard + probe13 max_u64 mutation class) split to
  `bootstrap-25`. **The W6 ladder (W6a→W6e) is done** — the deep bridge covers
  the full coverable fixture corpus with every leaf a genuine symmetric deep
  compare. This umbrella can close (its only open child was W6e).

## Writeup

_when done: findings, how the code works, assumptions made. Parent design doc:
`DESIGN-W6-stageB.md`. Ladder: W6a (probe) → W6b (mirror types + reference
renderer, the shared-crate edit) → W6c (serializer transcriptions) → W6d
(bridge deepened, DONE `bootstrap-23`) → W6e (mutation-kill + Tier-2,
`bootstrap-24`)._
