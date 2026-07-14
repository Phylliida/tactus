---
title: "W6b — land the frozen ExprData/TypData/render_exp mirror types in tactus-core (the one cache-churning edit)"
status: done
claimed_by: opus-b21
created: 2026-07-14T02:40:00Z
updated: 2026-07-14T03:55:00Z
---

## Description

Second rung of the W6 ladder (`bootstrap-11`; design `DESIGN-W6-stageB.md` §4/§5;
shape frozen by the W6a probe `bootstrap-20`).

Land the shapes the probe froze into the shared crate, as **one clean edit**
(datatype churn invalidates the whole crate's verus-cache once — batch it):

- Add `ExprData` + `TypData` (+ `CastKind`) inductives to `tactus-core/lib.rs`,
  mirroring `probe-w0/probe12_w6a_castleaf/probe12_w6a_castleaf.lean` verbatim
  (hybrid leaf: structural cast/binOp/app/fieldProj/spanMark + `atom(id)`
  terminal carrying its interned id).
- Add structural `expr_size` / `typ_size` measures +
  `#[verifier::structural_decreases]` throughout (kernel-compute discipline,
  same as the stage-A mirrors).
- Add the Tier-1 reference `render_exp` / `render_typ` spec fns implementing
  `needs_nat_coercion` at explicit-clip / arith-operand / call-arg sites (the
  probe's `render_exp`).
- **Decide the `GoalData::Leaf` migration.** §6 leans **additive** first: add a
  `LeafE(ExprData)` variant rather than changing `Leaf(u64)` → `Leaf(ExprData)`
  (smaller diff, reversible, avoids re-touching every stage-A cert + refWp arm).
- Verify the crate kernel-computes: in-crate `decide` guard analogous to
  `skeleton_kernel_computes` (so the deep leaves stay `decide`-reducible on the
  bridge, as the probe's `#print axioms` confirmed for the standalone shapes).

**Done when:** `tactus-core` verifies with the new types + `render_exp`, an
in-crate `decide` guard confirms kernel-computation, and the crate's e2e/gate is
green (verdict-neutral — the new types are additive, not yet wired into the
bridge; that's W6c/W6d).

**Blocked by:** nothing (W6a done — shape frozen).
**Blocks:** W6c (serializer raw-expr transcription + production LExpr→ExprData),
W6d (bridge deepened).

## Progress

- (2026-07-14, opus-b21) **DONE.** Landed the frozen W6a shapes into
  `tactus-core/lib.rs` as one batched cache-churning edit; canonical
  `--lean-backend --lean-all-proofs` gate is **50 verified, 0 errors**,
  package gate reports "composition + axiom closures kernel-verified".
  One real bug surfaced+fixed mid-run (Lean builtin name collision — see
  Writeup). Committed `3f92ae9`.

## Writeup

**What landed** (`tactus-core/lib.rs`, commit `3f92ae9`). The stage-B
expression vocabulary the W6a probe froze, ported verbatim from
`probe-w0/probe12_w6a_castleaf/probe12_w6a_castleaf.lean` into the shared
crate, as ONE edit (datatype churn invalidates the crate's verus-cache once):

- **Datatypes** (placed before `GoalData`, one-way nesting only):
  `TypData` (flat: `TyInt`/`TyNat`/`TyBool`/`TyNamed(u64)`/`TyRef(u64)`),
  `CastKind` (`IntToNat`/`NatToInt`), `ExprData` (the hybrid leaf:
  `Atom(u64)`/`Lit(int)` terminals + structural `Cast`/`BinOp`/`App`/
  `FieldProj`/`SpanMark`), and `RawExp` (the NEW type-tagged raw-SST input).
  Recursive fields use `Box<…>` (Rust indirection), matching the crate's
  existing `LeafList`/`GoalData` style.
- **Measures**: `expr_size` (`#[verifier::structural_decreases]`, `decreases
  e`) and `typ_size` (non-recursive → no structural_decreases; the match just
  documents the variant set).
- **Reference renderer** (Tier-1): `type_of` + `deref_type` (the type
  projection; `Deref` factored into `deref_type` to dodge the nested-match
  flattening caveat, like `ret_frame`), `needs_nat_coercion` (nat-returning
  predicate — bool would lower to a noncomputable Prop, finding-5),
  `coerce_if`, `deref_field`, and `render_exp`
  (`#[verifier::structural_decreases]`) — the INDEPENDENT reimplementation
  that re-derives the `as nat` coercion uniformly from type tags at
  explicit-clip / arith-operand / call-arg sites.
- **Structural equality** for the bridge: `ck_tag`/`castkind_eq`, `ed_tag` +
  13 non-recursive `ed_*` projection accessors, and `expr_eq`
  (`#[verifier::structural_decreases]`), all following `goal_eq`'s discipline
  (match the FIRST arg alone, read the second through tag+projection, every
  arm body a chain of `if`s — never a nested match).

**GoalData::Leaf migration decision — ADDITIVE (§6 additive-first).** Added a
new `GoalData::LeafE(ExprData)` variant rather than changing `Leaf(u64)`.
Wired it through every fn that matches `GoalData` exhaustively: `goal_size`
(`LeafE(_) => 1`, one spine node like `Leaf`), `gd_tag` (`=> 4`), `gd_child`
(`LeafE(e) => LeafE(e)`, self — never recursed), new accessor `gd_leafe_expr`,
and `goal_eq`'s `LeafE(e1)` arm dispatching to `expr_eq`. The `gd_*` scalar
accessors already had `_ => 0` wildcards, so they needed no change. Because
`close` still produces `Leaf(u64)`, **refWp never emits `LeafE`** — the change
is verdict-neutral; W6c wires the serializer to transcribe raw SST exprs and
emit `LeafE`. `goal_eq`'s `decreases a` is preserved: the `LeafE` arm makes no
recursive `goal_eq` call (it delegates to the separate `expr_eq` recursion).

**Kernel-computation guards** (the in-crate `decide` proof, analogous to
`skeleton_kernel_computes`):
- `expr_mirror_kernel_computes` — ports probe Cases A/B/C + the D negative
  control against the LANDED `render_exp`/`expr_eq`: each correct shape
  `expr_eq(render_exp(raw), prod_ok) == 1` and each mutation
  `… == 0`. Case B (the load-bearing one) DERIVES both `Int.toNat`s from a
  `TyNat`-typed `Mul` with two bare `TyInt` operands (no source cast to copy),
  so the one-operand-only mutation is caught. Also exercises `Lit(int)`
  equality and the size measures under `decide`.
- `leafe_goal_bridge_kernel_computes` — the additive `LeafE` variant threads
  `goal_eq`/`goals_eq`/`goal_size`; LeafE-vs-`Leaf` is a tag mismatch either
  direction.

**The one real bug (fixed mid-run).** First `--lean-backend` run failed:
`TactusDefs_lib__base.lean … type expected, got (Nat : TypData)`. The tactus
Lean backend renders a nullary constructor as `(Name : EnumType)`, so bare
`TypData::Int`/`Nat`/`Bool` resolved to Lean's builtin `Int`/`Nat`/`Bool`
types instead of the constructors. Fixed by `Ty`-prefixing all five `TypData`
variants (the other enums' variant names — `Atom`/`Cast`/`App`/`Var`/`Clip`/…
— have no Lean-Init collision, and re-ran clean). Worth flagging for W6c: any
future mirror-type variant must avoid Lean-Init type names.

**Verification evidence.** `TACTUS_LEAN_OUT=$PWD/out
../source/target-verus/release/verus --crate-type=lib --lean-backend
--lean-all-proofs lib.rs` → **50 verified, 0 errors**; "44 modules elaborated
… composition + axiom closures kernel-verified" (the emitted defs
kernel-compute with a clean axiom closure — no `WellFounded.fix`/`Classical`,
exactly as the stage-A mirrors require). All pre-existing fixture bridges
(`ref_wp_sum_to_loop`, `add_capped`, `count_down`, `call_pass_through`,
nested-loop, if-fallthrough) re-verified after the datatype churn.

**Assumptions / honesty.**
- **`render_typ` is served by `type_of`, not a separate renderer.** The frozen
  probe's `RawExp` carries `TypData` tags directly per node, so there is no
  raw-type TREE to render; `type_of` reads the pre-tagged type off each node
  (and `deref_type` resolves `&T`). A standalone `render_typ : RawTyp →
  TypData` only becomes meaningful in W6c when the serializer transcribes raw
  SST *types* — deferred there, faithful to the probe.
- **Verdict-neutral, NOT yet wired.** `close`/refWp still emit `Leaf(u64)`;
  nothing downstream references the new types (grep-confirmed: only
  `tactus-core/lib.rs`; `bootstrap-fixture` doesn't import tactus-core; the
  `to_lean_expr.rs` hit was `render_expr_with_derefs`, production's own
  renderer, a coincidental substring). So the W3 differential gate over tgt is
  unaffected by construction — I verified the crate gate (which includes every
  fixture bridge) but did NOT re-run the full tgt-scale W3 sweep (no runner in
  the bootstrap dir; the additivity argument is airtight: refWp output
  unchanged, `goal_eq`'s `LeafE` arm unreachable).
- **Case C `.deref` still modeled as explicit source-deref** (as in the
  probe); the real head_exec deref is ctx-derived (binder-aware `render_ctx`,
  bootstrap-18) — W6c's job.
- **`Lit(int)` decides.** Confirmed `int`-valued literals kernel-compute under
  `decide` in the tactus backend (the `expr_eq(Lit 5, Lit 5)` guard), so the
  frozen `Int` literal field is sound in the Verus mirror.

**Hand-off to W6c** (unblocked): serializer raw-expr transcription
(`vir::sst::ExpX` → `RawExp`, reading the per-node `typ` for the tags) + the
production `LExpr` → `ExprData` transcription, then `close`/the emitter start
producing `LeafE` and the bridge deepens (W6d).
