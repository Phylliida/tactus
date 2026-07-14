---
title: "W6a — stage-B probe: deepen-then-diff mechanic on one cast-class expr (no shared-crate edit)"
status: done
claimed_by: opus-b20
created: 2026-07-14T00:35:00Z
updated: 2026-07-14T02:30:00Z
---

## Description

First rung of the W6 ladder (`bootstrap-11`; design in `DESIGN-W6-stageB.md`).
Validate the D2 deepen-then-diff mechanic end-to-end on ONE cast-class
expression with **zero risk to `tactus-core`** — a standalone Lean probe, in
the `probe-w0/` style.

Concretely, hand-write in a self-contained `.lean`:
- `ExprData` (hybrid leaf: `Cast`/`BinOp`/`App`/`FieldProj`/`SpanMark`-wrapper
  structural constructors + an `Atom (id : Nat)` terminal that carries its id)
  and a minimal `TypData` (`Int`/`Nat` is enough for the cast decision).
- A tiny reference `render_exp : RawExp → ExprData` that reimplements JUST the
  nat-arith operand `Clip{Nat}` decision (`needs_nat_coercion`) — see
  `DECISION-cast-rendering.md` "The fix that landed" and `DESIGN-W6-stageB.md`
  §3.1.
- Target expression: `sum_to`'s `Int.toNat r = lib.tri (Int.toNat n)` (or the
  simpler `(x as nat) * x` shape). Model the raw SST tree with type tags.
- Two `decide`s: (i) the CORRECT production-side `ExprData` equals
  `render_exp(raw)` → closes; (ii) a coercion-DROPPED production shape
  (`Atom r` where the reference has `Cast IntToNat (Atom r)`) → the `decide`
  equality is FALSE (mutation-kill at expression level).

**Done when:** the probe file `decide`s both directions (correct closes, dropped
fails) and is committed under `probe-w0/` with a short REPORT note. This freezes
the `ExprData`/`render_exp` shape that W6b then lands in `tactus-core`.

**Blocked by:** nothing (design is settled — `DESIGN-W6-stageB.md`).
**Blocks:** W6b (the shared-crate mirror-type + reference-renderer edit).

## Progress

- (2026-07-14, opus-b20) **DONE.** Standalone probe written + green:
  `probe-w0/probe12_w6a_castleaf/{probe12_w6a_castleaf.lean,run.sh,REPORT.md}`.
  Grounded the target in the real fixture: `sum_to`'s ensures `r as nat ==
  tri(n as nat)` renders leaf `Int.toNat r = lib.tri (Int.toNat n)` (verbatim
  cert leaf 6/7/21). `lean` rc=0, ~1.2 s, `#print axioms` clean (no
  WellFounded/Classical — pure kernel `decide`). Non-vacuity meta-check passes
  (decide refuses `¬(a=a)` on the correct shape). Details in Writeup.

## Writeup

**What landed.** A pure-core `.lean` (no Mathlib/prelude/oleans) that freezes the
W6b shape and proves the D2 deepen-then-diff mechanic end-to-end:

- **Mirror types:** `TypData` (int/nat/bool/named/ref), `ExprData` (hybrid leaf =
  structural cast/binOp/app/fieldProj/spanMark + `atom (id)` terminal carrying its
  interned id), `RawExp` (the NEW type-tagged raw-SST input).
- **`render_exp : RawExp → ExprData`** — the INDEPENDENT reference renderer.
  Reimplements the coercion decision uniformly from type tags:
  `needs_nat_coercion(operand, op) = (operand==int && op==nat)`, applied at
  explicit-clip, arith-operand, and call-arg sites. Structural recursion ⇒
  kernel-reducible under `decide`/`rfl`.

**How the bridge works.** Each case asserts, against the SAME `render_exp(raw)`:
(i) the CORRECT production `ExprData` is EQUAL (`decide` + `rfl` close), and (ii)
a MUTATED production `ExprData` is PROVABLY UNEQUAL (`¬ (…=…)` by `decide`). Since
`decide` cannot prove both `x=a` and `¬(x=a)`, elaborating both is the kill.

**Cases (all green):**
- **A** — the verbatim `sum_to` leaf `Int.toNat r = lib.tri (Int.toNat n)`
  (explicit `as nat` clip + call-arg cast under a `bool`-typed `==`). Kill: LHS
  `Int.toNat` dropped (the exact Friction-2 elision on a bare var).
- **B** *(load-bearing)* — `(x as nat) * x` with BOTH inner clips ELIDED, so the
  reference DERIVES both `Int.toNat`s from `Mul:nat` + `operand:int` (no explicit
  source cast to copy — real implementation diversity). Kill: cast at one operand
  but not the structurally-identical other = **inconsistent application**, the
  documented core win.
- **C** — `lib.tree_head (t.deref)` on `t : &Tree` (FieldProj). Kill: `.deref`
  dropped (the pre-bootstrap-18 head_exec bug).
- **D** — negative control: `x = (x as nat)` keeps LHS bare (pins that the coercion
  fires only on `nat` targets, not `bool` cmps — DECISION §"Scope limits").

**Verification evidence.** `lean` rc=0. `#print axioms render_exp / A_ok_decide /
A_dropped_kill / B_inconsistent_kill` → "does not depend on any axioms". `run.sh`
also runs a non-vacuity meta-check (asserting `¬(a=a)` on the correct shape FAILS,
rc=1) so the kills test genuine inequality.

**Assumptions / honesty (full list in REPORT.md):**
- Monoculture caveat unchanged — D2 catches *inconsistent* (B) + *dropped* (A,C)
  casts, NOT a rule both sides get uniformly wrong (that's W5). No overclaim.
- Case C models `.deref` as an explicit source-deref transcription; the real
  head_exec deref is ctx-derived (binder-aware `render_ctx`, bootstrap-18) — W6b's
  job, flagged so W6b doesn't treat C's mechanic as the final deref path.
- Atoms stay opaque by design: a pure atom-string mis-print (`lean_pp`) is row 5 /
  Bridge-R, not covered by the hybrid leaf.

**Hand-off:** shapes frozen. W6b lands `ExprData`/`TypData`/`RawExp`/`render_exp`
(+ `expr_size`/`typ_size`, `#[verifier::structural_decreases]`) in
`tactus-core/lib.rs` as ONE clean cache-churning edit, and picks the
`GoalData::Leaf(u64) → LeafE(ExprData)` additive migration (§6).
