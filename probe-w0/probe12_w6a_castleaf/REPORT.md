# W6a — cast-leaf probe (deepen-then-diff mechanic), board bootstrap-20

Validates the **D2 "deepen-then-diff"** mechanic (`DESIGN-W6-stageB.md` §2) on
cast-class expressions, standalone, with **zero risk to `tactus-core`**. Freezes
the `ExprData`/`TypData`/`render_exp` shape that W6b then lands in the shared
crate.

## What it proves

A hand-written, pure-core `.lean` (no Mathlib, no prelude, no tactus-core
oleans) with three mirror inductives + an **independent** reference renderer:

- `TypData` — `int` (uN → Lean `Int`) / `nat` (→ `Nat`) / `bool` / `named` /
  `ref`. The cast decision only needs `int` vs `nat`.
- `ExprData` — the **hybrid leaf**: structural `cast`/`binOp`/`app`/`fieldProj`/
  `spanMark` constructors + an `atom (id : Nat)` terminal that **carries its
  interned id** (the §2.1 safety condition — a forgotten cast `atom 1` vs
  `cast intToNat (atom 1)` is a shape difference).
- `RawExp` — the NEW independent input: the raw SST tree, type-tagged, NOT run
  through production's renderer. This is the implementation diversity D2 needs.
- `render_exp : RawExp → ExprData` — reimplements the coercion DECISION uniformly
  from the type tags via `needs_nat_coercion(operand, op) = (operand==int &&
  op==nat)`, at explicit-clip / arith-operand / call-arg sites. Plainly
  structural ⇒ the kernel reduces it under `decide`/`rfl`.

The bridge in each case: the CORRECT production `ExprData` **equals**
`render_exp(raw)` (closes by `decide` **and** `rfl`); the MUTATED shape is
**provably unequal** (`¬ (… = …)` by `decide`) — mutation-kill at the expression
level.

### Cases (each = correct-closes + mutation-kill)

| Case | Expression | Source of the cast | Mutation killed |
|---|---|---|---|
| **A** | `Int.toNat r = lib.tri (Int.toNat n)` — the **verbatim** `sum_to` fixture leaf (6/7/21) | explicit `as nat` clip (LHS) + call-arg cast (RHS), `==` is `bool`-typed | LHS `Int.toNat` **dropped** (Verus elides `r as nat` on a bare var — the exact Friction-2 shape) |
| **B** | `Int.toNat x * Int.toNat x` from `(x as nat) * x`, both inner clips **elided** | **DERIVED** by the reference from `Mul:nat` + `operand:int` — no explicit source cast to copy (the genuine diversity) | cast at ONE operand but not the identical other — Friction-2 **inconsistent application**, the documented core win |
| **C** | `lib.tree_head (t.deref)` on `t : &Tree` (head_exec, bootstrap-18) | explicit `deref` → `FieldProj` | `.deref` **dropped** (the pre-bootstrap-18 bug) |
| **D** | `x = (x as nat)` (`bool`-typed cmp) | negative control | — (LHS stays bare: pins that `needs_nat_coercion` fires only on `nat` targets, per DECISION §"Scope limits") |

Case B is the load-bearing one: because the reference **derives** the coercion
from type tags rather than copying an explicit source node, a production emitter
that applies the rule inconsistently diverges. This is the precise, honest value
statement of `DESIGN-W6-stageB.md` §3.1/§6: **W6 catches inconsistent
application of a coercion rule.**

## Results

- `lean probe12_w6a_castleaf.lean` → **rc=0**, ~1.2 s wall (mostly process
  startup; pure core, no imports). 11 `theorem`s: 3× correct-closes (`decide` +
  `rfl`), 3× mutation-kill, 1× negative control.
- `#print axioms render_exp` / `A_ok_decide` / `A_dropped_kill` /
  `B_inconsistent_kill` → **"does not depend on any axioms"**. No
  `WellFounded.fix`, no `Classical` — the mechanic is pure kernel computation,
  exactly as the stage-A mirrors require (`decide`-reducible in-crate).
- **Non-vacuity meta-check** (`run.sh`): asserting `¬(render_exp raw_sum_to =
  prod_sum_to_ok)` on the CORRECT shape **fails** (`decide` reports "the
  proposition is false", rc=1). So the `_kill` theorems test genuine inequality,
  not that `decide` rubber-stamps every negation.

## Assumptions / honesty

- **Monoculture caveat unchanged** (`DESIGN-W6-stageB.md` §6): the probe shows D2
  catches *inconsistent* application (Case B) and *dropped* casts (A, C). It does
  NOT (alone) catch a rule both sides get uniformly wrong — that is W5's job. The
  probe does not overclaim beyond this.
- **Case C (`.deref`) is modeled as an explicit source-deref transcription.** The
  real head_exec fix (bootstrap-18) derives the deref from the binder-aware ctx
  (param types). The probe validates the `FieldProj` constructor + dropped-deref
  shape-diff; the ctx-derived version is W6b's binder-aware `render_ctx`. Called
  out so W6b doesn't assume C's mechanic is the final deref path.
- **Atoms opaque by design** (§2.1): a bug purely inside atom-string
  pretty-printing (`lean_pp` mis-printing a correct AST) is row 5 / Bridge-R,
  NOT covered here. The hybrid leaf verifies the *decision tree*, not the string
  generator.
- The type tags on `RawExp` stand in for what W6c's raw-SST transcription will
  read off `vir::sst::ExpX`; the probe assumes those tags are available per node
  (they are — the SST carries `typ`).

## Reproduce

    LEAN=<lean-v4.25.0> bash probe-w0/probe12_w6a_castleaf/run.sh

## Hand-off to W6b

The `ExprData` / `TypData` / `RawExp` / `render_exp` shapes above are frozen.
W6b lands them (+ `expr_size`/`typ_size` structural measures,
`#[verifier::structural_decreases]`) in `tactus-core/lib.rs`, and decides the
`GoalData::Leaf(u64)` → additive `LeafE(ExprData)` migration (§6 leans additive
first). The probe is the shape spec; W6b is one clean cache-churning edit.
