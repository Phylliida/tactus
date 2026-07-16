# W6 — Stage B: expression/type rendering joins the certificate

**Status:** design + roadmap (opus-b11, 2026-07-14). Board task
`bootstrap-11`. Spec parent: `DESIGN-bootstrap.md` §5 (W6 row) + §2 row 3;
`VERIFICATION-PATH.md` ladder rung 4; `DECISION-cast-rendering.md` (the target
bug class).

This doc resolves the central W6 architectural fork, gives the
**expression-level coverage roadmap** grounded in the actual fixture cert
corpus (the thing N4/`bootstrap-05` could not produce — its census was
statement-level: `Call`/`assert-query`), and splits W6 into small checkable
board sub-tasks. It does **not** yet touch the shared `tactus-core` crate (that
churns the whole crate's verus-cache); the shape below is settled first, then a
probe validates it (W6a) before any shared-crate edit (W6b+).

---

## 1. The problem stage A leaves open (precisely)

Stage A (`bootstrap-06`/`07`, done) certifies goal **structure**: binder
telescopes, hypothesis sets and order, let-chains, obligation
multiplicity/order. Every expression/type **leaf** is an opaque `u64` id into a
side-table of production-**rendered** Lean text:

```
-- leaf 12: ⟦/- @rust:lib.rs:85:13 -/ r = x + y⟧
-- leaf 17: ⟦x + y⟧
-- leaf 2:  ⟦0 ≤ x ∧ x < 18446744073709551616⟧
```

**The gap, stated as a construction fact — not a mere TODO.** The serializer
renders those leaf strings by *reusing production's own renderer*
(`to_lean_sst_expr::sst_exp_to_ast_checked{,_with_ctx}`, ~5049 lines — §2 row 3)
so the text byte-matches the goal side and the ids cancel across the `decide`
bridge. This is deliberate and documented (`sst_serialize.rs` module doc: "leaf
content is uncertified … so it MUST reuse the production path to match"). The
consequence: **a rendering bug renders identically on both sides, so the bridge
silently passes.** The `as nat`→`Int.toNat` coercion inserted at one site but
not a structurally-identical site (`DECISION-cast-rendering.md` Friction 2) is
exactly this shape — well-typed, semantically wrong, invisible to a stage-A
cert.

**Corollary (the load-bearing design constraint).** There is **no cheap
"just deepen the leaf to structured data" version of W6.** If both the
production side and the reference side transcribe from the *same* production
`LExpr`, they agree by construction and catch nothing new — deepening only
verifies the renderer is deterministic. Catching a renderer bug requires an
**independent** second rendering, i.e. genuine implementation diversity.
(Confirmed with the local model, 2026-07-14: "If both sides call
`to_lean_sst_expr(expr)`, you aren't verifying the renderer; you are verifying
that the renderer is deterministic.")

---

## 2. The fork, resolved: D2 (deepen-then-diff), hybrid leaf

Two candidate mechanisms (both named in `DESIGN-bootstrap.md` §4.1/§5.3):

* **Bridge-R (denotation + `rfl`).** Reference produces `Prop`s via a
  type-indexed denotation; the emitted statement *is* the reference form; `rfl`
  ties production's rendered term to it. Endgame for a verified translator, but
  a large leap: needs a full type-theoretic denotation of the source language
  and a normalization strong enough to survive defeq between denote-unfoldings
  and rendered terms (`Int.toNat` materialization sites, decoration wrappers).
  **Deferred** — this is the W5/W8 direction, not W6's first wedge.

* **D2 (deepen-then-diff, Bridge-D).** Add `ExprData`/`TypData` mirror
  inductives. The serializer transcribes production's rendered `LExpr` →
  `ExprData` for the **production** side (boring, 1:1, stays in TCB). The
  **reference** side gets a NEW input — the *raw* SST expression tree mirrored
  to data, type-annotated — and an independently-authored
  `render_exp : RawExp → ExprData` (tactus spec fns) that **reimplements the
  coercion/cast/deref-insertion decisions**. The bridge `decide`s
  `productionExprData == render_exp(rawExprMirror)`. **The reimplemented rules
  ARE the diversity.** This is a *structural* verification of the
  transformation: it turns "did we print the right string?" into "did we make
  the right structural decision about the type system?" — which is exactly
  where the unsoundness lives.

**Decision: W6 lands D2 first**, scoped to the cast/coercion class (the
highest-value row-3 subclass, `DECISION-cast-rendering.md`). Bridge-R stays the
named endgame.

### 2.1 Hybrid leaf (the first-increment scope)

`ExprData` mirrors the **structural decisions** (Cast/Coerce, Deref, FieldProj,
BinOp, UnOp, App, If, Let, Tuple, SpanMark) but bottoms out at **terminal
atoms** (variable reads, literals, spec-fn/type names) that stay **interned
`u64` string ids**, exactly as today. Rationale (endorsed by the local model as
strictly better than full-depth for the first increment):

* **Isolates the actual bug class.** The cast bugs are in the *decision* to
  insert an `Int.toNat` node, not in the string `"x"`. Mirroring structure while
  keeping atoms opaque verifies the **decision tree**, not the string generator.
* **TCB / proof-burden minimization.** `render_exp` never has to know how a
  `VarIdent` pretty-prints (`SST_Var(id) → "x_42"`); it only encodes the *logic*
  of where a coercion goes. Full-depth would spend ~80% of the effort mirroring
  atom-name pretty-printing for ~0 added security (a swapped-variable bug is
  catastrophic and Lean-type-errors immediately; the cast bugs are the insidious
  well-typed ones).
* **Safety condition (from the local model — must hold).** The atom leaf in
  `ExprData` MUST carry its interned `u64` id, so a *forgotten* cast is caught by
  the shape difference:
  `Production: Atom(42)` vs `Reference: Cast(IntToNat, Atom(42))` → `decide`
  fails. If atoms were structureless the forgotten-cast case could collapse.

**Honest limitation of the hybrid leaf.** A cast bug tied to the *string
identity* of an atom (a specific constant that triggers a special-case
coercion) is only caught if that atom's distinguishing id reaches `ExprData` —
which it does, since atoms carry their interned id. A bug purely inside
atom-string pretty-printing (`lean_pp` mis-printing a correct atom) is NOT
covered by the hybrid leaf; that is row 5, left to Bridge-R/W8, and is a
mis-print-a-correct-AST class (much narrower than row 3's decision logic).

---

## 3. Expression-level coverage roadmap (grounded in the fixture corpus)

N4 (`bootstrap-05`) established the fixture family — not tgt (9 exec fns) — is
the real serializer stress corpus. Enumerating **every rendered leaf across all
10 fixture certs** (`grep '^-- leaf' bootstrap-fixture/out/lib/cert/*.cert.lean`,
164 distinct) gives the concrete constructor set W6 must mirror. Mapped to
`lean_ast::ExprNode` (26 variants total; the fixture exercises ~11):

| ExprNode | Appears as (fixture leaves) | Cast-class relevance | Tier |
|---|---|---|---|
| `Var` | `x`, `acc`, `tmp__1`, `_h_ctx_0`, `_tactus_d_old_0_0`, `decrease_init0` | atom (opaque) | atom |
| `Lit` | `0`, `1`, `36`, `1000`, `18446744073709551616` | atom (opaque) | atom |
| `LitBool` | `True`, `False` | atom | atom |
| `BinOp` | `+ - * /`, `< ≤ ≥ = ≠`, `∧ ∨ →` | **operand coercion site** (arith result-typ decides `Clip`) | **1** |
| `UnOp` | `¬` | pass-through | 1 |
| `App` | `Int.toNat n`, `Int.ofNat 0`, `lib.tri (…)`, `lib.tree_head t`, `lib.Point.mk a b` | **`Int.toNat`/`Int.ofNat` = the coercion nodes**; also call-arg coercion | **1** |
| `FieldProj` | `p.x`, `r.1`, `r.2`, `t.deref`, `tmp__.deref.isLeaf`, `.Leaf_val0` | **`.deref` insertion** (`&`-param / Ref coerce) | **1** |
| `If` | `if x < y then y else x` | recursion into arms | 2 |
| `Let` | `let m := …; m`, nested | recursion into body | 2 |
| `Tuple` | `(b, a)` | recursion into elems | 2 |
| `SpanMark` | `/- @rust:loc -/ <e>` obligation annotations | wrapper, pass-through inner | 1 (wrapper) |

**Types** (`typ_leaf` slots): `Int` (uN), `Nat` (nat), `Type` (kind), type-var
`T`, `Tactus.Ref lib.Tree` (Ref wrapper), user datatypes (`lib.Point`,
`lib.Tree`). A `TypData` mirror needs only: a small closed set of base tags
(`Int`/`Nat`/`Bool`/`Type`), a `Ref` wrapper, and a `Named(id)` catch-all for
user/param types. The cast decision (`needs_nat_coercion(operand.typ, op.typ)`)
only needs the `Int` vs `Nat` distinction — so `TypData` can be *very* small at
first and still cover the cast class.

**The cast-class constructors are Tier 1** (`BinOp`, `App`, `FieldProj`,
`SpanMark`-wrapper), and they appear directly in the fixture — e.g. `sum_to`'s
`Int.toNat r = lib.tri (Int.toNat n)` and `tri`'s bound leaves. Tier 2
(`If`/`Let`/`Tuple`) is pure structural recursion with no new cast decision;
fold in second. Atoms never need deepening at stage B.

### 3.1 The exact decision to reimplement (first increment)

Per `DECISION-cast-rendering.md` "The fix that landed": at a **nat-typed arith
`BinOp`**, each operand whose type renders `Int` (a uN) but whose enclosing op
result renders `Nat` is wrapped in `Clip{Nat}` (→ `Int.toNat`). The predicate is
`needs_nat_coercion(operand.typ, op_result.typ)`; the same predicate governs the
call-arg path. So the reference `render_exp`, given each SST node's mirrored
`typ`, independently decides `Cast(IntToNat, ·)` placement. A production emitter
that inserts it inconsistently (Friction 2) diverges from the uniform reference
→ bridge fails. **This is the precise, honest value statement:** W6 catches
*inconsistent application* of a coercion rule (the actual Friction-2 class),
because the reference applies it uniformly from the type annotation.

---

## 4. Pieces (what changes where)

1. **`tactus-core/lib.rs` (shared — W6b):** add `ExprData` + `TypData`
   inductives + structural `expr_size`/`typ_size` + (Tier-1) the reference
   `render_exp`/`render_typ` spec fns. `#[verifier::structural_decreases]`
   throughout (kernel-compute discipline, same as the stage-A mirrors). The
   existing `GoalData::Leaf(u64)` becomes `GoalData::Leaf(ExprData)` OR a new
   `GoalData::LeafE(ExprData)` is introduced (shape TBD in W6b — the former is
   cleaner but touches every stage-A cert; the latter is incremental). **This is
   the churn-the-cache edit; do it once, after the probe.**
2. **New serializer input (W6c):** the *raw* SST `Exp` tree, mirrored to
   `RawExp` data with per-node `typ` tags — NOT rendered through
   `to_lean_sst_expr`. Boring 1:1 transcription of `vir::sst::ExpX` (the new TCB
   line item; small).
3. **Production-side transcription (W6c):** `LExpr → ExprData` for the emitted
   goal leaves (recognize Cast/Deref/FieldProj/BinOp/UnOp/App/SpanMark; atoms →
   interned id). Boring, TCB.
4. **Bridge (W6d):** `decide productionGoals == refWp(..)` now compares deep
   `ExprData` leaves; the reference goal leaves come from
   `render_exp(rawExprMirror)`.
5. **Acceptance (W6e):** a deliberately mis-rendered leaf (drop the coercion at
   one site on the production side) flips the bridge — mutation-kill at
   expression level, the W6 analog of `bootstrap-07`'s statement-level kill.

---

## 5. Board sub-task ladder (probe-first, each independently checkable)

* **W6a — probe (no shared-crate edit).** Standalone `.lean` (probe-w0 style):
  hand-write `ExprData`/`TypData` + a tiny `render_exp` for ONE cast-class
  expression (`Int.toNat r = lib.tri (Int.toNat n)` from `sum_to`), and a
  `decide` that (i) production-shape == reference-shape closes, and (ii) a
  coercion-dropped production shape FAILS. Validates the mechanic end-to-end with
  zero risk to `tactus-core`. **This is the next task.**
* **W6b — mirror types + reference renderer in `tactus-core`.** Land
  `ExprData`/`TypData` + `render_exp`/`render_typ` (Tier 1) + sizes; verify
  crate kernel-computes (in-crate `decide` guard like
  `skeleton_kernel_computes`). Decide the `GoalData::Leaf` shape migration.
* **W6c — serializer raw-expr transcription + production LExpr→ExprData.** Both
  boring TCB transcriptions; census-gated fail-loud on un-mirrored constructors.
* **W6d — bridge deepened; fixture closes.** Cast-class fixtures bridge with
  deep leaves; verdict-neutral (flag on == off).
* **W6e — mutation-kill acceptance + Tier-2 fold-in (If/Let/Tuple).**

---

## 6. Risks / honesty

* **Monoculture.** The reference `render_exp` could reimplement the *same*
  coercion rule the same wrong way, missing a bug both share. Mitigated exactly
  as the design says: the reference is structural/first-order, reviewed as spec,
  and W5's soundness proof re-anchors it to an operational semantics. What D2
  DOES robustly catch is *inconsistent application* (Friction 2) — the reference
  applies the rule uniformly from the type tag, so a site where production forgot
  it diverges. That is the documented, load-bearing win; do not overclaim
  beyond it.
* **Cache churn.** W6b touches shared `tactus-core` datatypes → invalidates the
  crate's verus-cache once (base-hash change). Batch all `tactus-core` shape
  edits into W6b; the probe (W6a) de-risks the shape first so W6b is one clean
  edit, not a churn loop.
* **`GoalData::Leaf` migration blast radius.** Changing `Leaf(u64)` →
  `Leaf(ExprData)` re-touches every stage-A cert + every refWp arm that emits a
  leaf. A `LeafE` additive variant avoids that but leaves two leaf kinds. W6b
  picks; lean toward the additive variant first (smaller diff, reversible),
  unify later.
