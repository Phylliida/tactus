# Typed renderer graduation — survey & plan (2026-07-03)

The "Exhibit B full fix" (REVIEW-2026-07-02 § 2.1): make rendering
return `(expr, typ)` everywhere so the invariant **rendered type ==
claimed type** is structural instead of per-site discipline. Survey
written before any code moves, same pattern as REFACTORING2/CRATEDEFS.

## The invariant and its bug family

Every composition site (call arg, let binding, projection, binder
bound, substitution) assumes the rendered value's Lean type matches
the VIR typ the site reads off the AST. Two dimensions break:

* **Wrapper depth** (`Tactus.Ref`/`Box`/… chains) — U2, B1, #95,
  #144–146, the three 2026-05 SST clusters, β refactor, and cluster
  bug 5 (tuple slots keep decorations the SST strips from projection
  results).
* **Numeric sort** (ℤ vs ℕ) — Exhibit B (2026-07-03): #128
  ret-substitution bound an ℤ-valued E into ℕ arithmetic; the fix
  needed a VIR-side *shadow walk* purely to recover E's type, because
  a rendered `LExpr` cannot answer "what sort am I".

Each member costs roughly a session, the family has never stopped
producing, and both of this week's members were found in code that had
been "done" for weeks. That's the definition of structural debt.

## What already exists (the head start is real)

* `typed_expr.rs` (191 lines): `TypedExpr { inner: Expr, typ: Typ }`,
  smart ctors, `into_slot` — the **currency decision (VIR `Typ`) is
  already made and DESIGN'd**, with rejected alternatives recorded
  (full elaborator, phantom typing, `Coe` delegation). Adoption: 4
  sites (stalled Phase 2).
* Render-time **value substitution is already typed** —
  `RenderSubst` carries `(LExpr, Typ)` pairs; `lookup_subst` bridges
  to the slot typ. The untyped stragglers are the POST-render
  substitutions (`typ_subst` name swaps — safe; `ret_subst` — Exhibit
  B's blind spot).
* `RenderCtx` threading (2.A) means ctx already reaches every arm —
  the migration has a substrate.
* The bridge primitives exist separately: `coerce_lexpr` (wrapper
  depth, longest-common-suffix wrap reconciliation, passthrough on
  match) and `apply_clip_coercion` (ℤ↔ℕ via `Int.toNat`/`Int.ofNat`).

## What's missing

1. `coerce_lexpr` doesn't know about numeric sorts — the two bridge
   dimensions live in different functions consulted at different
   sites.
2. The renderers return bare `ExprNode`/`LExpr`; actual-typ knowledge
   is recomputed (or guessed from claimed typs) at consumption sites
   via helper family: `sst_lean_wrap_count`, `tuple_slot_extra_derefs`,
   `render_expr_with_derefs`, `caller_arg_actual_typ`,
   `vir_ret_eq_rhs_typ` — each one a monument to a bug.
3. No stated per-node-class rule for what the ACTUAL typ of a rendered
   node is when it differs from the claimed typ (tuple projections,
   substituted values, clip results, call results at instantiated
   typs).

## Design decisions

**Settled (inherited from typed_expr.rs, don't reopen):** currency =
VIR `Typ`; trust-at-construction (no elaborator); goal/Prop layer
stays untyped (obligations are Props — sorts don't apply above the
value level).

**D1 — one bridge.** Extend `coerce_lexpr(value, actual, slot)` to
reconcile BOTH dimensions: wrap-depth (existing) then numeric sort
(fold in `apply_clip_coercion` keyed on `renders_as_lean_int` of the
peeled typs). Passthrough guarantee: when actual == slot in both
dimensions, output is byte-identical to today — this is what keeps
goal-shape churn near zero during migration.

**D3 — trust classification (discovered during P1, 2026-07-03).**
Claimed typs LIE in places beyond the known projection cases: VIR's
poly-boxing claims wrapper-decorated typs at Var uses whose bound
value is bare (`Box::new` ctor lowering: `Unbox(tmp : Box<u8>) : u8`
with `tmp` bound to the bare inner value). The old renderer's
claimed-typ contract silently CANCELED such lies; an actual-typ spine
that naively propagates them ACTS on them. Rule: an actual typ
propagates through typ-shifting transparent nodes (Box/Unbox) only
when it comes from a TRUSTED source — binder lookup, render-time
substitution, tuple-slot rule, Clip — otherwise reset to the claimed
contract (`actual_is_trusted`, mirroring `sst_lean_wrap_count`'s old
trust-binders-distrust-claims semantics). P2's WP let-binder typ
environment (binder typs recorded from the RHS's rendered actual, not
the declared SST typ) extends the trusted set and lifts the resets.
P3 must apply the same classification on the VIR side.

**D2 — actual-typ table.** Write the per-node rule as part of Phase 1
and pin it in the module doc. The interesting rows (everything else is
"claimed typ is correct"):

| node | actual typ |
|---|---|
| tuple `Field` projection | the base tuple's SLOT typ (keeps decorations the claimed typ strips) — cluster bug 5's rule, generalized |
| substituted `Var` | the substituted value's typ (already so at render-time; extends to post-render) |
| `Clip` | the DEST range's typ (already correct) |
| call result | callee ret typ instantiated with call typ args (`fn_param_typs`-style subst, ret-side) |
| `#128` dest binding | E's typ from the eq conjunct — carried on the typed tree, killing the shadow walk |

## Phases (each gated on full e2e + units, committed separately)

**P0 — unify the bridge (~½ session).** D1. `TypedExpr::into_slot`
then covers both dimensions. Add shape pins for the sort dimension
(usize/nat/int × wrapper × slot direction). Deletes nothing yet;
enables everything.

**P1 — SST renderer typed spine (~1 session).** New internal entry
`exp_to_typed(e, ctx) -> TypedExpr`; unmigrated arms wrap the old
render with the CLAIMED typ (today's semantics, bit-for-bit). Migrate
the high-risk arm clusters to return ACTUAL typs per D2: projections
(Field/IsVariant — **retires `tuple_slot_extra_derefs` and most
`sst_lean_wrap_count` consultation**), call args/results, Clip. Each
claimed≠actual divergence found during migration is a latent bug —
the migration doubles as the family's terminal bug-hunt.

**P2 — SST consumers (~1 session).** The centerpiece is the **WP
let-binder typ environment**: `walk_let` records each let-bound temp
at its RHS's rendered ACTUAL typ in an owned, evolving binder env
(today `binder_typs` is a borrowed, params-only map) — this extends
the D3 trusted set to let-bound temps and lifts the Box/Unbox resets.
Plus: ctor fields and binder bounds consume `TypedExpr` via
`into_slot`. (`vir_ret_eq_rhs_typ` retirement moved to P3 — the
ensures extraction walks the VIR-rendered tree, so it needs the VIR
renderer typed, not the SST consumers.)

**P3 — VIR renderer (~1–2 sessions).** Same treatment for
`to_lean_expr` (goals/clauses/instance bodies), applying the same D3
trust classification — **retires `render_expr_with_derefs` AND
`vir_ret_eq_rhs_typ`** (the ensures eq-extraction then walks a typed
tree that knows E's sort), and the remaining `RenderCtx::empty()`
hazards lose their teeth (a typed value carries its own truth even
when ctx is thin).

**P4 — sweep (~½ session).** Delete the remaining depth-repair
helpers, update DESIGN § "TypedExpr-with-smart-ctor" from
"opportunistic" to "the renderer's contract", close REVIEW § 2.1.

Total honest estimate: **4–5 sessions** of the recent working size.

## Cost & risk, honestly

* **Goal-shape churn is the real cost.** Bridging must not add
  annotations/coercions where today's output is already right —
  hence the P0 passthrough guarantee and per-phase e2e gating. Where
  output DOES change, today's output was wrong (that's the point),
  but a few of the 520 pins may close differently and need eyeballing.
* **Arm audit burden.** 55 + 61 arms; most are "claimed is correct"
  one-liners. The D2 rows are where the care goes.
* **The trust model doesn't change.** TypedExpr is
  trust-at-construction; we're concentrating ~116 reviewable typing
  claims at arms instead of re-deriving typs at hundreds of use sites.
  Not weaker than today — strictly fewer places to lie.
* **What we get to delete** (the measurable win):
  `sst_lean_wrap_count`, `tuple_slot_extra_derefs`,
  `vir_ret_eq_rhs_typ`, `render_expr_with_derefs`,
  `caller_arg_actual_typ` plumbing, the READPLACE-lift residue — plus
  every FUTURE session this family would have cost.

## Non-goals

No Lean elaborator in Rust; no typeclass/metavariable modeling; the
obligation/Prop layer stays untyped; `lean_pp` unchanged
(`into_untyped` at the emission boundary).
