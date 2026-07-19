# BUG: user-trait **default methods** break class/instance emission; impl-only trait classes missing from the defs umbrella (B6 follow-ons)

**Date:** 2026-07-19
**Found by:** the tactus-algebra arc (verified-CAD program), while probing why
`OrderedRing`/`PartialOrder` obligations failed with
`Unknown identifier lib.traits.partial_order.PartialOrder.le` after the B6
emission closure (e3da0f9).
**Status:** diagnosed; crate-side workaround applied in tactus-algebra
(`ge`/`gt` made required methods, provided per-impl). Two hard emission bugs
below, plus the walk-gap that had been hiding them.

## Symptom

`tactus-algebra` at the state where a generic fn first uses `T: OrderedRing`
as a bound (before that state, see "Walk-gap" below):

    verus --lean-backend -V cache --crate-type=lib src/lib.rs
    → tactus: defs module build failed for crate `lib` (full roots)
      — falling back to standalone emission
    → 8 verified, 545 errors  (whole-crate collapse:
      450× "Lean tactus_auto failed", 78× "Tactus codegen produced
      unresolved references")

The defs build failure (dumped to
`target/tactus-lean/lib/TactusDefs_lib_exec__base.lean.failed`) is two
independent bugs, both specific to **trait default methods** — every other
class in the ladder (`Equivalence → Field`) emits cleanly precisely because
none of them has a default method.

## Bug 1 — class emission: default-body references the not-yet-declared projection

Emitted class declaration:

```lean
class lib.traits.ordered_ring.OrderedRing (Self : Type)
    extends lib.traits.ring.Ring Self, lib.traits.partial_order.PartialOrder Self where
  lt : Self → Self → Prop
  ge : Self → Self → Prop := fun (self : _) (other : _) =>
    (lib.traits.ordered_ring.OrderedRing.lt other self : Prop)   -- ← BAD
  gt : Self → Self → Prop := fun (self : _) (other : _) =>
    ((lib.traits.ordered_ring.OrderedRing.lt self other : Prop)) = False
    ∧ ((lib.traits.equivalence.Equivalence.eqv self other : Prop)) = False
```

Elaboration:

    TactusDefs_lib_exec__base.lean:88:60: error: Invalid field `lt`:
      The environment does not contain `Function.lt`
    TactusDefs_lib_exec__base.lean:89:61: error: (same)

Inside the declaring class, the fully-qualified projection
`lib.traits.ordered_ring.OrderedRing.lt` does not exist yet, so dot-notation
resolution on the class constant misfires. Default bodies must reference the
**bare field name** (`lt other self`) or an equivalent in-scope form — the
source here is the Rust default body `other.lt(self)`, which the emitter
qualifies as if the class were already in scope.

## Bug 2 — instance emission: trait-default methods assigned under mangled names

Emitted instance (impl provides `lt` + axioms; `ge`/`gt` come from the Rust
trait defaults):

```lean
noncomputable instance : lib.traits.ordered_ring.OrderedRing Int where
  lt := fun (self : _) (other : _) => self < other
  axiom_le_total := fun (a : _) (b : _) => by sorry
  ...
  impl__5_default_ge := fun (self : _) (other : _) =>
    lib.traits.int_ring.impl__5_default_ge self other   -- ← BAD
  impl__5_default_gt := fun (self : _) (other : _) =>
    lib.traits.int_ring.impl__5_default_gt self other
```

Elaboration:

    error: `impl__5_default_ge` is not a field of structure
      `lib.traits.ordered_ring.OrderedRing`
    error: `impl__5_default_gt` is not a field of structure ...
    error: Fields missing: `ge`, `gt`

The mangled Rust-side name of the default-method impl
(`impl__5_default_ge`) is used as the *field* name. Correct behavior: when
the impl does not override the method, emit nothing (the class default covers
it); when it does override, assign the method's field name (`ge := ...`).

## Walk-gap (the reason these were latent)

Neither bug fired before because the defs umbrella only includes a trait's
class when **some generic fn uses the trait as a bound** (Ring via `poly*`,
Field via `divmod`). A trait that is only ever *impl'd* for concrete types —
`tactus-algebra`'s `PartialOrder`/`OrderedRing` were, until the probe — never
gets its class emitted, while the impl-obligation stmt files still reference
it:

    error(lean.unknownIdentifier): Unknown identifier
      `lib.traits.partial_order.PartialOrder.le`
    (16 fns: PartialOrder+OrderedRing impl obligations for int and Rational)

Repro of the gap: tactus-algebra with the `OrderedRing`-bounded lemmas in
`src/lemmas.rs` removed; the classes vanish from
`TactusDefs_lib_exec__base.lean` and the stmt files fail as above. Adding any
one generic `T: OrderedRing` fn pulls in both classes (supertrait closure)
and both instances — which is how Bugs 1+2 surfaced. If bound-driven
inclusion is intended, the gap is that impl-obligation stmts are emitted for
traits whose classes are not; if not intended, the walk needs to treat
impl'd traits as roots.

## Blast radius

A single default method anywhere in an emitted trait takes down the **whole
crate**: the defs umbrella fails to elaborate, the attempt ladder falls
through to standalone emission, and every per-fn file loses its imports
(545 errors from two bad lines). Worth a render-level guard (skip/degrade
the offending class rather than fail the part) independent of the fix.

## Crate-side workaround (applied, keeps semantics)

- `ge`/`gt` in `OrderedRing` made required methods (no default bodies);
  provided per-impl with the same formulas the defaults had
  (`other.lt(self)` / `!self.lt(other) && !self.eqv(other)`).
- Generic bound users added where genuinely wanted anyway (ordered lemma
  kit in `lemmas.rs`), pulling the classes in.
- Impl method bodies for `eqv`/`le`/`lt` on `Rational` inlined to closed
  cross-multiplication form (matching the `int` impls' style) so the fixed
  closer's `simp only [<projection>]` reaches omega-closable goals — the
  spec-fn indirection (`eqv_spec` etc.) otherwise strands the goal behind an
  un-unfolded def. This third item is really the N3 recursive-unfold
  territory, not this BUG; noted here because it's the same probe.

## Fix directions

1. Class emission of a default method body: reference sibling fields
   unqualified (or via the in-progress class's local field binders), never
   the qualified projection.
2. Instance emission: map provided methods to their trait field names;
   emit nothing for non-overridden defaults (the class already carries the
   default body — see Bug 1 for what it must look like).
3. Decide the walk-gap semantics (bound-driven vs impl-driven inclusion of
   classes) and make stmts/defs agree either way.
4. Consider a per-class render guard so one bad class can't sink the defs
   umbrella for the whole crate.

## Evidence pointers

- Failing defs dump: `tactus-algebra/target/tactus-lean/lib/TactusDefs_lib_exec__base.lean.failed`
  (class decl ~line 86, instances ~lines 141/184 in that file).
- Gate: `tactus-algebra/check.sh` (post 2026-07-19 LEAN_PATH fix —
  unrelated, but required to reproduce since `by (nonlinear_arith)` emits
  `import Mathlib.Tactic.Linarith`).
- B6 parent: `BUG-lean-all-proofs-user-traits.md` (emission phase closed
  e3da0f9; this is the next layer underneath).
