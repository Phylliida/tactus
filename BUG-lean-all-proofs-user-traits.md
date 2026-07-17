# BUG: `--lean-all-proofs` — user trait declarations & instance connection (new family, "B6")

**Date:** 2026-07-16
**Found by:** the tactus-algebra arc (verified-CAD program) — first trait-heavy
corpus pointed at `--lean-all-proofs`.
**Status:** diagnosed, not fixed. Companion to `DESIGN-lean-all-proofs-bugs.md`
(B1–B5 families); this is a distinct family those fixes don't cover — gt is
nearly trait-free, so it never surfaced there.

## Symptom

`../tactus-algebra` (182 proof fns, everything generic over a user trait ladder
`Equivalence → … → OrderedField`, plus impls for `int` and a `Rational` struct):

    verus --lean-backend --lean-all-proofs -V cache --crate-type=lib src/lib.rs
    → 2 verified, 5352 errors   (19 min; package gate skipped)

The only passing proof fn is the crate's only trait-free lemma
(`lemma_distrib_scale`, pure `Int` atoms) — i.e. the error mass is entirely this
family, not proof power. The same crate under the default `--lean-backend`
(proof fns → Z3): 182 verified, 0 errors, 5.5 s.

## Two failure modes

**(a) Cross-module: user trait classes never emitted into the island preamble.**
Island files for `tactus-algebra` contain the vstd spec-world (`lib.seq.*`
axioms, `Fn`/`Tuple` classes …) but no `class` declaration for the crate's own
traits, so every trait-method reference is an unknown identifier:

    error: Unknown identifier `lib.traits.partial_order.PartialOrder.le`
    (e.g. target/tactus-lean/lib/traits__int_ring__impl__5__axiom_le_mul_nonneg_monotone.lean;
     the emitted theorem binds `(h_req0 : (lib.traits.partial_order.PartialOrder.le ((a : Int)) ((b : Int)) : Prop))`
     with no such constant in scope — note also no instance argument on the application)

**(b) Single-module: impl obligations not connected to the instance body.**
Minimal repro (below, one file): the trait class resolves, but the impl's axiom
obligation is stated against the bare trait method and the closer has no way to
reduce it to the `int` instance's `open spec` body:

    a : Int
    ⊢ repro.Foo.foo_le a a
    → auto-tactic failed (1 verified, 1 errors — the *caller* of the axiom passes,
      the impl obligation itself fails)

## Minimal repro

```rust
use vstd::prelude::*;

verus! {

pub trait Foo: Sized {
    spec fn foo_le(self, other: Self) -> bool;

    proof fn axiom_foo_refl(a: Self)
        ensures a.foo_le(a),
    ;
}

impl Foo for int {
    open spec fn foo_le(self, other: Self) -> bool {
        self <= other
    }

    proof fn axiom_foo_refl(a: Self) {}
}

pub proof fn use_trait_method(a: int)
    ensures a.foo_le(a),
{
    int::axiom_foo_refl(a);
}

} // verus!
```

    verus --lean-backend --lean-all-proofs --crate-type=lib repro.rs
    → 1 verified, 1 errors (axiom_foo_refl fails with the ⊢ repro.Foo.foo_le a a goal)

Put the trait in one module and the impl/uses in another to reproduce mode (a).

## What a fix needs (sketch, from the outside)

1. Emit user `trait` decls as Lean `class`es (methods as fields) into the
   spec-world/defs preamble — same channel that already carries the vstd
   classes (`crate_defs.rs build_defs` / `generate.rs spec_world_cmds` per the
   emit-module code map), covering cross-module refs (mode a).
2. Emit `impl` blocks as `instance`s whose spec-method fields are the impl
   bodies, so trait-method applications at a concrete type are definitionally
   reducible (mode b) — plus instance-argument insertion at application sites
   (the mode-(a) binder shows the application currently missing it).
3. Trait proof-fn *obligations* (the impl's `axiom_*` ensures) should then be
   stated against the instance, with the body available to the closer.

## Acceptance corpus

`../tactus-algebra` is a ready-made acceptance gate for this family: 182
idiomatic trait-generic proof fns (trait ladder + int/Rational instances +
generic polynomial algebra through divmod/ring laws), currently
2/182 under `--lean-all-proofs` vs 182/182 under Z3. It is fresh, small, and
exercises: supertrait chains, static trait methods (`zero()`/`one()`),
default-body spec fns (`ge`/`gt`), generic fns with trait bounds calling
axioms, `assert ... by (nonlinear_arith)` inside impls, and cross-module
trait/impl/use splits. `./check.sh` there runs the default gate; add
`--lean-all-proofs` to re-measure this family.
