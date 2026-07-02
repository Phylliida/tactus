# BUG: vstd broadcast-preamble cluster poisons Lean-path exec-fn files

**Status:** OPEN — being fixed properly, one bug at a time (owner call
2026-07-02: no pruning/quarantine; fix the renderers).

**Found:** 2026-07-02, investigating why tactus-group-theory's derived
`Clone` fails under the Lean backend. It doesn't — the derived clone's
own obligation is `let _return := self.deref; _return = self.deref`
(trivially closable). The FILE fails: Clone's contract pulls vstd's
vec/deep-view broadcast-axiom cluster into the per-fn preamble, and
several rendering bugs in that cluster break elaboration of the whole
file, so every obligation in it reports "tactus_auto failed". The same
poisons sink the other Lean-path exec fns in vstd-heavy crates
(`is_inverse_pair_exec`, `apply_hom_symbol_exec` — same error
fingerprint, confirmed) — this cluster was most of tactus-group-theory's
78 errors at time of writing.

## Repro (seconds-fast loop, no Lean verification runs)

```rust
// /tmp/tactus-repro/mini.rs
use vstd::prelude::*;
verus! {
    #[derive(PartialEq, Eq, Clone, Copy)]
    pub enum Sym { Gen(usize), Inv(usize) }

    // vec cluster: axiom_vec_index_decreases, vec_clone_deep_view_proof,
    // DeepView instances
    pub fn touch_vec(v: &Vec<Sym>) -> (r: usize)
        requires v.len() > 0, ensures r == v.len(),
    { v.len() }

    // array cluster: array_view → Tactus.index fragment, View (Array T)
    // instance with const-generic N
    pub fn touch_arr(a: &[u8; 3]) -> (r: u8) ensures r == a[0], { a[0] }

    fn main() {}
}
```

```bash
verus --lean-backend --emit-lean --crate-type=lib mini.rs
LEAN_PATH="$HOME/.cache/tactus/prelude:$LEAN_PATH" \
  lean --json target/tactus-lean/mini/impl__4__clone.lean
```

All four preamble bugs appear in `impl__4__clone.lean` (line numbers as
of first capture; they drift with vstd):

## The bugs

### (1) Missing fragments for dep-walked defs — `Tactus.index`, `Fn` instances

```lean
noncomputable def array.array_view (T : Type) (N : Nat) (a : Array T) : seq.Seq T :=
  seq.Seq.new T (Int → T) N (fun (i : Int) => Tactus.index a i)
                                              ^^^^^^^^^^^^ Unknown identifier
```

Plus `failed to synthesize ops.function.Fn (Int → T) Int ?m` at the
`Seq.new` applications. `Tactus.index` and the arrow-type `Fn` instances
are per-file FRAGMENTS; the fragment collector doesn't emit them when
the def needing them arrives via the broadcast-axiom dep walk rather
than user code. Same root as CRATEDEFS.md's "fragment rehoming"
follow-up.

### (2) `View (Array T)` instance references unbound `N`

```lean
noncomputable instance {T : Type} : view.View (Array T) (seq.Seq T) where
  view := fun (self : _) => array.array_view T N self.deref
                                               ^ Unknown identifier
```

Lean's `Array T` erases the const-generic length, so vstd's
`View for [T; N]` impl cannot render over it — `N` has no binder to
come from. Verus's `[T; N]` typ DOES carry N (as a `ConstInt` typ arg),
the rendering drops it. Proper fix is a design decision: render `[T; N]`
as a length-carrying type (Lean core's `Vector T N`, or a
`Tactus.Array T N` prelude type) and re-point `array_view` / instances /
axioms at it. Owner input wanted before building.

### (3) Assoc-type projection unlifted inside INSTANCE BODIES

```lean
noncomputable instance … : view.DeepView (vec.Vec T A) (seq.Seq _tactus_assoc_T_DeepView_V) where
  deep_view := fun (self : _) => …
    seq.Seq.new (view.DeepView.V T) (Int → view.DeepView.V T) …
                 ^^^^^^^^^^^^^^^^^ Unknown constant
```

The instance HEAD lifts the projection correctly
(`_tactus_assoc_T_DeepView_V` binder), but the member BODY still renders
`<T as DeepView>::V` as an accessor constant. The standalone def
`Vec.DeepView.impl.deep_view` in the same file renders the identical
body CORRECTLY with the lifted binder — the RC2 projection-lift
(`impl_subst`) just doesn't reach the instance-member emission path.

### (4) Typ-arg substitution mismap in `axiom_vec_index_decreases` — **FIXED 2026-07-02**

```lean
… (view.View.view ((Tactus.Ref.mk v : Tactus.Ref (vec.Vec alloc.Global alloc.Global)) : seq.Seq alloc.Global)) …
                                                          ^^^^^^^^^^^^ should be A (the element type)
```

**Root cause (found by probe bisection: renderer faithful, VIR corrupted
post-`inline_spec`):** `substitute_body`'s type substitution composed the
per-level `map_expr_typ_visitor` (callback fires at EVERY typ node,
bottom-up, over rebuilt children) with the deep-recursive
`vir::sst_util::subst_typ` — so the parent-level callback re-substituted
its own output. With the axiom's element param named `A` colliding with
the inlined `Vec::<T, A>::spec_index` impl's allocator param `A`, the map
`{T ↦ A', A ↦ Global}` chained `Vec<T, A>` → `Vec<A', Global>` →
`Vec<Global, Global>` inside NESTED typs. Flat `TypParam` lists get one
application (leaf = no second pass) — which is why `DynamicResolved.typs`
survived and the corruption looked "selective". Invisible for
collision-free maps (re-runs are no-ops) — every prior test was
collision-free.

**Fix:** leaf-only callback (replace exactly `TypX::TypParam` nodes);
composed with the per-level visitor that IS simultaneous substitution,
exactly once. Pinned by `test_inline_typ_param_name_collision` (needs a
compound typ arg — `idp::<Pair<T, A>>` — to bite, per the flat-list
observation). `impl_subst`'s similar `rewrite_typ_rec` composition
audited: idempotent (its range is fresh synthetic names disjoint from its
domain), safe.

## Fn-specific bugs in the same crates (visible in `is_inverse_pair_exec`)

### (5) Enum variant/field tests through `Tactus.Ref` missing `.deref`

`Invalid field isGen: The environment does not contain Tactus.Ref.isGen`
(likewise `Gen_val0` etc.) — a variant test / field projection applied
to the wrapper-typed value instead of the deref'd inner. Wrapper-depth
(U2) family.

### (6) `istuple` variant test on Lean `Prod`

`Invalid field istuple: The environment does not contain Prod.istuple` —
tuple "variant test" should render as trivially `True` (tuples have one
variant), not as a `.istuple` projection.

## Fix order (each: miniature pin → fix → full e2e + unit gates → commit)

1. (4) typ-arg mismap — smallest, well-defined
2. (3) instance-body projection lift — machinery exists (`impl_subst`)
3. (1) fragment rehoming — CRATEDEFS follow-up, now with a repro
4. (5)/(6) wrapper variant-tests + istuple
5. (2) Array-N — design pass with owner first

Integration probe after each: regenerate the mini; final validation =
tactus-group-theory `./check.sh` (expect the 78 errors to collapse as
the cluster clears; 3 genuine `usize::MAX` IntegerTypeBound deferrals
in `todd_coxeter_rt.rs` / `find_cancellation_exec` remain — separate,
documented in DESIGN "Known deferrals").
