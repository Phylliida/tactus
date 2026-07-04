# BUG: call-arg SST temps record claimed (Ref-decorated) typ, emit ill-typed artifacts

**Status:** OPEN, diagnosed 2026-07-04. Pinned by
`test_exec_vec_field_index_clone` (currently `=> Err`; flip to `Ok` when
fixed). Blocks tactus-group-theory's `apply_hom_symbol_exec` (the last
un-migrated fn besides its dependents).

## Symptom

Cloning an element of a nested Vec behind a struct field:

```rust
struct Holder { imgs: Vec<Vec<u8>> }
fn clone_field_index(h: &Holder, i: usize) -> (out: Vec<u8>)
    requires (i as int) < h.imgs@.len(),
    ensures out@ == h.imgs@[i as int]@,
{ h.imgs[i].clone() }
```

emits obligation exps containing `std_specs.vec.spec_vec_len Int
alloc.Global tmp__1` where `tmp__1 : vec.Vec Int alloc.Global` — bare
value at a `Tactus.Ref (vec.Vec ..)`-typed slot. Lean:
"Application type mismatch … expected Tactus.Ref".

## Root cause (diagnosed, probe-verified)

The clone-callee's `self` substitutes to an SST temp (`tmp__1`, minted
by Verus's SST flattening for the index-read). In
`build_call_substitutions`:

* the substitution entry's `actual_typ` comes from
  `caller_arg_actual_typ`, which for a Var falls back to **arg.typ —
  the CLAIM** (`Decorate(Ref, …, Vec)`, probe-verified);
* the rendered binding of `tmp__1` holds the **bare** value (the
  borrow renders transparent);
* so `coerce_lexpr(claim → slot)` is an identity where a
  `Tactus.Ref.mk` wrap was needed.

## What was tried (all landed as groundwork, none sufficient)

1. `caller_arg_actual_typ` consults `obl.let_binder_typs` (the walker's
   storage-typ ledger) for non-param Vars — CORRECT but insufficient:
   probe shows **`tmp__1` has no ledger entry** at the call walk
   (ledger = `{tmp__2}` only).
2. Args render through the typed spine (`exp_to_typed` with the walk's
   binder-aware ctx + ledger) in `build_call_substitutions` — same
   result: the Var arm's ledger lookup misses, falls back to claim.
3. (Reverted) extending `caller_param_typs` with all `local_decls` —
   too broad; that map feeds `with_binder_typs` rendering and broke an
   instance emission ("Fields missing: clone").

## The open question for the fix

Where is `tmp__1`'s `let` frame pushed? Probes show NONE of the known
paths fire for it (no `walk_let` ledger insert, no `Wp::LetRaw`), yet
the emitted theorem contains `let tmp__1 := seq.Seq.index …`. Most
likely the binding is created at a call-walk/hyp-construction site that
builds the let-expression directly (or a WP-build shape not covered by
the walkers' ledger recording). Find that site; record the binding's
storage typ in `let_binder_typs` (or bind at the arg's actual typ with
an explicit `Tactus.Ref.mk` per the U2 invariant). The typed-spine
plumbing from (1)+(2) will then pick it up with no further change.

Debug aid: the probes used are in this bug doc's diagnosing session;
re-add `TACTUS_DEBUG_ARGS` eprintlns at `build_call_substitutions`'s
arg loop, `OblCtx::with_let_binder`, and the `Wp::LetRaw` arm.
