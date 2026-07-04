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

## ROOT CAUSE FOUND (2026-07-04, second session) — fix is a P3-completion

**The binding site**: `tmp__1` is the **vec-index CALL's return dest**
(the WP tree is `Let(tmp__2) → Call(index, dest=tmp__1) → Call(clone) →
Done` — `imgs[i]` is itself an exec call). The dest binds in
`push_post_call_frames` Phase 5 via the #128 substitution path:
`dest_value = E` where E = the ret-eq extraction from the callee's
ensures.

**The precise bug**: in `push_ret_frames`, the `ret_substitution`
bridge (`coerce_lexpr(e, e_typ, ret.typ)`) is SKIPPED for non-integer
rets ("numeric sorts don't apply — raw is correct") — conflating
sort-bridging with WRAPPER-bridging. Probe-verified: `e_typ =
TypParam(T)` (bare, honest), `ret.typ = Decorate(Ref, T)` — the skipped
bridge is exactly the missing `Tactus.Ref.mk` (U2 violation), and every
downstream use of the dest at a Ref-typed slot is ill-typed.

**Why the spot fix was reverted**: unifying both branches through
`coerce_lexpr` fixed the original mismatch (apply_hom 9→5 errors) but
RELOCATED the lie — new "Application type mismatch" sites appeared
(find_cancellation 0→4) because the bridge input `e_typ = q.rhs.typ`
is ITSELF a claim, and `render_call_ensure_expr` (the full
substitution render) has no typed variant reporting the actual typ of
what it produced. Also surfaced: the DESIGN.md "blanket shell
instances" tripwire fires as `Fields missing: clone` when the Clone
class emerges FULL in a crate where clone is resolvable while
instances still emit shell-style (a separate class/instance
consistency bug — the tripwire working as intended, loudly).

**The real fix (well-scoped, fresh session)**: extend the typed spine
through the call-ensures path — a typed `render_call_ensure_expr`
(returning value + actual typ, like `exp_to_typed`) so the
eq-extraction carries its rendered-actual typ; then the
`push_ret_frames` bridge (unified over both ret families) coerces from
truth to `ret.typ`, and the site tactics in tactus-group-theory's
find_cancellation_exec get re-tuned to the (now correctly wrapped)
shapes. Expect the class/instance shell-consistency bug to need its
own small fix (emit the class as shell iff its instances will be
shells — one predicate, two consumers).

Debug aid: re-add `TACTUS_DEBUG_ARGS`/`TACTUS_DEBUG_WP` eprintlns at
`build_call_substitutions`'s arg loop, `OblCtx::with_let_binder`, the
`Wp::LetRaw` arm, `walk_obligations` entry (variant dump), and the
`eq_extraction` build in `push_post_call_frames`.
