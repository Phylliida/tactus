# W7-AppN probe — per-arg-`TypData` `RawList` freeze (board bootstrap-34, step 1)

**Status:** ✓ green (`run.sh` rc=0, `wall≈2.1s`). All bridges close by `decide`
**and** `rfl`; all four mutation-kills are provably unequal; `render_exp` /
`render_list` and every checked theorem depend on **no axioms**; the non-vacuity
meta-check confirms `decide` refuses a false `¬(a=a)`.

## What this freezes

The one W7c body-constructor both transcriber sides still fail loud on:
**multi-argument application** (`CallN` → `AppN`). W7a's probe (probe15) already
froze a `RawList`/`render_list`, but in the **old shape** — `RawList.cons (hd)
(tl)`, no per-arg type, `render_list` = plain `render_exp` with no coercion. That
is the current `tactus-core` state (`lib.rs` `RawList::Cons(Box<RawExp>,
Box<RawList>)`, `render_list` at ~L974).

This probe freezes the per-arg-typed shape the batched `tactus-core` edit
(bootstrap-34 step 2) would land **if** it is needed — see the "Architectural
fork" section below, which found that necessity is **not yet settled** and hinges
on a materialize-vs-elide question a real multi-arg SST dump must answer first:

- **`RawList.cons (hd : RawExp) (argTy : TypData) (tl : RawList)`** — one
  expected-param-type per argument. This is the additive datatype field that
  forces the base-hash change ⟹ whole-crate re-verify + olean re-emit (the
  W6b/W7b "one batched cache-churning edit" discipline). It mirrors how the
  single-arg `Call(fn, ret, arg, argTy)` already carries its one arg's type, and
  how `ParamList::Cons(id, TypData, tl)` already carries a per-param type.

- **`render_list` = the single-arg `Call` arm generalized to a list.** Per cell:
  `coerce_if(needs_nat_coercion(type_of hd, argTy)) ∘
   deref_if(needs_ref_deref(type_of hd))`, in that order — byte-for-byte the
  chain the `Call` arm runs (`lib.rs` render_exp Call arm, L901–905). So the
  eventual `render_list` is literally that arm, lifted over `RawList`.

- **`CallN(fn, ret, args)` → `AppN(fn, render_list args)`** (the `_ret` slot is
  observable but unused by the render, exactly as in the single-arg `Call`).

## Cases (all in `probe18_appn.lean`)

| Case | Shape | What it exercises | Kill |
|---|---|---|---|
| **A** | `f(n, m)`, both params `nat`, bare `u64` args | both casts DERIVED from per-arg `argTy` (multi-arg generalization of W6a Case B) | drop the 2nd arg's `Int.toNat` |
| **B** | `g(n, k)`, params `(nat, int)` | **the load-bearing case** — coerce arg 0, leave arg 1 bare; closeable ONLY with per-cell `argTy` | (i) coerce the *wrong* arg; (ii) coerce *both* (what a uniform-type render does) |
| **C** | `h(*t, x)`, `t : &Tree` | auto-`.deref` a ref arg in list position; leave the int arg bare | forget the `.deref` |
| **D** | `f3(x, g(n), m)`, length-3 spine, arg 1 a **nested `callN`** | `render_list` recursion past length 2 + mutual recursion with `render_exp` (inner arg coerces) | drop the inner nested `Int.toNat n` |
| **E** | `g(n, m)`, both params `int`, bare int args | negative control: `render_list` is **not** vacuously coercive | — (must render both bare; `by decide`) |

Case **B** is the whole justification for the cache-churning edit: with a single
shared arg type you cannot render `g(Int.toNat n, k)` — you would coerce both or
neither. The two B kills pin exactly those two failure modes.

## ⚠ Architectural fork found — is the per-arg-`TypData` edit even load-bearing?

> **RESOLVED (step 2a, 2026-07-14) → WORLD (a). See `STEP2A-DUMP.md`.** A real
> multi-arg SST/VIR dump settled it: Verus rejects implicit call-arg coercions
> (compile error), so every coercion is a materialized `Clip` whose arg node's
> own `.typ` is the coerced type; a `Call` node carries no per-arg type and needs
> none. The per-arg-`TypData` edit (step 2b) is **UNNECESSARY and cancelled** —
> and the no-`TypData` `RawExp::CallN`/`RawList`/`render_list` spine is already
> landed & verified in `tactus-core`. Remaining work = step 3 (widen 3 serializer
> arms, Rust-only) + step 4 (bridge test). The analysis below is preserved as the
> pre-resolution reasoning; read `STEP2A-DUMP.md` for the settled plan.

**Correction to a first-draft claim in this report:** the single-arg serializer
does **not** put the callee's declared parameter type in the `argTy` slot. Both
`raw_exp` (SST) and `raw_vir_exp` (VIR) set `arg_ty = self.typ_data(&arg.typ)` —
the **argument node's own type** (`sst_serialize.rs` L689, and the L681 comment
"arg ty = the argument node's typ"). That fact reopens the question this card
assumes closed:

Because `argTy = arg.typ` and `type_of(the transcribed arg RawExp)` is derived
from that **same** arg node, the two are equal in practice, so the single-arg
`Call` arm's `coerce_if(needs_nat_coercion(type_of arg, argTy))` is a **structural
no-op** — it never fires. Any real `as nat` on a call arg is instead materialized
**inside** the arg subexpression as an explicit `Clip` node and handled by
recursion (the `sum_to` fixture leaf `tri(n as nat)` is exactly this; the W6a
probe Cases A/C confirm the call-node coerce/deref never fire). Likewise the
per-arg deref rides an explicit `Deref` node inside the arg.

So there are two worlds, and **which one holds decides whether this card's edit is
needed at all:**

- **(a) Verus MATERIALIZES per-arg call coercions** into the arg subexpressions
  (as the single-arg fixture does). Then `render_list` needs **no** per-arg type:
  each arg's `Clip`/`Deref`/`Cast` is transcribed recursively and the *existing*
  no-`TypData` `render_list` already renders correctly. **The cache-churning
  datatype edit is unnecessary.**
- **(b) Verus ELIDES per-arg call coercions** — as it demonstrably elides
  multiply-operand clips (W6a Case B: bare `u64 x` operands under a `nat`-typed
  `Mul`, casts DERIVED from the op result type). Then the arg's own `.typ` reads
  `Int`, the callee's expected `Nat` lives **only** at the call node, and
  `render_list` must carry the **expected** per-arg type to derive the cast.
  **The per-arg-`TypData` edit is load-bearing** — and this probe's machinery
  (Case B: coerce arg 0, leave arg 1) is exactly what's needed.

The local model (consulted on this fork) concurred: necessity hinges entirely on
materialize-vs-elide, and the edit should **not** be done until a real multi-arg
SST dump settles it. **Recommendation: before any cache-churning edit, get a
W6d.0-style SST/`LExpr` dump of a genuine ≥2-arg spec-fn call** (e.g. add a 2-arg
helper to the fixture or find one in the tgt slice) and inspect whether the args
arrive as bare-typed nodes (⟹ world (b), do the edit) or as explicit
`Clip`/`Cast`/`Deref` nodes (⟹ world (a), skip the edit and just widen the two
fail-loud arms to a no-`TypData` `AppN`/`CallN` spine).

## What this probe DOES establish (independent of the fork)

The per-arg render **machinery is correct if world (b) holds**: given per-arg
expected types, `render_list` = the single-arg `Call` arm generalized to a list
closes every correct render (A/B/C/D/E) and kills every dropped/mis-placed/
spurious coercion. It also freezes the invariants that hold in **both** worlds:

1. **`CallN(fn, ret, args)` → `AppN(fn, render_list args)`**, `_ret` observable
   but render-unused (a wrong return type is caught at the enclosing node), and
   **type-args dropped** keying on the fn name only — the existing single-arg
   convention (`RawExp::Call` drops `_typs`; `lexpr_to_exprdata` reads
   `app_head_fn_name`).
2. The two fail-loud arms to widen: reference `raw_vir_exp`
   `ExprX::Call(CallTarget::Fun, args)` (`Err("rawvir-call-arity")` on
   `args.len()!=1`) and production `lexpr_to_exprdata` `ExprNode::App` (`>1`
   value arg → `Err("ed-app-arity")`) — census-gated, unit-pinned, co-designed so
   `def_eq` agrees by construction.

## What remains (bootstrap-34 steps 2–4)

- **Step 2a (do this FIRST):** dump a real ≥2-arg spec-fn call's SST/`LExpr` and
  decide world (a) vs (b). This gates whether step 2b is even needed.
- **Step 2b (batched, cache-churning — ONLY if world (b)):** land
  `RawList::Cons(Box<RawExp>, TypData, Box<RawList>)` + the per-arg `render_list`
  in `tactus-core/lib.rs`; crate re-verifies, oleans re-emit, probe9/13/14/15
  stay green. If world (a): skip — the existing `render_list` suffices.
- **Step 3:** replace the two fail-loud arms in `sst_serialize.rs` with the
  census-gated, unit-pinned `CallN`/`AppN` transcriptions (with or without the
  per-arg type per the decision above).
- **Step 4:** a tgt-slice def with a ≥2-arg spec-fn call closes the live `def_eq`
  bridge (extend `probe17_w7d_live` or add a 2-arg fixture caller).

## How to reproduce

```
probe-w0/probe18_appn/run.sh          # LEAN=<lean> to override the toolchain
```
Pure Lean core — no Mathlib, no prelude, no tactus-core oleans.
