# bootstrap-34 step 2a — the SST/VIR dump that settles the fork

**Verdict: WORLD (a) — Verus MATERIALIZES per-arg call coercions as `Clip`
nodes inside the arg subexpr. The cache-churning per-arg-`TypData` `RawList`
edit (probe18 step 2b) is UNNECESSARY.** Remaining work is only the three Rust
serializer arms + a bridge test (steps 3–4), reusing the *existing* no-`TypData`
`tactus-core` machinery — which, it turns out, is already landed and verified.

## How the dump was produced (cheap: existing binary, no serializer rebuild)

Input: `bootstrap-fixture/appn_probe.rs` (heterogeneous 2-/3-arg spec fns +
a ref-arg exec caller). Command (from `bootstrap-fixture/`):

```
../source/target-verus/release/verus --crate-type=lib --lean-backend \
  --log-dir .verus-log-appn --log vir --log vir-sst appn_probe.rs
```

`--log vir` → `crate.vir` (VIR `ExprX`, what `raw_vir_exp` reads);
`--log vir-sst` → `root-sst.vir` (SST `Exp`, what `raw_exp` reads).
The `.verus-log-appn/` dir is regenerable — deleted after extracting the
excerpts below.

## Finding 1 — Verus has NO implicit per-arg coercions (compile error)

`g2(x, y)` with `x: u64` into a `nat` param is a **hard type error**:

```
error[E0308]: mismatched types
  --> appn_probe.rs:34:8
34 |     g2(x, y)
   |     -- ^ expected `nat`, found `u64`
```

So every `u64→nat` (or any narrowing) call-arg coercion **must** be a source
`as` cast. There is no "elided implicit coercion" world for spec-fn call args —
world (b) is impossible for the coercion axis by construction of the frontend.

## Finding 2 — every source `as` cast is a materialized `Clip` in the arg; the arg's own `.typ` is the coerced type

`call_explicit(x: u64, y: int) = g2(x as nat, y)`, VIR (`crate.vir`):

```
(> Call (CallTarget Fun … (Fun :path "appn_probe!g2.") () () …)
   (  ; arg 0 — a Clip whose OWN type is Nat:
    (> Unary (UnaryOp Clip :range (IntRange Nat) :truncate true)
       (> ReadPlace … (VarIdent "x" …) (Typ Int (IntRange U 64)) …)
     ) (Typ Int (IntRange Nat)))            ; <-- arg0.typ = Nat
    ; arg 1 — bare int, no clip:
    (> ReadPlace … (VarIdent "y" …) (Typ Int (IntRange Int)))
     (Typ Int (IntRange Int)))              ; <-- arg1.typ = Int
   ) None
 ) (Typ Int (IntRange Int))
```

Same at the SST level (`root-sst.vir`):

```
(Exp Call (CallFun Fun (Fun :path "appn_probe!g2.") None) ()
  ((Exp Unary (UnaryOp Clip :range (IntRange Nat) :truncate true)
      (Exp Var (VarIdent "x" …) (Typ Int (IntRange U 64)))
    ) (Typ Int (IntRange Nat)))             ; arg0.typ = Nat
   (Exp Var (VarIdent "y" …) (Typ Int (IntRange Int))))  ; arg1.typ = Int
```

The `Call` node itself carries **no per-arg-type slot** (just the fn, the
type-args `()`, and the flat arg list). It doesn't need one: `arg.typ` already
reflects the callee-expected type because the `Clip` is *inside* the arg.
`call_two_nat_explicit` (both args Clip'd) and `call_three` (length-3 spine,
args 0 & 2 Clip'd) confirm the same shape at every arity.

## Finding 3 — a `&T`/`*t` ref-deref arg arrives value-typed (the secondary axis is a no-op too)

`call_ref(n: u64, t: &Tree)` with `count_at(n as nat, *t)`, SST:

```
(Exp Call (CallFun Fun (Fun :path "appn_probe!count_at.") None) ()
  ((Exp Unary (UnaryOp Clip :range (IntRange Nat) …)
      (Exp Var (VarIdent "n" …) (Typ Int (IntRange U 64)))
    ) (Typ Int (IntRange Nat)))                       ; arg0 Clip'd → Nat
   (Exp Var (VarIdent "t" …)
      (Typ Datatype (Dt Path "appn_probe!Tree.") () ())))  ; arg1 = bare Tree VALUE
```

The `&Tree` decoration and the `*t` deref are **fully resolved away** before
transcription — the arg is a plain `Var t` of value type `Tree`, not a
ref-typed node. So `needs_ref_deref(type_of arg)` (which fires only on
`TypData` tag 4 = `TyRef`) is `0` here too.

## Why this kills step 2b entirely — the two per-arg helpers are both no-ops

The single-arg `Call` render arm (`tactus-core/lib.rs` L901) runs, per arg,
`coerce_if(needs_nat_coercion(type_of arg, argTy)) ∘ deref_if(needs_ref_deref(type_of arg))`:

- `needs_nat_coercion(op, res)` = 1 iff `op` is `int` (tag 0) **and** `res` is
  `nat` (tag 1). In the Call arm `argTy = arg.typ` and `type_of(rendered arg)`
  derives from that **same** `arg.typ`, so `op == res` **always** ⟹ never
  `int`-then-`nat` ⟹ **always 0** (structural no-op). Materialization (Finding 2)
  is exactly what makes `arg.typ` already carry the coerced type.
- `needs_ref_deref(op)` = 1 iff `op` is `TyRef` (tag 4). Ref/deref args resolve
  to value-typed `Var`s (Finding 3) ⟹ **never tag 4** ⟹ **always 0**.

So the *existing* no-`TypData` `render_list` (`lib.rs` L974: plain
`render_exp` per element, no `coerce_if`/`deref_if`) is **identical** to the
single-arg per-arg chain on every multi-arg shape that can be produced. And the
whole multi-arg spine is **already present and verified** in `tactus-core`:

- `RawExp::CallN(u64, TypData, Box<RawList>)` — fn, ret, args; **no per-arg type** (L392)
- `RawList::Nil | Cons(Box<RawExp>, Box<RawList>)` — **no per-arg type** (L405)
- `render_exp`: `CallN(fn, _ret, args) => AppN(fn, render_list args)` (L944)
- `render_list`: plain per-element `render_exp` (L974)
- `ExprData::AppN(u64, Box<ExprList>)` (L332); test cases at L1592–1603

⟹ **step 2b is a no-op: not even an additive constructor is needed.**

## Revised remaining plan (supersedes REPORT steps 2–4)

- ~~Step 2a~~ DONE (this doc).
- ~~Step 2b (cache-churning per-arg-`TypData` edit)~~ **CANCELLED** — world (a);
  the machinery already exists with the right (no-`TypData`) shape.
- **Step 3 (the only code left):** widen the three fail-loud arms in
  `source/lean_verify/src/sst_serialize.rs` to emit the multi-arg spine —
  reference `raw_exp` (`raw-call-arity`, L683) and `raw_vir_exp`
  (`rawvir-call-arity`, L932) → `RawExp.CallN(fn, ret, RawList[args])`;
  production `lexpr_to_exprdata` (`ed-app-arity`, L1421) → `ExprData.AppN(fn,
  ExprList[args])`. These are Rust serializer edits (rebuild `lean_verify` only)
  — **no `tactus-core` base-hash change, no whole-crate re-verify.** Co-design
  hinges on production's multi-arg `LExpr` head/arg shape (flat vs curried; the
  §7 Q3 test at L1592 assumes flat) — verify with a production `--emit-lean`
  dump of a 2-arg caller before writing the `lexpr_to_exprdata` arm.
- **Step 4:** add a 2-arg spec-fn caller to the fixture (or extend
  `probe17_w7d_live`) and close the live `def_eq` bridge.

## Residual honesty

Every multi-arg shape I could *construct* (heterogeneous coerce, length-3,
ref-deref arg) transcribes correctly with the existing machinery. The single
unproven corner: if some shape could make an arg's transcribed `TypData` carry
tag 4 (`TyRef`) *in list position*, plain `render_list` would drop a derived
`.deref`. I could not produce one — Verus resolves ref decorations away before
transcription. Step 3 should census-check for a `TyRef`-tagged multi-arg arg; if
one is ever found, the fix is to add a **per-element `deref_if`** to
`render_list` (which needs only the arg's OWN type — still **no** per-arg
`TypData` field). This is orthogonal to, and far cheaper than, the cancelled
step 2b.
