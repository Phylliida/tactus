---
title: "W5f v2 follow-on — GROUND the leaf-denotation oracles (fn/fnN/proj/ctorTag/ctorField) to REAL emitted defs, discharging the free hypotheses"
status: in_progress
claimed_by: opus-bootstrap57-groundoracles
created: 2026-07-16T02:30:00Z
updated: 2026-07-16T02:30:00Z
---

## Description

Spun out of bootstrap-55/56 (W5f v2). The reference-WP soundness model (probe29,
`w5f_v2_match_sem.lean`) defines a flat-Int operational semantics `eval`/`edenote`
over the emitted mirror `ExprData`, parameterized by an ABSTRACT `SymEnv` whose
oracle fields are:

```
av   : Int → St → Int         avP  : Int → St → Prop
opk  : Int → OpKind           fn   : Int → Int → Int          -- App   (unary spec-fn)
fnN  : Int → List Int → Int   proj : Int → Int → Int          -- AppN / FieldProj
ctorTag   : Int → Int         ctorField : Int → Nat → Int      -- Match decode
```

**Every adequacy fact** (FACT 5 `app_grounded`, FACT 8 `appn_grounded`, FACT 9/10/11
`match_*`) is stated over an **abstract `E : SymEnv` with FREE hypotheses** —
`hfn : E.fn fId = g`, `hfnN : E.fnN fId = h`, `htag : E.ctorTag v = c0`. The honest
content today is arm-selection / binder-threading / call-shape; the oracles
themselves are unconstrained.

**This card grounds them:** build a CONCRETE `crateEnv : SymEnv` literal (the P5
match-literal pattern, cf. probe5_symenv's `crateEnv`) that PINS `fn`/`fnN`/`proj`/
`ctorTag`/`ctorField` to the **actual emitted defs**, and re-derive the adequacy
facts as specializations where the hypotheses **discharge by `rfl`/`decide`** — so
the leaf denotation is tied to real emitter output, not a free assumption.

**Done when:** a probe elaborates a concrete `crateEnv` over real emitted user
spec-fns/datatype and the specialized adequacy facts close with the `hfn`/`hfnN`/
`htag`-style hypotheses discharged by `rfl`/`decide` (not passed in), over standard
axioms only. Staged — see rungs. Rung 1 alone is a meaningful close of the "free
hypothesis" gap for the CALL fragment.

## Recon (done 2026-07-16 — the design fork is settled)

**A. The emitter emits REAL Lean inductives, not a flat-Int encoding.** A datatype
value renders as a genuine Lean constructor + projection: `bootstrap-fixture/out/lib/
mk_point.lean`'s obligation is literally `let p := lib.Point.mk a b; p.x = a` over a
real `lib.Point` inductive. Consequence: `ctorTag`/`ctorField` have **no
emitter-produced Int-encoding to invert by `rfl`**. Grounding them means CHOOSING an
embedding `emb : U → Int` and PROVING `fnN`/`ctorTag`/`ctorField` mutually consistent
w.r.t. it — a real encoding/adequacy theorem, not a discharge. (Confirmed w/
Danielle's local model: "you are no longer performing grounding, you are proving an
encoding theorem — the Hard Rung.")

**B. The ExprData vocab has NO `Ctor` node** (tags 0–14: Atom/Lit/LitBool/Cast/BinOp/
App/FieldProj/SpanMark/Let/Not/Ite/Match/AppN/Forall/Exists — see
`TactusDefs_lib_exec__root.lean:103` `ed_tag`). So a constructor application
`Point.mk a b` renders through `App`/`AppN` (denoted by `fn`/`fnN`), and a field
access `p.x` renders as `FieldProj` (tag 5, denoted by `proj`). **`Match` (tag 11) is
the SOLE consumer of `ctorTag`/`ctorField`.** `render_exp`'s `RawExp.Field` →
`ExprData.FieldProj`, `RawExp.CallN` → `ExprData.AppN`, `RawExp.MatchR` →
`ExprData.Match` (root.lean:72–84).

**C. Real emitted user spec-fns exist — in the FIXTURE, not tactus-core.**
`bootstrap-fixture/out/lib/TactusDefs_lib_exec__root.lean` defines:
`lib.sq (x:Nat):Nat`, `lib.tri (n:Nat):Nat` (match-free unary), `lib.g2/g3` (N-ary),
and **`lib.tree_head (t:lib.Tree):Int`** — a MATCH-bodied fn over a real `lib.Tree`
datatype (this is the `tree_head.defcert.lean` the bootstrap-56 census flagged, the
only real `Match`-carrying cert on the slice → the natural rung-3 fixture).
tactus-core's own emitted defs are ALL `noncomputable` `ExprData→ExprData` machinery
(`pow2 : Nat→Int` is the only Int-returning one) — **no clean same-crate `Int→Int`
user fn to ground against.** So honest grounding is inherently cross-crate.

**D. CRUX obstacle — module-name collision.** Both crates emit the SAME module names
(`TactusDefs_lib_exec__root`, `__base`, `__seq_Seq`, …) into the SAME `lib`
namespace. `lib.sq` lives in the fixture's `__root`; `render_exp` lives in
tactus-core's `__root`. Same module name, different contents → a probe cannot put
both on `LEAN_PATH` (the loader resolves one olean per module name). Symbols are
disjoint (no `lib.sq` in tactus-core, no `render_exp` in the fixture), so a **module
RENAME** (re-emit/re-elaborate the fixture's def cone under a distinct module prefix,
e.g. `TactusDefs_fixlib_*`) makes the two importable together. This is the one-time
"plumbing tax" rung 1 pays. (Danielle's model: prefer this over a probe-local
hand-written fn — option (b) proves the MODEL satisfiable but bypasses the
emitter-output pin, which "invalidates the bootstrap claim.")

**E. Prior art.** `probe5_symenv.lean` already realizes a concrete `crateEnv :
SymEnv` and closes `gdenote crateEnv [] [] g1 = rendered1 := by rfl` — BUT for an
OLDER toy SymEnv (`.U`/`.tequ`). The current W5f-v2 SymEnv (probe28/29) has NO
concrete literal; its facts are all abstract. So this is fresh for the current model,
reusing the probe5 match-literal pattern.

## Staging (validated with Danielle's model)

- **RUNG 1 — ground `fn`/`fnN` (the CALL fragment).** Solve obstacle D: re-emit (or
  copy+rename) the fixture's def cone so a probe imports BOTH tactus-core's
  `render_exp` AND the renamed fixture's `lib.sq`/`lib.g2`. Build `crateEnv` pinning
  `fn sqId = <lib.sq lifted to Int>` / `fnN g2Id = <lib.g2 …>`. Specialize FACT 5/8
  so `hfn`/`hfnN` discharge by `rfl`. NOTE the Nat/Int seam: `lib.sq : Nat→Nat` but
  the goal language is Int and `g : Int→Int` — this exercises the real
  `needs_nat_coercion`/`coerce_if` render path (a feature, the realistic case), so
  either lift `lib.sq` through `Int.toNat`/`Int.ofNat` in the pin or state the fact
  at the coerced shape. Rung 1 = "the CALL leaf is pinned to emitter output."
- **RUNG 2 — ground `proj`/`FieldProj`.** Same setup over `lib.Point` (mk_point
  fixture): `p.x` renders `FieldProj (…) xFieldId`; pin `proj (embPoint p) xFieldId =
  <x-field of p>` consistent with the `Point.mk` encoding. Uses the same crateEnv.
- **RUNG 3 (the Hard Rung) — ground `ctorTag`/`ctorField` over a real ENUM+match.**
  Target `lib.tree_head`/`lib.Tree`. Choose `emb : lib.Tree → Int`, define
  `fnN`(constructor)/`ctorTag`/`ctorField` from it, and PROVE the consistency the
  FACT 9/10/11 hypotheses assume (`ctorTag (emb (Ctor …)) = tagOf Ctor`,
  `ctorField (emb (Ctor a b)) i = emb·aᵢ`). This is the encoding theorem, not an
  `rfl`. Because bodies (where Match lives) are already handled by the `fn`-pin
  (bootstrap-56 census), rung 3 is completeness for the RARE direct-Match-in-goal
  case — do it last, and only if the census ever finds a live one.

## Progress

- (2026-07-16, opus-bootstrap57-groundoracles) **CLAIMED + full recon + design fork
  settled; NO Lean landed this turn** (rung 1's module-rename is real plumbing, not a
  one-sitting change — recording the de-risked path so the next instance starts
  clean, per the W4/bootstrap-39 recon idiom). Findings A–E above. Consulted
  Danielle's local model on the fork: confirmed (1) ctorTag/ctorField grounding is an
  encoding theorem not a discharge, (2) the module collision is real, (3) the 3-rung
  decomposition is correct, and steered rung 1 to the module-RENAME (option a) over a
  probe-local hand-written fn, for bootstrap honesty. **Crisp entry for next
  instance:** start rung 1 = get a probe to import both tactus-core `render_exp` and a
  renamed copy of the fixture's `lib.sq` cone (obstacle D), then specialize FACT 5.

## Writeup

_when done: the concrete `crateEnv` literal, which oracles are pinned to which real
emitted defs, how the module-rename was done (obstacle D), how the Nat/Int coerce
seam was handled, and — for rung 3 — the chosen embedding + the consistency theorem.
Be explicit about which rungs landed vs. remain, and that rung 3 is the genuine
encoding-adequacy theorem (the others are rfl discharges)._
