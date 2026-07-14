# W7a — defs-layer probe (definition-level bridge mechanic), board bootstrap-26

The **definition-level** analog of W6a (`probe12_w6a_castleaf`). W6a certified
one obligation *leaf* (an expression); W7a certifies the **definitions** the
obligations are stated in terms of — `@[reducible] def` spec-fn bodies,
`inductive` datatype decls, and `<T>.height` measures (trust-inventory **row
4**). Standalone, pure-Lean, **zero `tactus-core` edits** (no cache churn). It
**freezes the extended body vocabulary** the one batched W7b edit will land.

## What it proves

A hand-written, pure-core `.lean` (no Mathlib, no prelude imports, no
tactus-core oleans) with the extended mirrors + an **independent** reference
lowering `render_def`/`render_dt`, bridged against production-style DefData/
DtData for the **real emitted fixture** defs (ground truth:
`bootstrap-fixture/out/lib/TactusDefs_lib_exec__{root,base}.lean`).

The bridge per case: the CORRECT production `DefData`/`DtData` **equals**
`render_def(raw)` / `render_dt(raw)` (closes by `decide` **and** `rfl`); a
body/ctor/measure mutation is **provably unequal** (`¬ (… = …)` by `decide`) —
mutation-kill at the definition level.

### Cases (each = correct-closes + mutation-kill)

| Case | Fixture def | New constructor | Mutations killed |
|---|---|---|---|
| **A** | `tri(n) = if n=0 then 0 else n + tri(Int.toNat (n-1))` (`__root:9`, verbatim) | **`Ite`** | swap then/else · drop recursive call · `+`↔`-` opcode · drop `Int.toNat` on `(n-1)` |
| **B** | `tree_head(t) = match t {Leaf v => v, Node _ _ => 0}` (`__root:13`, verbatim) | **`Match`** | wrong arm value · swapped arms · **binder-id mismatch (§7 Q1)** · forgotten match |
| **B′** | `sum_tree(t) = match t {Leaf v => v as nat, Node l r => sum_tree l.deref + sum_tree r.deref}` (predicted — pruned) | `Match` + recursion + `Cast` + Box-`Deref` | drop recursive call · drop Box-`.deref` |
| **C** | `Tree = Leaf(Int) \| Node(Box Tree, Box Tree)` + `Tree.height` (`__base:22`/`:36`, verbatim) | `DtData` + **`TyBox`** field type; height MODELLED AS a `DefData` | ctor field-type wrong · ctor order swapped · wrong measure (Leaf⇒0) · drop recursive height call |
| **V** | `∀ k, k=k` and `g a b` (synthetic — no fixture body quantifies or multi-arg-calls) | **`Forall`** / **`AppN`** | binder-type mutated · args swapped · arg dropped |

`render_exp` extends the W6 core to the body constructors and stays **plainly
structural over the mutual group** (Match/AppN recurse through dedicated
`ArmList`/`ExprList` inductives, mirroring production's `RawExpList`
discipline), so the kernel reduces it under `decide`/`rfl` with **no
`WellFounded.fix`**.

## The frozen extended vocabulary (the W7b target)

The exact shapes W7b lands additively in `tactus-core/lib.rs` (Rust `enum`s
mirroring these Lean inductives; the W6 subset is unchanged, the `-- W7` lines
are the batched delta):

```lean
inductive TypData
  | int | nat | bool | named (id : Nat) | ref (inner : Nat)
  | box (inner : Nat)                                   -- W7: Box<T> field type (≠ ref)

mutual
inductive ExprData
  | atom | lit | litBool | cast | binOp | app | fieldProj | spanMark | letE | notE  -- W6
  | ite     (c t e : ExprData)                          -- W7: first-class if
  | matchE  (scrut : ExprData) (arms : ArmList)         -- W7: match
  | appN    (fn : Nat) (args : ExprList)                -- W7: multi-arg app
  | forallE (bid : Nat) (bty : TypData) (body : ExprData)   -- W7
  | existsE (bid : Nat) (bty : TypData) (body : ExprData)   -- W7
inductive MatchArm | arm (ctor : Nat) (binders : List Nat) (body : ExprData)
inductive ArmList  | nil | cons (hd : MatchArm) (tl : ArmList)
inductive ExprList | nil | cons (hd : ExprData) (tl : ExprList)
end

-- RawExp mirrors ExprData + type tags; adds ite/matchR/callN/forallR/existsR
-- (matchR/callN carry a result TypData for the arm-body/value coercion). NO
-- HasType (obligation-goal construct, not a body construct).

structure DefData  { name : Nat; params : List (Nat × TypData); ret : TypData; body : ExprData }
structure RawDef   { name : Nat; params : List (Nat × TypData); ret : TypData; body : RawExp }
structure CtorData { name : Nat; fields : List TypData }        -- positional field TYPES only
structure DtData   { name : Nat; ctors : List CtorData }
structure RawCtor  { name : Nat; fields : List TypData }
structure RawDt    { name : Nat; ctors : List RawCtor }
```

`render_def` copies the header (name/params/ret transcribed directly from VIR)
and renders the body via the extended `render_exp`; `render_dt` copies ctor
names + positional field types. `def_eq`/`dt_eq` (W7b) extend the W6 `expr_eq`
tag+projection idiom — the **arm-list** equality is the one novel step
(`arms_eq`, demonstrated here, §7 Q1).

## Results

- `lean probe15_w7a_defs.lean` → **rc=0**, ~4 s wall (pure core, no imports).
  ~30 `theorem`s: 6× correct-closes (`decide` + `rfl`) across A/B/B′/C(dt)/
  C(height); 15× mutation-kill; 3× vocab-completeness synthetics; 2× §7 Q1
  `arms_eq` (closes + kills).
- `#print axioms` on `render_exp`/`render_def`/`render_dt`/`arms_eq` + every
  correct-closes and kill → **"does not depend on any axioms"**. No
  `WellFounded.fix`, no `Classical` — pure kernel computation, exactly as the
  in-crate `decide` bridge requires.
- **Non-vacuity meta-check** (`run.sh`): asserting `¬ (render_def raw_tri =
  prod_tri_ok)` on the CORRECT def **fails** (rc=1). The `_kill` theorems test
  genuine inequality, not that `decide` rubber-stamps every negation.

## §7 open-question verdicts

1. **Match-arm binder-id discipline (Q1)** — **VERDICT: binder ids are part of
   structural equality, ride straight through `render`, and `decide` reduces
   `def_eq`/`arms_eq` over arm lists.** `B_th_binder_kill` shows a Leaf-arm
   binder-id mismatch (body unchanged) is a shape diff → kill. The production
   nat-returning `arms_eq` (match first arg, tag+projection on the second,
   recurse) `decide`s to 1/0 (`Q1_arms_eq_closes`/`Q1_arms_eq_kills`). W7b must
   intern arm-binder ids identically on both sides (the W6b atom-id invariant,
   one level up); wildcards (`_`) get a canonical positional id (`wildId`) so
   arity still matches — a Leaf arm binds one field even when unused.
2. **Height-fn inertness (Q2)** — **VERDICT: `def_eq` is syntactic; it never
   reduces the callee, so a body that *calls* `height` (even `height` itself)
   `decide`s fine.** `C_height_ok_decide` closes on a Match→Nat body whose Node
   arm is `App heightId (...)` twice — the callee is compared as an `App` node,
   never unfolded. So height's kernel-computability (W1.5 `termination_by
   structural`) is irrelevant to the *bridge* — only W5 would reduce it. This
   bites neither side.
3. **Multi-arg lowering (Q3)** — **VERDICT: flat arg list (`appN (fn) (args)`),
   reference matches production's currying by construction.** The mirror is
   flat; production's `lib.f a b` currying is a *rendering* detail. Caveat: the
   probe's `AppN` renders args straight (`render_list`), so per-arg
   Int→Nat coercion at the *expected param type* is **not yet modelled** — no
   fixture body is multi-arg, so this is deferred to W7c, which must carry a
   per-arg expected-type list (or require materialized `clip`s in the args).
   Flagged, not silently dropped.
4. **Datatype field-name vs positional (Q4)** — **VERDICT: `CtorData` carries
   positional field TYPES only; accessor names are a separate certifiable
   surface.** `Tree` mirrors to `Dt(treeTy, [Ctor(leaf,[int]), Ctor(node,[box
   treeTy, box treeTy])])`. Also: **`Box<T>` gets its own `TyBox` tag, NOT
   reused `TyRef`** — Box (owned heap) and Ref (`&T` borrow) deref identically
   but are semantically distinct; conflating them would let a Box/Ref field
   swap pass the bridge. `C_dt_wrong_kill` pins the positional-field-type check.

## Definition-level census (deliverable #6)

The fixture's spec fns + datatypes, each mapped to the body constructors it
uses and the W7b constructor it needs. (N4 was statement-level; W6a was
expression-leaf-level; **this is definition-level.**) Emitted defs read off
`TactusDefs_lib_exec__{root,base}.lean`; cert references from `out/lib/cert/`.

| Def | Body constructors | Needs (new) | Emitted? | Cert refs |
|---|---|---|---|---|
| `sq(x:nat)→nat = x*x` | BinOp | — (W6-complete) | yes (`__root`) | none (only `cast_shapes` proof) |
| `tri(n:nat)→nat` | **Ite**, BinOp(Eq/Add/Sub), App(rec), Cast, Lit, Atom | **Ite** | yes | `scope_shape`, `sum_to`, `tri_one` |
| `tree_head(t:Tree)→Int` | **Match**(2 arms), Atom, Lit | **Match** | yes | `head_exec` |
| `sum_tree(t:Tree)→nat` | **Match**, App(rec), FieldProj(Box), Cast, BinOp | **Match**, TyBox | **no — pruned** (no caller) | none |
| `Tree.height(s:Tree)→nat` | **Match**, App(self-rec), FieldProj(Box), BinOp, Lit | **Match**, TyBox | yes (`__base`, auto measure) | via `Tree` |
| `Point.height(_)→nat = 1` | Lit | — (W6-complete) | yes (`__base`, auto) | via `Point` |

| Datatype | Ctors (positional field types) | Needs (new) | Emitted? | Cert refs |
|---|---|---|---|---|
| `Tree` | `Leaf[Int]`, `Node[Box Tree, Box Tree]` | **TyBox** | yes (`__base`) | `head_exec` |
| `Point` (struct) | one ctor `[Int, Int]` (named `x`,`y` — accessor surface, §7 Q4) | — | yes (`__base`) | `mk_point` |
| `Set`, `Seq` | vstd machinery (height=1 stub) | — | out of scope |

**W7b constructor roadmap:** `Ite` → `tri` only. `Match` → `tree_head`,
`sum_tree`, `Tree.height`. `TyBox` → `Tree`, `sum_tree`, `Tree.height`.
`AppN` (multi-arg) and `Forall`/`Exists` → **no fixture body** (`fill_zeros`'s
`forall` is in *ensures* = goal-level `GoalData::All`, not a spec-fn body); the
tgt slice (W7d) exercises them for real, so they're frozen + synthetically
validated here.

## Assumptions / honesty

- **Monoculture caveat unchanged** (`DESIGN-W7-defslayer.md` §2): the
  independent `render_def` catches an *inconsistent* or *wrong* second lowering
  (Friction-class), not a rule both the emitter and the reference implement
  identically-wrong — that residual is W5.
- **`sum_tree` (Case B′) is a PREDICTED shape, not emitted-verified.** It is
  pruned from this fixture (no exec/proof fn calls it), so its DefData is the
  mechanical composition of the source with the `tree_head`/`Tree.height`
  patterns. Called out so W7d doesn't assume B′ was checked against real output;
  W7d should either add a caller or verify against a def-emit dump.
- **Datatype "render" is transcription, not decision.** Unlike expr bodies (a
  real coercion decision), `render_dt` is structural copy — the bridge teeth are
  the VIR-vs-LExpr transcription *diversity* (which the probe abstracts as two
  hand-written inputs). The kill is a wrong-transcribed field type / ctor.
- **`AppN` per-arg coercion deferred** (§7 Q3 caveat) — no fixture body is
  multi-arg; W7c must carry expected param types for AppN.
- **`u64` renders as `Int` in def signatures** (`tree_head : Int`), matching the
  emitted output — the probe models ret/field `u64`→`.int` faithfully.

## Reproduce

    LEAN=<lean-v4.25.0> bash probe-w0/probe15_w7a_defs/run.sh

## Hand-off to W7b

The `TypData`(+`box`) / `ExprData`(+`ite`/`matchE`/`appN`/`forallE`/`existsE`)
/ `DefData` / `RawDef` / `DtData` / `CtorData` / `render_def` / `render_dt`
shapes above are **frozen**. W7b lands them (+ `expr_size`/arm-list structural
measures, `#[verifier::structural_decreases]`, and the nat-returning
`def_eq`/`dt_eq`/`arms_eq` extending W6's `expr_eq` idiom) in
`tactus-core/lib.rs` as **one batched cache-churning edit** (base-hash change ⇒
whole-crate re-verify + olean re-emit — the caching doc's "datatypes are
all-or-nothing"). Keep probe9/13/14 green. The probe is the shape spec.
