/- W6a probe (board bootstrap-20): validate the D2 "deepen-then-diff" mechanic on
   ONE cast-class expression, standalone, with ZERO risk to `tactus-core`.

   Parent design: DESIGN-W6-stageB.md (§2 the D2 fork, §2.1 hybrid leaf, §3.1 the
   exact decision to reimplement). Target bug class: DECISION-cast-rendering.md
   (Friction 2 — the `as nat` coercion applied at one site but not a
   structurally-identical one).

   What this probe freezes for W6b:
     * the `ExprData` hybrid leaf (structural cast/binop/app/fieldproj/span
       constructors + an `Atom (id)` terminal that CARRIES its interned id — the
       local-model safety condition, so a *forgotten* cast is a shape difference),
     * the minimal `TypData` (Int vs Nat is all the cast decision needs; + Ref),
     * an INDEPENDENT reference renderer `render_exp : RawExp → ExprData` that
       reimplements the coercion DECISION from the raw SST's type tags — it does
       NOT reuse production's renderer, which is the whole point (§1 corollary:
       "if both sides call to_lean_sst_expr you only verify the renderer is
       deterministic").

   The bridge in each case: the CORRECT production `ExprData` must equal
   `render_exp(raw)` (closes by `decide` AND `rfl`), and a coercion-DROPPED /
   inconsistently-coerced production shape must be PROVABLY unequal (mutation-kill
   at expression level — `¬ (… = …)` by `decide`).

   Pure Lean core: no Mathlib, no prelude, no tactus-core oleans. Run with just
   `lean probe12_w6a_castleaf.lean`. -/

-- ── mirror types (the shape W6b lands in tactus-core) ───────────────────────

/-- Minimal type mirror. The cast decision only needs `int` (a uN, renders Lean
    `Int`) vs `nat` (renders Lean `Nat`); `bool` is the type of comparisons/`Eq`
    (which are deliberately NOT arith-coercion sites — DECISION §"Scope limits");
    `named`/`ref` cover user datatypes and `&`-params (the `.deref` class). -/
inductive TypData where
  | int
  | nat
  | bool
  | named (id : Nat)
  | ref   (inner : Nat)
deriving DecidableEq, Repr

inductive CastKind where
  | intToNat   -- `Int.toNat` (the materialized `as nat`)
  | natToInt   -- `Int.ofNat` (the reverse; present for completeness)
deriving DecidableEq, Repr

/-- The HYBRID leaf. Structural cast/coerce/binop/app/fieldproj/span decisions are
    mirrored; terminal atoms (var reads, names) stay interned `id : Nat`. Atoms
    carry their id so a forgotten cast (`atom 1` vs `cast intToNat (atom 1)`) is a
    shape difference the bridge catches (§2.1 safety condition). -/
inductive ExprData where
  | atom      (id : Nat)                        -- var read / spec-fn or type name
  | lit       (val : Int)
  | cast      (k : CastKind) (e : ExprData)     -- Int.toNat / Int.ofNat node
  | binOp     (op : Nat) (l r : ExprData)
  | app       (fn : Nat) (arg : ExprData)       -- lib.tri (…), lib.tree_head (…)
  | fieldProj (e : ExprData) (field : Nat)      -- `.deref`, `.x`, `.1`, …
  | spanMark  (loc : Nat) (e : ExprData)        -- `/- @rust:loc -/ <e>` wrapper
deriving DecidableEq, Repr

/-- The NEW independent input: the raw SST expression tree, mirrored to data and
    type-annotated. NOT rendered through production's `to_lean_sst_expr`. This is
    what gives the bridge implementation diversity. -/
inductive RawExp where
  | var    (id : Nat) (ty : TypData)                       -- typed variable read
  | lit    (val : Int) (ty : TypData)
  | clip   (target : TypData) (e : RawExp)                 -- an explicit `as` cast (Verus Clip)
  | binop  (op : Nat) (ty : TypData) (l r : RawExp)        -- ty = op RESULT type
  | call   (fn : Nat) (ret : TypData) (arg : RawExp) (argTy : TypData)
  | deref  (e : RawExp)                                    -- `*t` on a `&`-param
  | span   (loc : Nat) (e : RawExp)
deriving DecidableEq, Repr

-- ── the reference renderer (INDEPENDENT reimplementation of the decision) ────

/-- The rendered type a raw node presents to its parent. Crucially: a `clip target`
    presents `target` (not its operand's type) — that is how an elided-clip operand
    still reads `int` to the enclosing op, and a materialized one reads `nat`. -/
def typeOf : RawExp → TypData
  | .var _ ty        => ty
  | .lit _ ty        => ty
  | .clip target _   => target
  | .binop _ ty _ _  => ty
  | .call _ ret _ _  => ret
  | .deref e         => match typeOf e with
                        | .ref inner => .named inner
                        | t          => t
  | .span _ e        => typeOf e

/-- The coercion PREDICATE (DECISION §"The fix that landed"): an operand that
    renders `Int` under an op/target that renders `Nat` needs the `Int.toNat` the
    `as nat` denotes. This is the same predicate the call-arg path uses. -/
def needs_nat_coercion (operand op_result : TypData) : Bool :=
  operand == TypData.int && op_result == TypData.nat

@[inline] def coerceIf (b : Bool) (e : ExprData) : ExprData :=
  if b then .cast .intToNat e else e

/-- Interned field id for `.deref` (the `&`-param dereference field). -/
def derefField : Nat := 0

/-- `render_exp` reimplements the cast/coercion decision UNIFORMLY from the type
    tags. The recursion is plainly structural (each call is on a subterm), so the
    kernel reduces it under `decide`/`rfl` (no `WellFounded.fix`). -/
def render_exp : RawExp → ExprData
  | .var id _       => .atom id
  | .lit v _        => .lit v
  | .clip target e  =>
      -- explicit `as` cast: materialize `Int.toNat` iff there is a real Int→Nat gap
      let inner := render_exp e
      coerceIf (needs_nat_coercion (typeOf e) target) inner
  | .binop op ty l r =>
      -- nat-typed arith op: each Int-rendering operand is materialized (Friction-2
      -- site). For a `bool`-typed op (cmp/Eq) `needs_nat_coercion _ bool = false`,
      -- so operands are left as-is — DECISION §"Scope limits".
      let l' := coerceIf (needs_nat_coercion (typeOf l) ty) (render_exp l)
      let r' := coerceIf (needs_nat_coercion (typeOf r) ty) (render_exp r)
      .binOp op l' r'
  | .call fn _ret arg argTy =>
      -- call-arg coercion: same predicate, target is the expected param type
      let a := coerceIf (needs_nat_coercion (typeOf arg) argTy) (render_exp arg)
      .app fn a
  | .deref e        => .fieldProj (render_exp e) derefField
  | .span loc e     => .spanMark loc (render_exp e)

-- ── interned-id / opcode constants (readability only; concrete Nats) ─────────

def rId  : Nat := 1   -- var `r`
def nId  : Nat := 2   -- var `n`
def xId  : Nat := 3   -- var `x`
def tId  : Nat := 4   -- var `t : &Tree`
def eqOp : Nat := 0
def mulOp : Nat := 1
def triId : Nat := 10        -- `lib.tri`
def treeHeadId : Nat := 11   -- `lib.tree_head`
def treeTy : Nat := 100      -- `lib.Tree`

/- ════════════════════════════════════════════════════════════════════════════
   CASE A — the real `sum_to` postcond leaf:  Int.toNat r = lib.tri (Int.toNat n)
   (ensures `r as nat == tri(n as nat)`; verbatim fixture leaf 6/7/21).
   Exercises: BinOp(Eq), explicit `as nat` clip (LHS), call-arg cast (RHS), App.
   ════════════════════════════════════════════════════════════════════════════ -/

/-- raw SST: `(r : u64) as nat  ==  tri((n : u64) as nat)`. The `==` is a
    `bool`-typed BinOp; both casts are explicit source `clip`s to `nat`. -/
def raw_sum_to : RawExp :=
  .binop eqOp .bool
    (.clip .nat (.var rId .int))
    (.call triId .nat (.clip .nat (.var nId .int)) .nat)

/-- CORRECT production `ExprData` = the real leaf `Int.toNat r = lib.tri (Int.toNat n)`. -/
def prod_sum_to_ok : ExprData :=
  .binOp eqOp
    (.cast .intToNat (.atom rId))
    (.app triId (.cast .intToNat (.atom nId)))

/-- MUTATED production: the LHS `as nat` was dropped (Verus elides `r as nat` on a
    bare var — exactly the Friction-2 inconsistency; `r` rendered `Int`, not `ℕ`). -/
def prod_sum_to_dropped : ExprData :=
  .binOp eqOp
    (.atom rId)                                    -- BUG: forgotten Int.toNat
    (.app triId (.cast .intToNat (.atom nId)))

-- correct shape CLOSES (both decide and rfl):
theorem A_ok_decide : render_exp raw_sum_to = prod_sum_to_ok := by decide
theorem A_ok_rfl    : render_exp raw_sum_to = prod_sum_to_ok := by rfl
-- dropped-coercion shape is PROVABLY unequal (mutation-kill):
theorem A_dropped_kill : ¬ (render_exp raw_sum_to = prod_sum_to_dropped) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE B — the DERIVED-coercion case (the genuinely interesting one):
   `(x as nat) * x` where Verus ELIDED both inner clips, leaving bare `x : u64`
   operands under a `nat`-typed `Mul`. The reference must INSERT both `Int.toNat`s
   purely from the type tags — no explicit source cast to copy. This is where D2's
   implementation diversity is real, and where inconsistent production application
   (Friction 2) diverges. (DECISION §"The fix that landed" / pinned test
   `test_exec_arith_operand_as_nat_materializes`.)
   ════════════════════════════════════════════════════════════════════════════ -/

/-- raw SST: `Mul : nat` with two bare `x : u64` operands (source clips elided). -/
def raw_arith : RawExp :=
  .binop mulOp .nat (.var xId .int) (.var xId .int)

/-- CORRECT: reference derives BOTH casts → `Int.toNat x * Int.toNat x`. -/
def prod_arith_ok : ExprData :=
  .binOp mulOp (.cast .intToNat (.atom xId)) (.cast .intToNat (.atom xId))

/-- MUTATED (Friction 2 exactly): production materialized the cast at ONE operand
    but not the structurally-identical other. -/
def prod_arith_inconsistent : ExprData :=
  .binOp mulOp (.cast .intToNat (.atom xId)) (.atom xId)

theorem B_ok_decide : render_exp raw_arith = prod_arith_ok := by decide
theorem B_ok_rfl    : render_exp raw_arith = prod_arith_ok := by rfl
theorem B_inconsistent_kill : ¬ (render_exp raw_arith = prod_arith_inconsistent) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE C — the `.deref` (FieldProj) class:  lib.tree_head (t.deref)  on t : &Tree
   (head_exec's `r == tree_head(*t)`; the row-3 ref-deref subclass, bootstrap-18).
   Exercises the FieldProj constructor + a dropped-deref mutation-kill.
   ════════════════════════════════════════════════════════════════════════════ -/

/-- raw SST: `tree_head(*t)` — `*t` is a deref of `t : &Tree` (Ref treeTy). -/
def raw_deref : RawExp :=
  .call treeHeadId (.named treeTy) (.deref (.var tId (.ref treeTy))) (.named treeTy)

/-- CORRECT: `lib.tree_head (t.deref)`. -/
def prod_deref_ok : ExprData :=
  .app treeHeadId (.fieldProj (.atom tId) derefField)

/-- MUTATED: production forgot the `.deref` (passed the `&Tree` where a `Tree` is
    expected — the head_exec bug before bootstrap-18's binder-aware ctx fix). -/
def prod_deref_dropped : ExprData :=
  .app treeHeadId (.atom tId)

theorem C_ok_decide : render_exp raw_deref = prod_deref_ok := by decide
theorem C_ok_rfl    : render_exp raw_deref = prod_deref_ok := by rfl
theorem C_dropped_kill : ¬ (render_exp raw_deref = prod_deref_dropped) := by decide

/- ── negative control: the reference is NOT vacuously permissive ──
   A cmp/`Eq` op does NOT coerce its operands (DECISION scope limit): a comparison
   `x < (x as nat)` keeps the LHS `x` bare. This pins that `needs_nat_coercion`
   fires ONLY on nat targets — if it fired on `bool` too, this would be wrong. -/
def raw_cmp : RawExp :=
  .binop eqOp .bool (.var xId .int) (.clip .nat (.var xId .int))
def prod_cmp_ok : ExprData :=
  .binOp eqOp (.atom xId) (.cast .intToNat (.atom xId))   -- LHS bare, RHS cast
theorem D_cmp_no_spurious_coercion : render_exp raw_cmp = prod_cmp_ok := by decide

-- ── axiom hygiene: the whole mechanic is pure kernel computation ─────────────
#print axioms render_exp
#print axioms A_ok_decide
#print axioms A_dropped_kill
#print axioms B_inconsistent_kill

#eval "W6a probe: all bridges elaborated (see rc); axioms printed above."
