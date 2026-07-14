/- W7-AppN probe (board bootstrap-34): freeze the per-arg-`TypData` `RawList`
   vocabulary for multi-argument application (`CallN` / `AppN`), standalone, with
   ZERO risk to `tactus-core`.

   Parent thread: bootstrap-28 and -29 closed the fixture-covering def+datatype body
   surface but LEFT multi-arg `CallN`/`AppN` fail-loud (the fixture callers `tri`,
   `sq`, `tree_head`, `sum_tree` are all nullary/single-arg, so nothing forced it).
   W7a's probe (probe15) already froze `RawList`/`render_list` — but in the OLD
   shape `RawList.cons (hd) (tl)`, no per-arg type, and `render_list` renders each
   arg with NO coercion. That is exactly the current `tactus-core` state (lib.rs
   `RawList::Cons(Box<RawExp>, Box<RawList>)`, `render_list` = plain `render_exp`).

   WHY that shape is wrong for a FAITHFUL multi-arg render (the deferral reason,
   Danielle-endorsed): Verus inserts a per-argument `Int.toNat` / `&`-deref based
   on the CALLEE's parameter type for THAT position. The single-arg `Call` arm
   already does this — it carries `argTy` and applies `coerce_if(needs_nat_coercion
   …) ∘ deref_if(needs_ref_deref …)` (lib.rs `render_exp` Call arm). A 2-arg call
   where position 0 expects `nat` and position 1 expects `int` needs the cast on
   arg 0 but NOT arg 1 — a single shared type cannot express that. So each list
   cell must carry its own expected type.

   What this probe FREEZES for the batched `tactus-core` edit (bootstrap-34 step 2):
     * the NEW `RawList` shape `cons (hd : RawExp) (argTy : TypData) (tl : RawList)`
       — one expected-param-type per argument (the additive datatype field that
       forces the base-hash / whole-crate re-verify);
     * `render_list` that reproduces the single-arg `Call` arm's chain PER ARG:
       `coerce_if(needs_nat_coercion(type_of hd, argTy)) ∘
        deref_if(needs_ref_deref(type_of hd))` — same order, same predicates, so
       the eventual `render_list` is literally the `Call` arm generalized to a list;
     * the `CallN` → `AppN(fn, render_list args)` bridge.

   The bridge in each case: the CORRECT production `ExprData` (what the transcriber
   `lexpr_to_exprdata` must emit) equals `render_exp(raw)` — closes by `decide` AND
   `rfl` — and any per-arg coercion DROPPED / mis-placed / spuriously-added is
   PROVABLY unequal (`¬ (… = …)` by `decide`). The per-arg heterogeneous case
   (Case B) is the load-bearing one: it is closeable ONLY because each cell carries
   its own `argTy`.

   Pure Lean core: no Mathlib, no prelude, no tactus-core oleans. Run with just
   `lean probe18_appn.lean` (or `run.sh`). -/

-- ── mirror types (the shape the batched edit lands in tactus-core) ──────────

/-- Minimal type mirror (same order/tags as `tactus-core` `td_tag`: int=0, nat=1,
    bool=2, named=3, ref=4). The multi-arg coercion decision needs `int`↔`nat`
    (the `Int.toNat` gap) and `ref` (the `&`-param `.deref`). -/
inductive TypData where
  | int
  | nat
  | bool
  | named (id : Nat)
  | ref   (inner : Nat)
deriving DecidableEq, Repr

inductive CastKind where
  | intToNat
  | natToInt
deriving DecidableEq, Repr

-- ExprData / ExprList: the production (transcriber) surface. `appN` takes an
-- ExprList (a genuine multi-arg spine, unlike single-arg `app`). Mutually
-- inductive because `appN` holds an `ExprList` of `ExprData`.
mutual
inductive ExprData where
  | atom      (id : Nat)
  | lit       (val : Int)
  | cast      (k : CastKind) (e : ExprData)
  | binOp     (op : Nat) (l r : ExprData)
  | app       (fn : Nat) (arg : ExprData)          -- single-arg (already frozen)
  | appN      (fn : Nat) (args : ExprList)         -- W7: multi-arg spine
  | fieldProj (e : ExprData) (field : Nat)
deriving DecidableEq, Repr
inductive ExprList where
  | nil
  | cons (hd : ExprData) (tl : ExprList)
deriving DecidableEq, Repr
end

-- RawExp / RawList: the INDEPENDENT reference (VIR-transcribed) surface. The
-- freeze: `RawList.cons` now carries `argTy : TypData` — one expected-param-type
-- per position. `callN` holds a `RawList`.
mutual
inductive RawExp where
  | var    (id : Nat) (ty : TypData)
  | lit    (val : Int) (ty : TypData)
  | clip   (target : TypData) (e : RawExp)
  | binOp  (op : Nat) (ty : TypData) (l r : RawExp)
  | call   (fn : Nat) (ret : TypData) (arg : RawExp) (argTy : TypData)   -- single-arg
  | callN  (fn : Nat) (ret : TypData) (args : RawList)                   -- W7: multi-arg
  | deref  (e : RawExp)
deriving DecidableEq, Repr
inductive RawList where
  | nil
  | cons (hd : RawExp) (argTy : TypData) (tl : RawList)                  -- ← per-arg TypData
deriving DecidableEq, Repr
end

-- ── the reference renderer (INDEPENDENT reimplementation of the decision) ────

/-- The rendered type a raw node presents to its parent. `callN` presents its
    carried return type in one step (no recursion into args) — parallel to `call`. -/
def type_of : RawExp → TypData
  | .var _ ty        => ty
  | .lit _ ty        => ty
  | .clip target _   => target
  | .binOp _ ty _ _  => ty
  | .call _ ret _ _  => ret
  | .callN _ ret _   => ret
  | .deref e         => match type_of e with
                        | .ref inner => .named inner
                        | t          => t

/-- Int→Nat coercion predicate (the `as nat` gap). Same as the call-arg path. -/
def needs_nat_coercion (operand op_result : TypData) : Bool :=
  operand == TypData.int && op_result == TypData.nat

@[inline] def coerceIf (b : Bool) (e : ExprData) : ExprData :=
  if b then .cast .intToNat e else e

/-- `&`-param deref predicate: an arg whose OWN type is `ref` gets a `.deref`
    (spec fns never take `&T`, so the ref tag on the arg is the whole signal —
    `argTy` is the pointee). Parallel to `needs_ref_deref` in tactus-core. -/
def needs_ref_deref (operand : TypData) : Bool :=
  match operand with | .ref _ => true | _ => false

def derefField : Nat := 0

@[inline] def derefIf (b : Bool) (e : ExprData) : ExprData :=
  if b then .fieldProj e derefField else e

-- `render_exp` / `render_list`: mutually recursive, structural over the mutual
-- group (every recursive call is on a subterm), so the kernel reduces them
-- under `decide` / `rfl`. The `callN` arm delegates to `render_list`; each list
-- cell applies the SAME coerce-then-deref chain the single-arg `call` arm does.
mutual
def render_exp : RawExp → ExprData
  | .var id _        => .atom id
  | .lit v _         => .lit v
  | .clip target e   => coerceIf (needs_nat_coercion (type_of e) target) (render_exp e)
  | .binOp op ty l r =>
      .binOp op
        (coerceIf (needs_nat_coercion (type_of l) ty) (render_exp l))
        (coerceIf (needs_nat_coercion (type_of r) ty) (render_exp r))
  | .call fn _ret arg argTy =>
      -- single-arg: coerce THEN deref (the exact order `render_list` copies).
      .app fn (derefIf (needs_ref_deref (type_of arg))
                (coerceIf (needs_nat_coercion (type_of arg) argTy) (render_exp arg)))
  | .callN fn _ret args => .appN fn (render_list args)
  | .deref e         => .fieldProj (render_exp e) derefField
def render_list : RawList → ExprList
  | .nil            => .nil
  | .cons h argTy t =>
      -- PER ARG, the single-arg `call` chain: coerce at the expected type, then
      -- deref if the arg is a `&`-param. This is the whole point of the per-arg
      -- `argTy` — position 0 and position 1 can decide differently (Case B).
      .cons (derefIf (needs_ref_deref (type_of h))
              (coerceIf (needs_nat_coercion (type_of h) argTy) (render_exp h)))
            (render_list t)
end

-- ── interned-id / opcode constants (readability only; concrete Nats) ─────────

def nId : Nat := 2   -- var `n : u64`
def xId : Nat := 3   -- var `x : u64`
def tId : Nat := 4   -- var `t : &Tree`
def mId : Nat := 5   -- var `m : u64`
def kId : Nat := 6   -- var `k : int`  (a genuinely-int param arg)
def f2Id : Nat := 20 -- a 2-arg spec fn (nat, nat)
def gId  : Nat := 21 -- a 2-arg spec fn (used with varying param types)
def hId  : Nat := 22 -- a 2-arg spec fn (Tree, int)  — the ref-deref case
def f3Id : Nat := 23 -- a 3-arg spec fn (int, nat, nat)
def treeTy : Nat := 100

/- ════════════════════════════════════════════════════════════════════════════
   CASE A — plain multi-arg, BOTH args derive an `Int.toNat`:  f(n, m)  where
   n, m : u64 are bare (source clips elided) and both params expect `nat`. The
   reference must INSERT both casts purely from the per-arg `argTy`. This is the
   multi-arg generalization of W6a Case B; the kill drops the 2nd arg's cast.
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_A : RawExp :=
  .callN f2Id .nat
    (.cons (.var nId .int) .nat
      (.cons (.var mId .int) .nat .nil))

def prod_A_ok : ExprData :=
  .appN f2Id
    (.cons (.cast .intToNat (.atom nId))
      (.cons (.cast .intToNat (.atom mId)) .nil))

def prod_A_dropped : ExprData :=            -- BUG: 2nd arg's Int.toNat forgotten
  .appN f2Id
    (.cons (.cast .intToNat (.atom nId))
      (.cons (.atom mId) .nil))

theorem A_ok_decide : render_exp raw_A = prod_A_ok := by decide
theorem A_ok_rfl    : render_exp raw_A = prod_A_ok := by rfl
theorem A_dropped_kill : ¬ (render_exp raw_A = prod_A_dropped) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE B — the LOAD-BEARING per-arg-heterogeneous case:  g(n, k)  where param 0
   expects `nat` (bare u64 `n` → Int.toNat) but param 1 expects `int` (`k` stays
   bare). This is closeable ONLY because each `RawList` cell carries its own
   `argTy` — a single shared type could not coerce arg 0 while leaving arg 1. Two
   kills: coercing the WRONG arg, and coercing BOTH (what a uniform-type render
   would do).
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_B : RawExp :=
  .callN gId .nat
    (.cons (.var nId .int) .nat        -- param 0 expects nat  → coerce
      (.cons (.var kId .int) .int .nil))  -- param 1 expects int  → leave bare

def prod_B_ok : ExprData :=
  .appN gId
    (.cons (.cast .intToNat (.atom nId))
      (.cons (.atom kId) .nil))

def prod_B_wrong_arg : ExprData :=          -- BUG: coerced arg 1, not arg 0
  .appN gId
    (.cons (.atom nId)
      (.cons (.cast .intToNat (.atom kId)) .nil))

def prod_B_both : ExprData :=               -- BUG: coerced BOTH (uniform-type render)
  .appN gId
    (.cons (.cast .intToNat (.atom nId))
      (.cons (.cast .intToNat (.atom kId)) .nil))

theorem B_ok_decide       : render_exp raw_B = prod_B_ok := by decide
theorem B_ok_rfl          : render_exp raw_B = prod_B_ok := by rfl
theorem B_wrong_arg_kill  : ¬ (render_exp raw_B = prod_B_wrong_arg) := by decide
theorem B_both_kill       : ¬ (render_exp raw_B = prod_B_both) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE C — a `&`-param DEREF arg in list position:  h(*t, x)  on t : &Tree. The
   per-arg chain must auto-`.deref` the ref arg (position 0) and leave the other
   bare (position 1 expects int, x : int). The kill forgets the deref.
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_C : RawExp :=
  .callN hId (.named treeTy)
    (.cons (.var tId (.ref treeTy)) (.named treeTy)   -- arg is &Tree → deref; argTy = Tree
      (.cons (.var xId .int) .int .nil))              -- int param → bare

def prod_C_ok : ExprData :=
  .appN hId
    (.cons (.fieldProj (.atom tId) derefField)
      (.cons (.atom xId) .nil))

def prod_C_dropped : ExprData :=            -- BUG: passed &Tree where Tree expected
  .appN hId
    (.cons (.atom tId)
      (.cons (.atom xId) .nil))

theorem C_ok_decide    : render_exp raw_C = prod_C_ok := by decide
theorem C_ok_rfl       : render_exp raw_C = prod_C_ok := by rfl
theorem C_dropped_kill : ¬ (render_exp raw_C = prod_C_dropped) := by decide

/- ════════════════════════════════════════════════════════════════════════════
   CASE D — length-3 spine + a NESTED `callN` argument:  f3(x, g(n), m)  with
   params (int, nat, nat). Exercises `render_list` recursion past length 2 AND
   the mutual recursion (arg 1 is itself a `callN`, whose own arg coerces). Kill:
   drop the INNER nested coercion (Int.toNat n) — must still be caught.
   ════════════════════════════════════════════════════════════════════════════ -/

def raw_D : RawExp :=
  .callN f3Id .nat
    (.cons (.var xId .int) .int                       -- arg 0: int param → bare
      (.cons (.callN gId .nat                          -- arg 1: nested callN (returns nat)
                (.cons (.var nId .int) .nat .nil)) .nat  --   nat param → coerce inner n
        (.cons (.var mId .int) .nat .nil)))            -- arg 2: nat param → coerce m

def prod_D_ok : ExprData :=
  .appN f3Id
    (.cons (.atom xId)
      (.cons (.appN gId (.cons (.cast .intToNat (.atom nId)) .nil))
        (.cons (.cast .intToNat (.atom mId)) .nil)))

def prod_D_inner_dropped : ExprData :=      -- BUG: inner nested Int.toNat n forgotten
  .appN f3Id
    (.cons (.atom xId)
      (.cons (.appN gId (.cons (.atom nId) .nil))
        (.cons (.cast .intToNat (.atom mId)) .nil)))

theorem D_ok_decide        : render_exp raw_D = prod_D_ok := by decide
theorem D_ok_rfl           : render_exp raw_D = prod_D_ok := by rfl
theorem D_inner_dropped_kill : ¬ (render_exp raw_D = prod_D_inner_dropped) := by decide

/- ── negative control: `render_list` is NOT vacuously coercive ──
   A 2-arg call whose BOTH params expect `int`, with bare int args, must leave
   both args bare. If `render_list` coerced regardless of `argTy`, this would be
   wrong — pins that per-arg `needs_nat_coercion` fires only on a nat expected
   type. (Mirror of W6a's D_cmp negative control, in list position.) -/
def raw_E : RawExp :=
  .callN gId .int
    (.cons (.var nId .int) .int
      (.cons (.var mId .int) .int .nil))
def prod_E_ok : ExprData :=
  .appN gId (.cons (.atom nId) (.cons (.atom mId) .nil))
theorem E_no_spurious_coercion : render_exp raw_E = prod_E_ok := by decide

-- ── axiom hygiene: the whole mechanic is pure kernel computation ─────────────
#print axioms render_exp
#print axioms render_list
#print axioms A_ok_decide
#print axioms B_ok_decide
#print axioms B_wrong_arg_kill
#print axioms B_both_kill
#print axioms C_dropped_kill
#print axioms D_inner_dropped_kill

#eval "W7-AppN probe: all AppN/CallN bridges elaborated (see rc); axioms printed above."
