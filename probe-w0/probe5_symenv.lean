/- W0 pre-probe P5: goals REFERENCE USER SPEC FNS and user datatypes. The
   denotation can't know them in advance — it takes a symbol environment.
   Question: does the rfl-bridge survive environment lookups, i.e. does
   `gdenote fenv g = <rendered form naming the real fns>` still close by rfl
   when fenv is a concrete match-literal? Also: a user datatype as an opaque
   quantifier domain via a type environment (the dependent bit that will have
   to live in hand-Lean, not tactus). -/

-- "user" spec fns (stand-ins for emitted crate-defs)
def myDouble (x : Int) : Int := x + x
def myAbs (x : Int) : Int := if x < 0 then -x else x

-- "user" datatype
inductive Color where | red | green | blue deriving DecidableEq
def colorRank : Color → Int | .red => 0 | .green => 1 | .blue => 2

-- typed goal syntax with fn symbols and one opaque type slot
inductive TExpr where
  | tvar  : Nat → TExpr
  | tlit  : Int → TExpr
  | tadd  : TExpr → TExpr → TExpr
  | tcall : Nat → TExpr → TExpr        -- fn symbol index, one Int arg
deriving DecidableEq, Repr

inductive TGoal where
  | tforallI : TGoal → TGoal            -- ∀ (x : Int)
  | tforallU : TGoal → TGoal            -- ∀ (u : U)  (opaque user type slot)
  | timpLe   : TExpr → TExpr → TGoal → TGoal
  | teq      : TExpr → TExpr → TGoal
  | tequ     : Nat → TExpr → TGoal      -- ucall applied to the u-var == expr
deriving Repr

structure SymEnv where
  U : Type                              -- the opaque user type
  ifns : Nat → (Int → Int)              -- Int-fn symbols
  ufns : Nat → (U → Int)                -- U-consuming fn symbols

def edenote (env : SymEnv) (ienv : List Int) : TExpr → Int
  | .tvar i    => ienv.getD i 0
  | .tlit n    => n
  | .tadd a b  => edenote env ienv a + edenote env ienv b
  | .tcall f a => env.ifns f (edenote env ienv a)

def gdenote (env : SymEnv) (ienv : List Int) (uenv : List env.U) : TGoal → Prop
  | .tforallI g    => ∀ x : Int, gdenote env (x :: ienv) uenv g
  | .tforallU g    => ∀ u : env.U, gdenote env ienv (u :: uenv) g
  | .timpLe a b g  => edenote env ienv a ≤ edenote env ienv b → gdenote env ienv uenv g
  | .teq a b       => edenote env ienv a = edenote env ienv b
  | .tequ f a      => (match uenv with
                       | u :: _ => env.ufns f u
                       | []     => 0) = edenote env ienv a

-- the per-crate environment literal (what the emitter would generate)
def crateEnv : SymEnv where
  U := Color
  ifns | 0 => myDouble | 1 => myAbs | _ => id
  ufns | 0 => colorRank | _ => fun _ => 0

-- ∀ (x : Int), 0 ≤ x → myDouble x = x + x   and   ∀ (c : Color), colorRank c = colorRank c
def g1 : TGoal :=
  .tforallI (.timpLe (.tlit 0) (.tvar 0)
    (.teq (.tcall 0 (.tvar 0)) (.tadd (.tvar 0) (.tvar 0))))

def g2 : TGoal := .tforallU (.tequ 0 (.tcall 1 (.tlit (-3))))

-- rendered forms (as the production emitter pretty-prints them, naming real fns)
def rendered1 : Prop := ∀ x : Int, 0 ≤ x → myDouble x = x + x
def rendered2 : Prop := ∀ c : Color, colorRank c = myAbs (-3)

example : gdenote crateEnv [] [] g1 = rendered1 := by rfl
example : gdenote crateEnv [] [] g2 = rendered2 := by rfl
