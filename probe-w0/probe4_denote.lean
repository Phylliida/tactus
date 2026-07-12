/- W0 pre-probe P4: the DENOTATION bridge (Bridge-R / the W5 soundness path).
   Typed goal syntax quantifying over real Int; structural denotation into
   Prop; `rfl` against the hand-elaborated ("production-rendered") form.
   Tests: binder recursion, env lookup reduction under a bound variable,
   Int literal elaboration agreement, imp/conj mapping. -/

inductive TExpr where
  | tvar : Nat → TExpr          -- de Bruijn index into env
  | tlit : Int → TExpr
  | tadd : TExpr → TExpr → TExpr
deriving DecidableEq, Repr

inductive TGoal where
  | tforall : TGoal → TGoal               -- ∀ (x : Int), …
  | timpLe  : TExpr → TExpr → TGoal → TGoal   -- (a ≤ b) → …
  | tconj   : TGoal → TGoal → TGoal
  | teq     : TExpr → TExpr → TGoal       -- a = b
deriving Repr

def edenote (env : List Int) : TExpr → Int
  | .tvar i   => env.getD i 0
  | .tlit n   => n
  | .tadd a b => edenote env a + edenote env b

def gdenote (env : List Int) : TGoal → Prop
  | .tforall g    => ∀ x : Int, gdenote (x :: env) g
  | .timpLe a b g => edenote env a ≤ edenote env b → gdenote env g
  | .tconj a b    => gdenote env a ∧ gdenote env b
  | .teq a b      => edenote env a = edenote env b

-- ∀ x, 0 ≤ x → (x + 0 = x ∧ ∀ y, y ≤ x → y + 1 = y + 1)
def g1 : TGoal :=
  .tforall (.timpLe (.tlit 0) (.tvar 0)
    (.tconj
      (.teq (.tadd (.tvar 0) (.tlit 0)) (.tvar 0))
      (.tforall (.timpLe (.tvar 0) (.tvar 1)
        (.teq (.tadd (.tvar 0) (.tlit 1)) (.tadd (.tvar 0) (.tlit 1)))))))

-- The "production-rendered" statement, as the emitter would pretty-print it:
def rendered1 : Prop :=
  ∀ x : Int, 0 ≤ x → (x + 0 = x ∧ ∀ y : Int, y ≤ x → y + 1 = y + 1)

-- THE BRIDGE (Bridge-R shape): denotation ≡ rendered, definitionally
example : gdenote [] g1 = rendered1 := by rfl

-- and the statement form usable as the authoritative Stmts def:
example : gdenote [] g1 ↔ rendered1 := Iff.rfl
