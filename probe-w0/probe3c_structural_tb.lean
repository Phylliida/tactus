/- W0 pre-probe P3c: `termination_by structural` — the candidate emitter
   feature. Same def as probe3's WF twin, but compiled structurally via the
   explicit annotation. Expect: decide + rfl both work (probe1 behavior),
   and no axioms in the closure (vs. Tactus.heightLt under the current
   datatype-measure emission). -/

inductive PExpr where
  | ivar : Nat → PExpr
  | ilit : Int → PExpr
  | le   : PExpr → PExpr → PExpr
deriving DecidableEq, Repr

inductive PStm where
  | assert : PExpr → PStm
  | assume : PExpr → PStm
  | seq    : PStm → PStm → PStm
deriving DecidableEq, Repr

inductive GoalAst where
  | atom : PExpr → GoalAst
  | imp  : PExpr → GoalAst → GoalAst
  | conj : GoalAst → GoalAst → GoalAst
  | gtrue : GoalAst
deriving DecidableEq, Repr

def refWpS : PStm → GoalAst → GoalAst
  | .assert e,   g => .conj (.atom e) (.imp e g)
  | .assume e,   g => .imp e g
  | .seq a b,    g => refWpS a (refWpS b g)
termination_by structural s _ => s

def prog : PStm := .seq (.assert (.le (.ilit 0) (.ivar 0))) (.assume (.le (.ivar 0) (.ilit 3)))
def expected : GoalAst :=
  .conj (.atom (.le (.ilit 0) (.ivar 0)))
    (.imp (.le (.ilit 0) (.ivar 0)) (.imp (.le (.ivar 0) (.ilit 3)) .gtrue))

example : refWpS prog .gtrue = expected := by decide
example : refWpS prog .gtrue = expected := by rfl

#print axioms refWpS
