/- W0 pre-probe P1: does a STRUCTURALLY-compiled reference WP kernel-evaluate
   on concrete data, under both `decide` (via derived DecidableEq) and `rfl`?
   This is the Bridge-D mechanic. Pure core, no Mathlib. -/

-- Mini SST: expressions
inductive PExpr where
  | ivar : Nat → PExpr
  | ilit : Int → PExpr
  | add  : PExpr → PExpr → PExpr
  | le   : PExpr → PExpr → PExpr
  | not  : PExpr → PExpr
deriving DecidableEq, Repr

-- Mini SST: statements (binary seq instead of List to keep recursion plainly structural)
inductive PStm where
  | assign : Nat → PExpr → PStm
  | assert : PExpr → PStm
  | assume : PExpr → PStm
  | ite    : PExpr → PStm → PStm → PStm
  | seq    : PStm → PStm → PStm
deriving DecidableEq, Repr

-- Deep goal syntax (the GoalAst / LExpr-mirror analog)
inductive GoalAst where
  | atom : PExpr → GoalAst
  | imp  : PExpr → GoalAst → GoalAst
  | conj : GoalAst → GoalAst → GoalAst
  | glet : Nat → PExpr → GoalAst → GoalAst
  | gtrue : GoalAst
deriving DecidableEq, Repr

-- Reference WP: plain structural recursion, NO termination_by.
def refWp : PStm → GoalAst → GoalAst
  | .assign x e, g => .glet x e g
  | .assert e,   g => .conj (.atom e) (.imp e g)
  | .assume e,   g => .imp e g
  | .ite c t f,  g => .conj (.imp c (refWp t g)) (.imp (.not c) (refWp f g))
  | .seq a b,    g => refWp a (refWp b g)

-- A small program: x := 1; assert (0 <= x); if (x <= 5) { assume (x <= 3) } else { assert (0 <= x) }
def prog1 : PStm :=
  .seq (.assign 0 (.ilit 1))
    (.seq (.assert (.le (.ilit 0) (.ivar 0)))
      (.ite (.le (.ivar 0) (.ilit 5))
        (.assume (.le (.ivar 0) (.ilit 3)))
        (.assert (.le (.ilit 0) (.ivar 0)))))

-- Hand-written expected goal (what the "production emitter" would have serialized)
def expected1 : GoalAst :=
  .glet 0 (.ilit 1)
    (.conj (.atom (.le (.ilit 0) (.ivar 0)))
      (.imp (.le (.ilit 0) (.ivar 0))
        (.conj
          (.imp (.le (.ivar 0) (.ilit 5))
            (.imp (.le (.ivar 0) (.ilit 3)) .gtrue))
          (.imp (.not (.le (.ivar 0) (.ilit 5)))
            (.conj (.atom (.le (.ilit 0) (.ivar 0)))
              (.imp (.le (.ilit 0) (.ivar 0)) .gtrue))))))

-- THE BRIDGE, both forms:
example : refWp prog1 .gtrue = expected1 := by decide
example : refWp prog1 .gtrue = expected1 := by rfl

#print axioms refWp
