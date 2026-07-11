/- W0 pre-probe P2: Bridge-D kernel COST at scale. Generate a ~600-statement
   program and its expected goal independently; kernel must evaluate refWp
   over it and compare. Proxy for a large real fn's bridge check. -/

inductive PExpr where
  | ivar : Nat → PExpr
  | ilit : Int → PExpr
  | add  : PExpr → PExpr → PExpr
  | le   : PExpr → PExpr → PExpr
  | not  : PExpr → PExpr
deriving DecidableEq, Repr

inductive PStm where
  | assign : Nat → PExpr → PStm
  | assert : PExpr → PStm
  | assume : PExpr → PStm
  | ite    : PExpr → PStm → PStm → PStm
  | seq    : PStm → PStm → PStm
deriving DecidableEq, Repr

inductive GoalAst where
  | atom : PExpr → GoalAst
  | imp  : PExpr → GoalAst → GoalAst
  | conj : GoalAst → GoalAst → GoalAst
  | glet : Nat → PExpr → GoalAst → GoalAst
  | gtrue : GoalAst
deriving DecidableEq, Repr

def refWp : PStm → GoalAst → GoalAst
  | .assign x e, g => .glet x e g
  | .assert e,   g => .conj (.atom e) (.imp e g)
  | .assume e,   g => .imp e g
  | .ite c t f,  g => .conj (.imp c (refWp t g)) (.imp (.not c) (refWp f g))
  | .seq a b,    g => refWp a (refWp b g)

-- n-block generator: assign; assert; if … {assume} else {assert} — 4 stms per unit
def mkUnit (i : Nat) : PStm :=
  .seq (.assign i (.ilit (Int.ofNat i)))
    (.seq (.assert (.le (.ilit 0) (.ivar i)))
      (.ite (.le (.ivar i) (.ilit 5))
        (.assume (.le (.ivar i) (.ilit 3)))
        (.assert (.le (.ilit 0) (.ivar i)))))

def mkProg : Nat → PStm
  | 0 => .assert (.le (.ilit 0) (.ilit 0))
  | n + 1 => .seq (mkUnit n) (mkProg n)

-- independently-built expected form (mirrors refWp's output shape by hand)
def expUnit (i : Nat) (g : GoalAst) : GoalAst :=
  .glet i (.ilit (Int.ofNat i))
    (.conj (.atom (.le (.ilit 0) (.ivar i)))
      (.imp (.le (.ilit 0) (.ivar i))
        (.conj
          (.imp (.le (.ivar i) (.ilit 5))
            (.imp (.le (.ivar i) (.ilit 3)) g))
          (.imp (.not (.le (.ivar i) (.ilit 5)))
            (.conj (.atom (.le (.ilit 0) (.ivar i)))
              (.imp (.le (.ilit 0) (.ivar i)) g))))))

def expected : Nat → GoalAst
  | 0 => .conj (.atom (.le (.ilit 0) (.ilit 0))) (.imp (.le (.ilit 0) (.ilit 0)) .gtrue)
  | n + 1 => expUnit n (expected n)

-- ~150 units = 600 statements; each `ite` DOUBLES the continuation g in the
-- goal, so keep nesting linear here (units chain sequentially; exponential
-- blowup from value-position ite forks is a separate, real concern noted in
-- the findings).
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
example : refWp (mkProg 150) .gtrue = expected 150 := by decide
