/- W0 pre-probe P3b: can `unseal` (semireducible) rescue kernel evaluation of a
   WF-compiled def? If yes: bridge modules just say `unseal refWp in` and the
   emitter needs NO structural-termination feature. If no: the mitigation must
   be `termination_by structural` emission or simp-based bridging. -/

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

def PStm.size : PStm → Nat
  | .assert _ => 1
  | .assume _ => 1
  | .seq a b => a.size + b.size + 1

def refWpWF : PStm → GoalAst → GoalAst
  | .assert e,   g => .conj (.atom e) (.imp e g)
  | .assume e,   g => .imp e g
  | .seq a b,    g => refWpWF a (refWpWF b g)
termination_by s _ => s.size
decreasing_by all_goals (simp [PStm.size]; omega)

def prog : PStm := .seq (.assert (.le (.ilit 0) (.ivar 0))) (.assume (.le (.ivar 0) (.ilit 3)))
def expected : GoalAst :=
  .conj (.atom (.le (.ilit 0) (.ivar 0)))
    (.imp (.le (.ilit 0) (.ivar 0)) (.imp (.le (.ivar 0) (.ilit 3)) .gtrue))

set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
unseal refWpWF in
example : refWpWF prog .gtrue = expected := by rfl
