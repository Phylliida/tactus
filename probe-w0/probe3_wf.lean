/- W0 pre-probe P3: the SAME refWp but WF-compiled (explicit termination_by on
   a Nat measure — what tactus emits for every recursive spec fn with a
   `decreases` clause). Question: do `rfl` / `decide` still evaluate it?
   Expected: NO (WF defs are sealed/irreducible; Acc.rec gets stuck), and
   `unseal` may or may not rescue it. `simp [refWpWF]` (equation lemmas)
   should work. Each claim tested below; failures are the DATA. -/

inductive PExpr where
  | ivar : Nat → PExpr
  | ilit : Int → PExpr
  | le   : PExpr → PExpr → PExpr
  | not  : PExpr → PExpr
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

-- WF-compiled: explicit termination_by on the Nat measure (tactus emission shape)
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

-- T1: decide on the WF def
example : refWpWF prog .gtrue = expected := by decide

-- T2: rfl on the WF def
-- example : refWpWF prog .gtrue = expected := by rfl

-- T3: unseal + rfl
-- unseal refWpWF in
-- example : refWpWF prog .gtrue = expected := by rfl

-- T4: simp with equation lemmas (deterministic fallback)
example : refWpWF prog .gtrue = expected := by simp [refWpWF, prog, expected]
