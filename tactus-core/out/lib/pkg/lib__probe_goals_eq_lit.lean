import TactusStmts_lib_exec__lib__probe_goals_eq_lit
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.probe_goals_eq_lit :
    lib.goals_eq lib.GoalList.Nil lib.GoalList.Nil = 1 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
