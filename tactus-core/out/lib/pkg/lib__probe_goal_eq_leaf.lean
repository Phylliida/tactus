import TactusStmts_lib_exec__lib__probe_goal_eq_leaf
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.probe_goal_eq_leaf :
    lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 5) = 1 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 6) = 0 := by
  decide 
