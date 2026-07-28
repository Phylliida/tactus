import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_goal_eq_leaf_stmt : Prop :=
  lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 5) = 1 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 6) = 0
