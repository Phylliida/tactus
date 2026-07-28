import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_goal_eq_nested_stmt : Prop :=
  lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 1 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 7 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0
