import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.goal_eq_strictness_stmt : Prop :=
  lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 6) = 0 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.Leaf 5) = 1 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.All 7 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goal_eq (lib.GoalData.Imp 2 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.Imp 3 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goal_eq (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) (lib.GoalData.Imp 1 (Tactus.Box.mk (lib.GoalData.Leaf 9))) = 0 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Leaf 9)) (Tactus.Box.mk lib.GoalList.Nil)) lib.GoalList.Nil = 0
