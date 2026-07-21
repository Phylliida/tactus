import TactusStmts_lib_exec__lib__leafe_goal_bridge_kernel_computes
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem lib.leafe_goal_bridge_kernel_computes :
    lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) = 1 ∧ lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))))) (lib.GoalData.LeafE (lib.ExprData.BinOp 1 (Tactus.Box.mk (lib.ExprData.Cast lib.CastKind.IntToNat (Tactus.Box.mk (lib.ExprData.Atom 3)))) (Tactus.Box.mk (lib.ExprData.Atom 3)))) = 0 ∧ lib.goal_eq (lib.GoalData.LeafE (lib.ExprData.Atom 5)) (lib.GoalData.Leaf 5) = 0 ∧ lib.goal_eq (lib.GoalData.Leaf 5) (lib.GoalData.LeafE (lib.ExprData.Atom 5)) = 0 ∧ lib.goals_eq (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))) (Tactus.Box.mk lib.GoalList.Nil)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goal_size (lib.GoalData.Imp 7 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9)))) = 2 := by
  decide 
