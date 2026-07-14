import TactusStmts_lib_exec__lib__ref_wp_seed_and_assert
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.ref_wp_seed_and_assert :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Assert 9)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.Leaf 9)))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil (lib.LeafList.Cons 5 (Tactus.Box.mk (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil))))) (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 5 (Tactus.Box.mk (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil))))))) = 2 := by
  decide 
