import TactusStmts_lib_exec__lib__ref_wp_add_capped_seed_spine
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.ref_wp_add_capped_seed_spine :
    lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 3 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 18 4 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.BinderList.Cons 17 5 (Tactus.Box.mk (lib.BinderList.Cons 16 6 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.LeafList.Cons 7 (Tactus.Box.mk lib.LeafList.Nil))) (lib.StmData.Assert 15)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.All 3 1 (Tactus.Box.mk (lib.GoalData.All 18 4 (Tactus.Box.mk (lib.GoalData.All 17 5 (Tactus.Box.mk (lib.GoalData.All 16 6 (Tactus.Box.mk (lib.GoalData.Leaf 15)))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
