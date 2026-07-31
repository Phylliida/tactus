import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.ref_wp_add_capped_seed_spine_stmt : Prop :=
  lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.BinderList.Cons 8 7 (Tactus.Box.mk (lib.BinderList.Cons 10 9 (Tactus.Box.mk lib.BinderList.Nil)))) lib.MutParamList.Nil (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1) (lib.StmData.Assert (lib.atom_ob 15) 0 14 0)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 15))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1
