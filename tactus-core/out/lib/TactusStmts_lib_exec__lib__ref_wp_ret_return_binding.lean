import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.ref_wp_ret_return_binding_stmt : Prop :=
  lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 9 14 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 22 (Tactus.Box.mk lib.LeafList.Nil))) (lib.RetBind.RetLet 23 9))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 9 14 (Tactus.Box.mk (lib.GoalData.Let 23 9 (Tactus.Box.mk (lib.GoalData.Leaf 22)))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 9 14 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 22 (Tactus.Box.mk lib.LeafList.Nil))) lib.RetBind.RetNone)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 9 14 (Tactus.Box.mk (lib.GoalData.Leaf 22)))) (Tactus.Box.mk lib.GoalList.Nil)) = 1
