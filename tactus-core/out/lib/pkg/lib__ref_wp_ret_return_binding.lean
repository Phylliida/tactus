import TactusStmts_lib_exec__lib__ref_wp_ret_return_binding
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.ref_wp_ret_return_binding :
    lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 16 23 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 12)) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 13 16))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 16 23 (Tactus.Box.mk (lib.GoalData.Let 13 16 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 ∧ lib.goals_eq (lib.wp_stm (lib.FrameList.FLet 16 23 (Tactus.Box.mk lib.FrameList.FNil)) (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.atom_ob 12)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.Let 16 23 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 12))))) (Tactus.Box.mk lib.GoalList.Nil)) = 1 := by
  decide 
