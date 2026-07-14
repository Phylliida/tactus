import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.ref_wp_seq_threads_frame_stmt : Prop :=
  lib.goals_eq (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk lib.BinderList.Nil)) (lib.ParamBoundList.Bound 19 2 (Tactus.Box.mk lib.ParamBoundList.Nil)) lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 9) 9)) (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 10) 10)))) (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 9))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 19 2 (Tactus.Box.mk (lib.GoalData.Imp 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 10))))))))) (Tactus.Box.mk lib.GoalList.Nil)))) = 1
