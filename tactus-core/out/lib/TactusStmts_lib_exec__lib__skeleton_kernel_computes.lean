import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.skeleton_kernel_computes_stmt : Prop :=
  lib.stm_size (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.atom_ob 0) 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone))))) = 5 ∧ lib.goal_size (lib.GoalData.Imp 7 (Tactus.Box.mk (lib.GoalData.All 8 9 (Tactus.Box.mk (lib.GoalData.Leaf 10))))) = 3 ∧ lib.leaf_len (lib.LeafList.Cons 1 (Tactus.Box.mk (lib.LeafList.Cons 2 (Tactus.Box.mk lib.LeafList.Nil)))) = 2
