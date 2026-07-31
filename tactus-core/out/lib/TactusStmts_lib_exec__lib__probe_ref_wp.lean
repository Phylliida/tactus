import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_ref_wp_stmt : Prop :=
  lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.MutParamList.Nil lib.LeafList.Nil lib.LeafList.Nil lib.PropDeepList.Nil 1) (lib.StmData.Assert (lib.atom_ob 9) 0 9)) = 1
