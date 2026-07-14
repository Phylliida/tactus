import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def lib.probe_ref_wp_stmt : Prop :=
  lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.LeafList.Nil) (lib.StmData.Assert (lib.atom_ob 9) 9)) = 1
