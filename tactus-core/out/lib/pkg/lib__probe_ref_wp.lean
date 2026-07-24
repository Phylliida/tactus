import TactusStmts_lib_exec__lib__probe_ref_wp
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem lib.probe_ref_wp :
    lib.goal_count (lib.ref_wp (lib.FnCtxData.mk lib.BinderList.Nil lib.BinderList.Nil lib.ParamBoundList.Nil lib.BinderList.Nil lib.LeafList.Nil 1) (lib.StmData.Assert (lib.atom_ob 9) 0 9 0)) = 1 := by
  decide 
