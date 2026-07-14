import TactusStmts_lib_exec__lib__probe_wp_stm
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.probe_wp_stm :
    lib.goal_count (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert (lib.atom_ob 9) 9)) = 1 ∧ lib.goal_count (lib.wp_stm lib.FrameList.FNil lib.StmData.Skip) = 0 := by
  decide 
