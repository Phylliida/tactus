import TactusStmts_lib_exec__lib__probe_close
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem lib.probe_close :
    lib.goal_size (lib.close lib.FrameList.FNil 9) = 1 ∧ lib.goal_size (lib.close (lib.FrameList.FBind 0 1 (Tactus.Box.mk lib.FrameList.FNil)) 9) = 2 := by
  decide 
