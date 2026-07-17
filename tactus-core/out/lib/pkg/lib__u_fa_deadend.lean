import TactusStmts_lib_exec__lib__u_fa_deadend
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_fa_deadend_at_lib_3765_13_1 (f : lib.FrameList) (b : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:3765:13 -/ lib.frame_after f (lib.StmData.DeadEnd b) = f := by
  tactus_auto
