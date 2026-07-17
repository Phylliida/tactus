import TactusStmts_lib_exec__lib__u_wp_skip
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_wp_skip_at_lib_3462_13_1 (f : lib.FrameList) :
    /- @rust:lib.rs:3462:13 -/ lib.wp_stm f lib.StmData.Skip = lib.GoalList.Nil := by
  tactus_auto
