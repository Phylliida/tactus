import TactusStmts_lib_exec__lib__u_wp_deadend
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_wp_deadend_at_lib_3433_13_1 (f : lib.FrameList) (b : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:3433:13 -/ lib.wp_stm f (lib.StmData.DeadEnd b) = lib.wp_stm f b.deref := by
  tactus_auto
