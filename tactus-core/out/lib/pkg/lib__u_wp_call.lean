import TactusStmts_lib_exec__lib__u_wp_call
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_wp_call_at_lib_3430_13_1 (f : lib.FrameList) (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList) :
    /- @rust:lib.rs:3430:13 -/ lib.wp_stm f (lib.StmData.Call reqs post) = lib.close_each_e f reqs.deref := by
  tactus_auto
