import TactusStmts_lib_exec__lib__u_wp_ret
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_wp_ret_at_lib_3436_13_1 (f : lib.FrameList) (es : Tactus.Box lib.RawExpList) (rb : lib.RetBind) :
    /- @rust:lib.rs:3436:13 -/ lib.wp_stm f (lib.StmData.Ret es rb) = lib.close_each_e (lib.ret_frame f rb) es.deref := by
  tactus_auto
