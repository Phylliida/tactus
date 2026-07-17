import TactusStmts_lib_exec__lib__u_cce_nil
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_cce_nil_at_lib_3406_13_1 (f : lib.FrameList) :
    /- @rust:lib.rs:3406:13 -/ lib.close_each_e f lib.RawExpList.Nil = lib.GoalList.Nil := by
  tactus_auto
