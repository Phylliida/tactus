import TactusStmts_lib_exec__lib__u_close_e_nil
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_close_e_nil_at_lib_3394_13_1 (ob : lib.RawExp) :
    /- @rust:lib.rs:3394:13 -/ lib.close_e lib.FrameList.FNil ob = lib.GoalData.LeafE (lib.render_exp ob) := by
  tactus_auto
