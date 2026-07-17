import TactusStmts_lib_exec__lib__u_fapp_fnil
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_fapp_fnil_at_lib_3771_13_1 (g : lib.FrameList) :
    /- @rust:lib.rs:3771:13 -/ lib.frame_append lib.FrameList.FNil g = g := by
  tactus_auto
