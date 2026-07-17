import TactusStmts_lib_exec__lib__u_fapp_fhyp
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_fapp_fhyp_at_lib_3778_13_1 (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.FrameList) :
    /- @rust:lib.rs:3778:13 -/ lib.frame_append (lib.FrameList.FHyp h t) g = lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) := by
  tactus_auto
