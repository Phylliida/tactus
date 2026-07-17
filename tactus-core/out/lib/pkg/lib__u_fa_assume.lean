import TactusStmts_lib_exec__lib__u_fa_assume
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_fa_assume_at_lib_3761_13_1 (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616) :
    /- @rust:lib.rs:3761:13 -/ lib.frame_after f (lib.StmData.Assume e) = lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) := by
  tactus_auto
