import TactusStmts_lib_exec__lib__u_wp_seq
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_wp_seq_at_lib_3465_13_1 (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:3465:13 -/ lib.wp_stm f (lib.StmData.Seq a b) = lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref) := by
  tactus_auto
