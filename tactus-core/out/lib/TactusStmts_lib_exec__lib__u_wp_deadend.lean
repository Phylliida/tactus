import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_deadend_at_lib_3755_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (b : Tactus.Box lib.StmData), /- @rust:lib.rs:3755:13 -/ lib.wp_stm f (lib.StmData.DeadEnd b) = lib.wp_stm f b.deref
