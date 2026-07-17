import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_aqnl_at_lib_3470_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (b : Tactus.Box lib.StmData), /- @rust:lib.rs:3470:13 -/ lib.wp_stm f (lib.StmData.AssertQueryNl b) = lib.wp_stm (lib.strip_hyps f) b.deref
