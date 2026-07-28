import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fa_deadend_at_lib_6004_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (b : Tactus.Box lib.StmData), /- @rust:lib.rs:6004:13 -/ lib.frame_after f (lib.StmData.DeadEnd b) = f
