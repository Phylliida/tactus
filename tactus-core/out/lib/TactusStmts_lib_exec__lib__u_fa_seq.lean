import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fa_seq_at_lib_6076_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData), /- @rust:lib.rs:6076:13 -/ lib.frame_after f (lib.StmData.Seq a b) = lib.frame_after (lib.frame_after f a.deref) b.deref
