import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_seq_at_lib_4610_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:4610:13 -/ lib.wp_stm f (lib.StmData.Seq a b) = lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref)
