import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_seq_at_lib_5339_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:5339:13 -/ lib.wp_stm pp f (lib.StmData.Seq a b) = lib.goals_append (lib.wp_stm pp f a.deref) (lib.wp_stm pp (lib.frame_after pp f a.deref) b.deref)
