import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_skip_at_lib_5320_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList), /- @rust:tactus-core/lib.rs:5320:13 -/ lib.wp_stm pp f lib.StmData.Skip = lib.GoalList.Nil
