import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_skip_at_lib_4985_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList), /- @rust:lib.rs:4985:13 -/ lib.wp_stm f lib.StmData.Skip = lib.GoalList.Nil
