import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cet_nil_at_lib_4839_13_1_stmt : Prop :=
  ∀ (g : lib.GoalData), /- @rust:lib.rs:4839:13 -/ lib.close_e_tel lib.FrameList.FNil g = g
