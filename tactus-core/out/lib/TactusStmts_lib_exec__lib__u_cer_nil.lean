import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cer_nil_at_lib_4678_13_1_stmt : Prop :=
  ∀ (g : lib.GoalData), /- @rust:lib.rs:4678:13 -/ lib.residue_fold_e lib.FrameList.FNil g = g
