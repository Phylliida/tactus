import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cer_nil_at_lib_5196_13_1_stmt : Prop :=
  ∀ (g : lib.GoalData), /- @rust:tactus-core/lib.rs:5196:13 -/ lib.residue_fold_e lib.FrameList.FNil g = g
