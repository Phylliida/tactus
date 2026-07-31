import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cer_ucl_at_lib_5041_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList) (g : lib.GoalData), /- @rust:tactus-core/lib.rs:5041:13 -/ lib.residue_fold_e (lib.FrameList.FUserCloser t) g = lib.residue_fold_e t.deref g
