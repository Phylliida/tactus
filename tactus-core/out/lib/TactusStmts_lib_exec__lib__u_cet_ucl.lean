import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cet_ucl_at_lib_4858_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList) (g : lib.GoalData), /- @rust:lib.rs:4858:13 -/ lib.close_e_tel (lib.FrameList.FUserCloser t) g = lib.close_e_tel t.deref g
