import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gateu_ucl_at_lib_4770_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList), /- @rust:lib.rs:4770:13 -/ lib.has_user_closer (lib.FrameList.FUserCloser t) = 1
