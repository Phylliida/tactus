import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gateu_ucl_at_lib_4932_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:4932:13 -/ lib.has_user_closer (lib.FrameList.FUserCloser t) = 1
