import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cewl_ucl_at_lib_4645_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList) (ob : lib.RawExp), /- @rust:lib.rs:4645:13 -/ lib.close_e_wrap_lead (lib.FrameList.FUserCloser t) ob = lib.close_e_wrap_lead t.deref ob
