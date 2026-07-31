import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cew_ucl_at_lib_4967_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList) (ob : lib.RawExp), /- @rust:tactus-core/lib.rs:4967:13 -/ lib.close_e_wrap (lib.FrameList.FUserCloser t) ob = lib.close_e_wrap t.deref ob
