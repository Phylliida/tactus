import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gate_ucl_at_lib_4387_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:4387:13 -/ lib.has_plain_flet (lib.FrameList.FUserCloser t) = lib.has_plain_flet t.deref
