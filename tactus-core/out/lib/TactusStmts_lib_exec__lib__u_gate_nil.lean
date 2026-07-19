import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gate_nil_at_lib_3668_13_1_stmt : Prop :=
  /- @rust:lib.rs:3668:13 -/ lib.has_plain_flet lib.FrameList.FNil = 0
