import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gateu_nil_at_lib_5072_13_1_stmt : Prop :=
  /- @rust:tactus-core/lib.rs:5072:13 -/ lib.has_user_closer lib.FrameList.FNil = 0
