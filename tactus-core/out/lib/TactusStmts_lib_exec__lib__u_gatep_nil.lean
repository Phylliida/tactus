import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gatep_nil_at_lib_4729_13_1_stmt : Prop :=
  /- @rust:lib.rs:4729:13 -/ lib.has_poisoned_hyp lib.FrameList.FNil = 0
