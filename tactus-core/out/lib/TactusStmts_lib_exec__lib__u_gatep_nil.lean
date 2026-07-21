import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gatep_nil_at_lib_3963_13_1_stmt : Prop :=
  /- @rust:tactus-core/lib.rs:3963:13 -/ lib.has_poisoned_hyp lib.FrameList.FNil = 0
