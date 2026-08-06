import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gatep_nil_at_lib_5064_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList), /- @rust:tactus-core/lib.rs:5064:13 -/ lib.has_poisoned_hyp pp lib.FrameList.FNil = 0
