import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fapp_fnil_at_lib_5391_13_1_stmt : Prop :=
  ∀ (g : lib.FrameList), /- @rust:tactus-core/lib.rs:5391:13 -/ lib.frame_append lib.FrameList.FNil g = g
