import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fapp_fucl_at_lib_6488_13_1_stmt : Prop :=
  ∀ (t : Tactus.Box lib.FrameList) (g : lib.FrameList), /- @rust:tactus-core/lib.rs:6488:13 -/ lib.frame_append (lib.FrameList.FUserCloser t) g = lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t.deref g))
