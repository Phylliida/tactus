import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fapp_fletr_at_lib_6484_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.FrameList), /- @rust:tactus-core/lib.rs:6484:13 -/ lib.frame_append (lib.FrameList.FLetR x v t) g = lib.FrameList.FLetR x v (Tactus.Box.mk (lib.frame_append t.deref g))
