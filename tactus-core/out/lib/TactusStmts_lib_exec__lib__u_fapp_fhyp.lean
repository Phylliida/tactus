import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fapp_fhyp_at_lib_4968_13_1_stmt : Prop :=
  ∀ (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (p : Int) (h_p_bound : 0 ≤ p ∧ p < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.FrameList), /- @rust:tactus-core/lib.rs:4968:13 -/ lib.frame_append (lib.FrameList.FHyp n h p t) g = lib.FrameList.FHyp n h p (Tactus.Box.mk (lib.frame_append t.deref g))
