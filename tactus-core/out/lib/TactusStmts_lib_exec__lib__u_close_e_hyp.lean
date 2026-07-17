import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_close_e_hyp_at_lib_3434_13_1_stmt : Prop :=
  ∀ (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.FrameList) (ob : lib.RawExp), /- @rust:lib.rs:3434:13 -/ lib.close_e (lib.FrameList.FHyp h t) ob = lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e t.deref ob))
