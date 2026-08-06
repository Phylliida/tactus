import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gate_hyp_at_lib_5047_13_1_stmt : Prop :=
  ∀ (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:5047:13 -/ lib.has_plain_flet (lib.FrameList.FHyp n h t) = lib.has_plain_flet t.deref
