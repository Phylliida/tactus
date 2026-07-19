import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cew_let_at_lib_3704_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (ob : lib.RawExp), /- @rust:lib.rs:3704:13 -/ lib.close_e_wrap (lib.FrameList.FLet x v t) ob = lib.GoalData.Let x v (Tactus.Box.mk (lib.close_e_wrap t.deref ob))
