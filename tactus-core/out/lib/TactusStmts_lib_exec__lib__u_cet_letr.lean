import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cet_letr_at_lib_5175_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.GoalData), /- @rust:tactus-core/lib.rs:5175:13 -/ lib.close_e_tel (lib.FrameList.FLetR x v t) g = lib.close_e_tel t.deref g
