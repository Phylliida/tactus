import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cew_leth_at_lib_4462_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (en : Int) (h_en_bound : 0 ≤ en ∧ en < 18446744073709551616) (ep : Int) (h_ep_bound : 0 ≤ ep ∧ ep < 18446744073709551616) (t : Tactus.Box lib.FrameList) (ob : lib.RawExp), /- @rust:tactus-core/lib.rs:4462:13 -/ lib.close_e_wrap (lib.FrameList.FLetH x ty v en ep t) ob = lib.GoalData.Let x v (Tactus.Box.mk (lib.close_e_wrap t.deref ob))
