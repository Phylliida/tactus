import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cet_bind_at_lib_4116_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.GoalData), /- @rust:tactus-core/lib.rs:4116:13 -/ lib.close_e_tel (lib.FrameList.FBind x ty t) g = lib.GoalData.All x ty (Tactus.Box.mk (lib.close_e_tel t.deref g))
