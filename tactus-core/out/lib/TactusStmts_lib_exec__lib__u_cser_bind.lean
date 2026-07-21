import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cser_bind_at_lib_3811_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.FrameList) (o : lib.RawExp), /- @rust:tactus-core/lib.rs:3811:13 -/ ∀ (st : Int → Int), lib.close_sem_e_res hp he lv (lib.FrameList.FBind x ty t) st o = lib.close_sem_e_res hp he lv t.deref st o
