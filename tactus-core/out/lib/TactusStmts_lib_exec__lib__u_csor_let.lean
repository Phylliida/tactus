import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csor_let_at_lib_4888_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList), /- @rust:tactus-core/lib.rs:4888:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_res hp he lv (lib.FrameList.FLet x v t) st l = lib.close_sem_obligs_res hp he lv t.deref st l
