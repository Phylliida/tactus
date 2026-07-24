import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csor_ucl_at_lib_4164_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList), /- @rust:tactus-core/lib.rs:4164:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_res hp he lv (lib.FrameList.FUserCloser t) st l = lib.close_sem_obligs_res hp he lv t.deref st l
