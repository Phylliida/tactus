import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csew_nil_at_lib_4598_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (o : lib.RawExp), /- @rust:tactus-core/lib.rs:4598:13 -/ ∀ (st : Int → Int), lib.close_sem_e_wrap hp he lv lib.FrameList.FNil st o = he (lib.render_exp o) st
