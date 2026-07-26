import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csewl_nil_at_lib_4140_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (o : lib.RawExp), /- @rust:lib.rs:4140:13 -/ ∀ (st : Int → Int), lib.close_sem_e_wrap_lead hp he lv lib.FrameList.FNil st o = he (lib.render_exp o) st
