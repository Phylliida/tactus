import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cse_nil_at_lib_4577_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (o : lib.RawExp), /- @rust:tactus-core/lib.rs:4577:13 -/ ∀ (st : Int → Int), lib.close_sem_e pp hp he lv lib.FrameList.FNil st o = he (lib.render_exp o) st
