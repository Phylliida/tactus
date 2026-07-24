import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cset_nil_at_lib_3969_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f0 : lib.FrameList) (o : lib.RawExp), /- @rust:tactus-core/lib.rs:3969:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv lib.FrameList.FNil f0 st o = lib.close_sem_e_res hp he lv f0 st o
