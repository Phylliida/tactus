import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csow_nil_at_lib_3865_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (l : lib.RawExpList), /- @rust:tactus-core/lib.rs:3865:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv lib.FrameList.FNil st l = lib.obligs_safe he l st
