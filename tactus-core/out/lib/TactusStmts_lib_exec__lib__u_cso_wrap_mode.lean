import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cso_wrap_mode_at_lib_3524_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList), /- @rust:lib.rs:3524:13 -/ lib.has_plain_flet f = 1 → (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st l = lib.close_sem_obligs_wrap hp he lv f st l)
