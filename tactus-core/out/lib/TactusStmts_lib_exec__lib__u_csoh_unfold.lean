import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csoh_unfold_at_lib_4507_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList), /- @rust:lib.rs:4507:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st l = lib.close_sem_obligs_tel hp he lv f f st l
