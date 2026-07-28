import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_cso_nil_true_hoist_at_lib_5440_13_3_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList), let tmp__1 := lib.RawExpList.Nil;
                                                                                                                                 ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st tmp__1 = lib.close_sem_obligs_tel hp he lv f f st tmp__1) → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv f f st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:5440:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st lib.RawExpList.Nil = True))
