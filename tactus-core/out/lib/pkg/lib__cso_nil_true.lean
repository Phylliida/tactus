import TactusStmts_lib_exec__lib__cso_nil_true
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_precondition_cso_nil_true_at_lib_4000_9_2 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    /- @rust:lib.rs:3999:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Nil;
                                                          /- @rust:lib.rs:4000:9 -/ lib.has_plain_flet f = 1) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_cso_nil_true_at_lib_3997_13_4 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    /- @rust:lib.rs:3999:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Nil;
                                                          ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__1 = lib.close_sem_obligs_wrap hp he lv f st tmp__1) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv f st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:3997:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_nil_true_at_lib_4003_9_6 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    ¬(/- @rust:lib.rs:3999:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Nil;
                                                             /- @rust:lib.rs:4003:9 -/ ¬(lib.has_plain_flet f = 1)) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_cso_nil_true_at_lib_3997_13_8 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    ¬(/- @rust:lib.rs:3999:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Nil;
                                                             ∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__2 = lib.close_sem_obligs_hoist hp he lv f st tmp__2) → (∀ (_tactus_ret_7 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:3997:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
