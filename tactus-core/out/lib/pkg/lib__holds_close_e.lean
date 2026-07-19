import TactusStmts_lib_exec__lib__holds_close_e
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_precondition_holds_close_e_at_lib_3894_9_2 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → /- @rust:lib.rs:3894:9 -/ lib.has_plain_flet f = 1 := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_holds_close_e_at_lib_3895_9_4 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → (∀ (_tactus_ret_1 : Unit), lib.close_e f o = lib.close_e_wrap f o → /- @rust:lib.rs:3895:9 -/ lib.has_plain_flet f = 1) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_holds_close_e_at_lib_3890_13_6 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → (∀ (_tactus_ret_1 : Unit), lib.close_e f o = lib.close_e_wrap f o → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_wrap hp he lv f st o) → (∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_wrap f o) st = lib.close_sem_e_wrap hp he lv f st o) → (/- @rust:lib.rs:3890:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f o) st = lib.close_sem_e hp he lv f st o)))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_holds_close_e_at_lib_3898_9_8 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → /- @rust:lib.rs:3898:9 -/ ¬(lib.has_plain_flet f = 1) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_holds_close_e_at_lib_3899_9_10 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → (∀ (_tactus_ret_7 : Unit), lib.close_e f o = lib.close_e_hoist f o → /- @rust:lib.rs:3899:9 -/ ¬(lib.has_plain_flet f = 1)) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_holds_close_e_at_lib_3890_13_12 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → (∀ (_tactus_ret_7 : Unit), lib.close_e f o = lib.close_e_hoist f o → (∀ (_tactus_ret_9 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_hoist hp he lv f st o) → (∀ (_tactus_ret_11 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_hoist f o) st = lib.close_sem_e_hoist hp he lv f st o) → (/- @rust:lib.rs:3890:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f o) st = lib.close_sem_e hp he lv f st o)))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
