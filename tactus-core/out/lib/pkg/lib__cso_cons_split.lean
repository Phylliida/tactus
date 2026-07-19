import TactusStmts_lib_exec__lib__cso_cons_split
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_precondition_cso_cons_split_at_lib_4102_9_2 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    /- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Cons h t;
                                                          /- @rust:lib.rs:4102:9 -/ lib.has_plain_flet f = 1) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_cons_split_at_lib_4103_9_4 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    /- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Cons h t;
                                                          ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__1 = lib.close_sem_obligs_wrap hp he lv f st tmp__1) → /- @rust:lib.rs:4103:9 -/ lib.has_plain_flet f = 1) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_cons_split_at_lib_4104_9_6 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    /- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Cons h t;
                                                          ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__1 = lib.close_sem_obligs_wrap hp he lv f st tmp__1) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st h.deref = lib.close_sem_e_wrap hp he lv f st h.deref) → /- @rust:lib.rs:4104:9 -/ lib.has_plain_flet f = 1)) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_cso_cons_split_at_lib_4098_13_8 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    /- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1 → (let tmp__1 := lib.RawExpList.Cons h t;
                                                          ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__1 = lib.close_sem_obligs_wrap hp he lv f st tmp__1) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st h.deref = lib.close_sem_e_wrap hp he lv f st h.deref) → (∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st t.deref = lib.close_sem_obligs_wrap hp he lv f st t.deref) → (∀ (_tactus_ret_7 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e_wrap hp he lv f st h.deref ∧ lib.close_sem_obligs_wrap hp he lv f st t.deref)) → (/- @rust:lib.rs:4098:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e hp he lv f st h.deref ∧ lib.close_sem_obligs hp he lv f st t.deref)))))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_cons_split_at_lib_4107_9_10 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    ¬(/- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Cons h t;
                                                             /- @rust:lib.rs:4107:9 -/ ¬(lib.has_plain_flet f = 1)) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_cons_split_at_lib_4108_9_12 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    ¬(/- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Cons h t;
                                                             ∀ (_tactus_ret_9 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__2 = lib.close_sem_obligs_hoist hp he lv f st tmp__2) → /- @rust:lib.rs:4108:9 -/ ¬(lib.has_plain_flet f = 1)) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_precondition_cso_cons_split_at_lib_4109_9_14 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    ¬(/- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Cons h t;
                                                             ∀ (_tactus_ret_9 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__2 = lib.close_sem_obligs_hoist hp he lv f st tmp__2) → (∀ (_tactus_ret_11 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st h.deref = lib.close_sem_e_hoist hp he lv f st h.deref) → /- @rust:lib.rs:4109:9 -/ ¬(lib.has_plain_flet f = 1))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
theorem _tactus_postcondition_cso_cons_split_at_lib_4098_13_16 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    ¬(/- @rust:lib.rs:4101:8 -/ lib.has_plain_flet f = 1) → (let tmp__2 := lib.RawExpList.Cons h t;
                                                             ∀ (_tactus_ret_9 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__2 = lib.close_sem_obligs_hoist hp he lv f st tmp__2) → (∀ (_tactus_ret_11 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st h.deref = lib.close_sem_e_hoist hp he lv f st h.deref) → (∀ (_tactus_ret_13 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st t.deref = lib.close_sem_obligs_hoist hp he lv f st t.deref) → (∀ (_tactus_ret_15 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e_hoist hp he lv f st h.deref ∧ lib.close_sem_obligs_hoist hp he lv f st t.deref)) → (/- @rust:lib.rs:4098:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e hp he lv f st h.deref ∧ lib.close_sem_obligs hp he lv f st t.deref)))))) := by
  first | tactus_auto | (intros <;> tactus_case_split simp_all)
