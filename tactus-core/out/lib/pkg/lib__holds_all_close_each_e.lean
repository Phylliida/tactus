import TactusStmts_lib_exec__lib__holds_all_close_each_e
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_holds_all_close_each_e_at_lib_4111_13_4 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList) (st : Int → Int) :
    let decrease_init0 := l;
    let tmp___0 := l;
    /- @rust:lib.rs:4116:9 -/ tmp___0.isNil → (∀ (_tactus_ret_1 : Unit), lib.close_each_e f lib.RawExpList.Nil = lib.GoalList.Nil → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv lib.GoalList.Nil st = True) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True) → /- @rust:lib.rs:4111:13 -/ lib.holds_all hp he lv (lib.close_each_e f l) st = lib.close_sem_obligs hp he lv f st l))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_termination_holds_all_close_each_e_at_lib_4126_13_9 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList) (st : Int → Int) :
    let decrease_init0 := l;
    let tmp___0 := l;
    ¬/- @rust:lib.rs:4116:9 -/ tmp___0.isNil → (let h := tmp___0.Cons_val0;
                                                let t := tmp___0.Cons_val1;
                                                ∀ (_tactus_ret_5 : Unit), lib.close_each_e f (lib.RawExpList.Cons h t) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref)) (Tactus.Box.mk (lib.close_each_e f t.deref)) → (let tmp__1 := lib.close_e f h.deref;
                                                                                                                                                                                                                                   let tmp__2 := lib.close_each_e f t.deref;
                                                                                                                                                                                                                                   ∀ (_tactus_ret_6 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons (Tactus.Box.mk tmp__1) (Tactus.Box.mk tmp__2)) st = (lib.holds hp he lv tmp__1 st ∧ lib.holds_all hp he lv tmp__2 st)) → (∀ (_tactus_ret_7 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f h.deref) st = lib.close_sem_e hp he lv f st h.deref) → (∀ (_tactus_ret_8 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e hp he lv f st h.deref ∧ lib.close_sem_obligs hp he lv f st t.deref)) → /- @rust:lib.rs:4126:13 -/ lib.RawExpList.height t.deref < lib.RawExpList.height decrease_init0 ∨ lib.RawExpList.height t.deref = lib.RawExpList.height decrease_init0 ∧ False)))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
theorem _tactus_postcondition_holds_all_close_each_e_at_lib_4111_13_11 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList) (st : Int → Int) :
    let decrease_init0 := l;
    let tmp___0 := l;
    ¬/- @rust:lib.rs:4116:9 -/ tmp___0.isNil → (let h := tmp___0.Cons_val0;
                                                let t := tmp___0.Cons_val1;
                                                ∀ (_tactus_ret_5 : Unit), lib.close_each_e f (lib.RawExpList.Cons h t) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref)) (Tactus.Box.mk (lib.close_each_e f t.deref)) → (let tmp__1 := lib.close_e f h.deref;
                                                                                                                                                                                                                                   let tmp__2 := lib.close_each_e f t.deref;
                                                                                                                                                                                                                                   ∀ (_tactus_ret_6 : Unit), (∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons (Tactus.Box.mk tmp__1) (Tactus.Box.mk tmp__2)) st = (lib.holds hp he lv tmp__1 st ∧ lib.holds_all hp he lv tmp__2 st)) → (∀ (_tactus_ret_7 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f h.deref) st = lib.close_sem_e hp he lv f st h.deref) → (∀ (_tactus_ret_8 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e hp he lv f st h.deref ∧ lib.close_sem_obligs hp he lv f st t.deref)) → lib.RawExpList.height t.deref < lib.RawExpList.height decrease_init0 ∨ lib.RawExpList.height t.deref = lib.RawExpList.height decrease_init0 ∧ False → (∀ (_tactus_ret_10 : Unit), lib.holds_all hp he lv (lib.close_each_e f t.deref) st = lib.close_sem_obligs hp he lv f st t.deref → /- @rust:lib.rs:4111:13 -/ lib.holds_all hp he lv (lib.close_each_e f l) st = lib.close_sem_obligs hp he lv f st l))))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
