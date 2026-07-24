import TactusStmts_lib_exec__lib__cso_nil_true_hoist
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_cso_nil_true_hoist_at_lib_4576_13_3 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let tmp__1 := lib.RawExpList.Nil;
    ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st tmp__1 = lib.close_sem_obligs_tel hp he lv f f st tmp__1) → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv f f st lib.RawExpList.Nil = True) → (/- @rust:lib.rs:4576:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st lib.RawExpList.Nil = True)) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))
