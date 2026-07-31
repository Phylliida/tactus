import TactusStmts_lib_exec__lib__cso_nil_true
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_cso_nil_true_at_lib_5610_13_5 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    let tmp__1 := lib.RawExpList.Nil;
    ∀ (_tactus_ret_1 : Unit), (lib.gate_wrap f = 1 → (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__1 = lib.close_sem_obligs_wrap_lead hp he lv f st tmp__1)) → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_wrap_lead hp he lv f st lib.RawExpList.Nil = True) → (let tmp__2 := lib.RawExpList.Nil;
                                                                                                                                                                                                                                                                                                         ∀ (_tactus_ret_3 : Unit), (¬(lib.gate_wrap f = 1) → (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st tmp__2 = lib.close_sem_obligs_hoist hp he lv f st tmp__2)) → (∀ (_tactus_ret_4 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st lib.RawExpList.Nil = True) → (/- @rust:tactus-core/lib.rs:5610:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st lib.RawExpList.Nil = True)))) := by
  first | tactus_auto | (intros <;> by_cases _hgate : lib.gate_wrap f = 1 <;> simp_all (config := { zetaDelta := true }))
