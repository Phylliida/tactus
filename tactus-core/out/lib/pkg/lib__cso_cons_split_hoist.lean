import TactusStmts_lib_exec__lib__cso_cons_split_hoist
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_cso_cons_split_hoist_at_lib_4721_13_5 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    let tmp__1 := lib.RawExpList.Cons h t;
    ∀ (_tactus_ret_1 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st tmp__1 = lib.close_sem_obligs_tel hp he lv f f st tmp__1) → (∀ (_tactus_ret_2 : Unit), (∀ (st : Int → Int), lib.close_sem_e_hoist hp he lv f st h.deref = lib.close_sem_e_tel hp he lv f f st h.deref) → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st t.deref = lib.close_sem_obligs_tel hp he lv f f st t.deref) → (∀ (_tactus_ret_4 : Unit), (∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv f f st (lib.RawExpList.Cons h t) = (lib.close_sem_e_tel hp he lv f f st h.deref ∧ lib.close_sem_obligs_tel hp he lv f f st t.deref)) → (/- @rust:tactus-core/lib.rs:4721:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv f st (lib.RawExpList.Cons h t) = (lib.close_sem_e_hoist hp he lv f st h.deref ∧ lib.close_sem_obligs_hoist hp he lv f st t.deref))))) := by
  first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))
