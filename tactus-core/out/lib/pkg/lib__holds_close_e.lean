import TactusStmts_lib_exec__lib__holds_close_e
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_holds_close_e_at_lib_5591_13_7 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (_tactus_ret_1 : Unit) (_h_hoist_1 : lib.gate_wrap pp f = 1 → lib.close_e pp f o = lib.close_e_wrap_lead f o) (_tactus_ret_2 : Unit) (_h_hoist_2 : lib.gate_wrap pp f = 1 → (∀ (st : Int → Int), lib.close_sem_e pp hp he lv f st o = lib.close_sem_e_wrap_lead hp he lv f st o)) (_tactus_ret_3 : Unit) (_h_hoist_3 : ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_wrap_lead f o) st = lib.close_sem_e_wrap_lead hp he lv f st o) (_tactus_ret_4 : Unit) (_h_hoist_4 : ¬(lib.gate_wrap pp f = 1) → lib.close_e pp f o = lib.close_e_hoist f o) (_tactus_ret_5 : Unit) (_h_hoist_5 : ¬(lib.gate_wrap pp f = 1) → (∀ (st : Int → Int), lib.close_sem_e pp hp he lv f st o = lib.close_sem_e_hoist hp he lv f st o)) (_tactus_ret_6 : Unit) (_h_hoist_6 : ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_hoist f o) st = lib.close_sem_e_hoist hp he lv f st o) :
    /- @rust:tactus-core/lib.rs:5591:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e pp f o) st = lib.close_sem_e pp hp he lv f st o := by
  first | tactus_auto | (intros <;> by_cases _hgate : lib.gate_wrap pp f = 1 <;> simp_all)
