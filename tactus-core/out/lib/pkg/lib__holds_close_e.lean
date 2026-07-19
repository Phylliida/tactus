import TactusStmts_lib_exec__lib__holds_close_e
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_holds_close_e_at_lib_3888_13_7 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (_tactus_ret_1 : Unit) (_h_ctx_0 : lib.has_plain_flet f = 1 → lib.close_e f o = lib.close_e_wrap f o) (_tactus_ret_2 : Unit) (_h_ctx_1 : lib.has_plain_flet f = 1 → (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_wrap hp he lv f st o)) (_tactus_ret_3 : Unit) (_h_ctx_2 : ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_wrap f o) st = lib.close_sem_e_wrap hp he lv f st o) (_tactus_ret_4 : Unit) (_h_ctx_3 : ¬(lib.has_plain_flet f = 1) → lib.close_e f o = lib.close_e_hoist f o) (_tactus_ret_5 : Unit) (_h_ctx_4 : ¬(lib.has_plain_flet f = 1) → (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_hoist hp he lv f st o)) (_tactus_ret_6 : Unit) (_h_ctx_5 : ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_hoist f o) st = lib.close_sem_e_hoist hp he lv f st o) :
    /- @rust:lib.rs:3888:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f o) st = lib.close_sem_e hp he lv f st o := by
  first | tactus_auto | (intros <;> by_cases _hgate : lib.has_plain_flet f = 1 <;> simp_all)
