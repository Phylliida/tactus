import TactusStmts_lib_exec__lib__u_csot_nil
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_csot_nil_at_lib_4099_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f0 : lib.FrameList) (l : lib.RawExpList) :
    /- @rust:tactus-core/lib.rs:4099:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv lib.FrameList.FNil f0 st l = lib.close_sem_obligs_res hp he lv f0 st l := by
  first | tactus_auto | (intros <;> rfl)
