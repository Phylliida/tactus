import TactusStmts_lib_exec__lib__u_cset_nil
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cset_nil_at_lib_3790_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f0 : lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3790:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv lib.FrameList.FNil f0 st o = lib.close_sem_e_res hp he lv f0 st o := by
  first | tactus_auto | (intros <;> rfl)
