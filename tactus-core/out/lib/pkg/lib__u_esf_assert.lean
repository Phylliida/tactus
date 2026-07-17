import TactusStmts_lib_exec__lib__u_esf_assert
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_esf_assert_at_lib_3326_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) :
    /- @rust:lib.rs:3326:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Assert o h) st = lib.close_sem_e hp he lv f st o := by
  first | tactus_auto | (intros <;> rfl)
