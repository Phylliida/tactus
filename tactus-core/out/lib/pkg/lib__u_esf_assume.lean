import TactusStmts_lib_exec__lib__u_esf_assume
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_esf_assume_at_lib_3591_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616) :
    /- @rust:lib.rs:3591:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Assume e) st = True := by
  first | tactus_auto | (intros <;> rfl)
