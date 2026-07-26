import TactusStmts_lib_exec__lib__u_esf_assign
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_assign_at_lib_4431_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (rhs : Int) (h_rhs_bound : 0 ≤ rhs ∧ rhs < 18446744073709551616) :
    /- @rust:lib.rs:4431:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Assign x rhs) st = True := by
  first | tactus_auto | (intros <;> rfl)
