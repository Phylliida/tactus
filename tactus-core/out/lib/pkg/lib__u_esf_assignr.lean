import TactusStmts_lib_exec__lib__u_esf_assignr
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_assignr_at_lib_3963_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) :
    /- @rust:tactus-core/lib.rs:3963:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.AssignR x v) st = True := by
  first | tactus_auto | (intros <;> rfl)
