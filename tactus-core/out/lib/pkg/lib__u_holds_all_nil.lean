import TactusStmts_lib_exec__lib__u_holds_all_nil
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_holds_all_nil_at_lib_4560_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) :
    /- @rust:tactus-core/lib.rs:4560:13 -/ ∀ (st : Int → Int), lib.holds_all hp he lv lib.GoalList.Nil st = True := by
  first | tactus_auto | (intros <;> rfl)
