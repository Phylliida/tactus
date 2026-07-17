import TactusStmts_lib_exec__lib__u_obligs_nil
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_obligs_nil_at_lib_3277_13_1 (he : lib.ExprData → (Int → Int) → Prop) :
    /- @rust:lib.rs:3277:13 -/ ∀ (st : Int → Int), lib.obligs_safe he lib.RawExpList.Nil st = True := by
  first | tactus_auto | (intros <;> rfl)
