import TactusStmts_lib_exec__lib__u_esf_skip
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_skip_at_lib_4015_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) :
    /- @rust:tactus-core/lib.rs:4015:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f lib.StmData.Skip st = True := by
  first | tactus_auto | (intros <;> rfl)
