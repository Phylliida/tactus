import TactusStmts_lib_exec__lib__u_cseh_unfold
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cseh_unfold_at_lib_3783_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:3783:13 -/ ∀ (st : Int → Int), lib.close_sem_e_hoist hp he lv f st o = lib.close_sem_e_tel hp he lv f f st o := by
  first | tactus_auto | (intros <;> rfl)
