import TactusStmts_lib_exec__lib__u_cso_hoist_mode
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_cso_hoist_mode_at_lib_3529_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList) :
    /- @rust:lib.rs:3529:13 -/ ¬(lib.has_plain_flet f = 1) → (∀ (st : Int → Int), lib.close_sem_obligs hp he lv f st l = lib.close_sem_obligs_hoist hp he lv f st l) := by
  first | tactus_auto | (intros <;> simp_all [lib.close_sem_obligs])
