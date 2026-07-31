import TactusStmts_lib_exec__lib__u_cso_wrap_mode
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cso_wrap_mode_at_lib_4742_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (l : lib.RawExpList) :
    /- @rust:tactus-core/lib.rs:4742:13 -/ lib.gate_wrap pp f = 1 → (∀ (st : Int → Int), lib.close_sem_obligs pp hp he lv f st l = lib.close_sem_obligs_wrap_lead hp he lv f st l) := by
  first | tactus_auto | (intros <;> simp_all [lib.close_sem_obligs])
