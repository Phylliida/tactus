import TactusStmts_lib_exec__lib__u_cse_wrap_mode
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cse_wrap_mode_at_lib_4571_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:4571:13 -/ lib.gate_wrap pp f = 1 → (∀ (st : Int → Int), lib.close_sem_e pp hp he lv f st o = lib.close_sem_e_wrap_lead hp he lv f st o) := by
  first | tactus_auto | (intros <;> simp_all [lib.close_sem_e])
