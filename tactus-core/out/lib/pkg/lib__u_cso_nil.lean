import TactusStmts_lib_exec__lib__u_cso_nil
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cso_nil_at_lib_4751_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (l : lib.RawExpList) :
    /- @rust:tactus-core/lib.rs:4751:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs pp hp he lv lib.FrameList.FNil st l = lib.obligs_safe he l st := by
  first | tactus_auto | (intros <;> rfl)
