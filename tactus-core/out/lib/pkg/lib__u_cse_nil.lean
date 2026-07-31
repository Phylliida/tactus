import TactusStmts_lib_exec__lib__u_cse_nil
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cse_nil_at_lib_4577_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:4577:13 -/ ∀ (st : Int → Int), lib.close_sem_e pp hp he lv lib.FrameList.FNil st o = he (lib.render_exp o) st := by
  first | tactus_auto | (intros <;> rfl)
