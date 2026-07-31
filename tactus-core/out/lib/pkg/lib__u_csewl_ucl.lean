import TactusStmts_lib_exec__lib__u_csewl_ucl
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_csewl_ucl_at_lib_4665_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:4665:13 -/ ∀ (st : Int → Int), lib.close_sem_e_wrap_lead hp he lv (lib.FrameList.FUserCloser t) st o = lib.close_sem_e_wrap_lead hp he lv t.deref st o := by
  first | tactus_auto | (intros <;> rfl)
