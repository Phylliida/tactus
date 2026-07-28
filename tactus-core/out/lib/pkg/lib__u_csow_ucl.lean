import TactusStmts_lib_exec__lib__u_csow_ucl
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_csow_ucl_at_lib_4462_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList) :
    /- @rust:lib.rs:4462:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv (lib.FrameList.FUserCloser t) st l = lib.close_sem_obligs_wrap hp he lv t.deref st l := by
  first | tactus_auto | (intros <;> rfl)
