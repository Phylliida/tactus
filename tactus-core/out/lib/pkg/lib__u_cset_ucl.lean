import TactusStmts_lib_exec__lib__u_cset_ucl
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cset_ucl_at_lib_4710_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:4710:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv (lib.FrameList.FUserCloser t) f0 st o = lib.close_sem_e_tel hp he lv t.deref f0 st o := by
  first | tactus_auto | (intros <;> rfl)
