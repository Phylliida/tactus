import TactusStmts_lib_exec__lib__u_esf_call
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_call_at_lib_4924_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList) :
    /- @rust:tactus-core/lib.rs:4924:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Call reqs post) st = lib.close_sem_obligs pp hp he lv f st reqs.deref := by
  first | tactus_auto | (intros <;> rfl)
