import TactusStmts_lib_exec__lib__u_esf_call
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_call_at_lib_4443_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList) :
    /- @rust:lib.rs:4443:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Call reqs post) st = lib.close_sem_obligs hp he lv f st reqs.deref := by
  first | tactus_auto | (intros <;> rfl)
