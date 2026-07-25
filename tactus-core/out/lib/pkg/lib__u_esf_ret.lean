import TactusStmts_lib_exec__lib__u_esf_ret
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_ret_at_lib_4315_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (es : Tactus.Box lib.RawExpList) (rb : lib.RetBind) :
    /- @rust:tactus-core/lib.rs:4315:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Ret es rb) st = lib.close_sem_obligs hp he lv (lib.ret_frame f rb) st es.deref := by
  first | tactus_auto | (intros <;> rfl)
