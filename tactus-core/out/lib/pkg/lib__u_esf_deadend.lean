import TactusStmts_lib_exec__lib__u_esf_deadend
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_esf_deadend_at_lib_3604_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (b : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:3604:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.DeadEnd b) st = lib.exec_safe_f hp he lv f b.deref st := by
  first | tactus_auto | (intros <;> rfl)
