import TactusStmts_lib_exec__lib__u_esf_seq
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_seq_at_lib_5025_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData) :
    /- @rust:tactus-core/lib.rs:5025:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Seq a b) st = (lib.exec_safe_f pp hp he lv f a.deref st ∧ lib.exec_safe_f pp hp he lv (lib.frame_after pp f a.deref) b.deref st) := by
  first | tactus_auto | (intros <;> rfl)
