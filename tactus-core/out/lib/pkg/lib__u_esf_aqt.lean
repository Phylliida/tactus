import TactusStmts_lib_exec__lib__u_esf_aqt
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_aqt_at_lib_4205_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (hpz : Int) (h_hpz_bound : 0 ≤ hpz ∧ hpz < 18446744073709551616) :
    /- @rust:tactus-core/lib.rs:4205:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.AssertQueryTactus o hn h hpz) st = lib.close_sem_e hp he lv (lib.frame_append f (lib.FrameList.FUserCloser (Tactus.Box.mk lib.FrameList.FNil))) st o := by
  first | tactus_auto | (intros <;> rfl)
