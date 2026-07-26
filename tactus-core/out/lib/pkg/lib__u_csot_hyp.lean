import TactusStmts_lib_exec__lib__u_csot_hyp
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_csot_hyp_at_lib_4362_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (p : Int) (h_p_bound : 0 ≤ p ∧ p < 18446744073709551616) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (l : lib.RawExpList) :
    /- @rust:lib.rs:4362:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv (lib.FrameList.FHyp n h p t) f0 st l = (∀ (v : Int), lib.close_sem_obligs_tel hp he lv t.deref f0 (lib.upd st n v) l) := by
  first | tactus_auto | (intros <;> rfl)
