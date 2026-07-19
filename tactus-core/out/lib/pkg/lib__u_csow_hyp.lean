import TactusStmts_lib_exec__lib__u_csow_hyp
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_csow_hyp_at_lib_3549_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList) :
    /- @rust:lib.rs:3549:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv (lib.FrameList.FHyp n h t) st l = (hp h st → lib.close_sem_obligs_wrap hp he lv t.deref st l) := by
  first | tactus_auto | (intros <;> rfl)
