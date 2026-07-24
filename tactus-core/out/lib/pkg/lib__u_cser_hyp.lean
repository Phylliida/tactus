import TactusStmts_lib_exec__lib__u_cser_hyp
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cser_hyp_at_lib_3835_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (p : Int) (h_p_bound : 0 ≤ p ∧ p < 18446744073709551616) (t : Tactus.Box lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3835:13 -/ ∀ (st : Int → Int), lib.close_sem_e_res hp he lv (lib.FrameList.FHyp n h p t) st o = lib.close_sem_e_res hp he lv t.deref st o := by
  first | tactus_auto | (intros <;> rfl)
