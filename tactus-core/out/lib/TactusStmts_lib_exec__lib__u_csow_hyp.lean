import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csow_hyp_at_lib_4442_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (p : Int) (h_p_bound : 0 ≤ p ∧ p < 18446744073709551616) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList), /- @rust:lib.rs:4442:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_wrap hp he lv (lib.FrameList.FHyp n h p t) st l = (hp h st → lib.close_sem_obligs_wrap hp he lv t.deref st l)
