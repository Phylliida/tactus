import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cset_hyp_at_lib_4078_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (n : Int) (h_n_bound : 0 ≤ n ∧ n < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (p : Int) (h_p_bound : 0 ≤ p ∧ p < 18446744073709551616) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (o : lib.RawExp), /- @rust:tactus-core/lib.rs:4078:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv (lib.FrameList.FHyp n h p t) f0 st o = (∀ (v : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd st n v) o)
