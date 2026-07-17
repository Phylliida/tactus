import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cso_hyp_at_lib_3316_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList), /- @rust:lib.rs:3316:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs hp he lv (lib.FrameList.FHyp h t) st l = (hp h st → lib.close_sem_obligs hp he lv t.deref st l)
