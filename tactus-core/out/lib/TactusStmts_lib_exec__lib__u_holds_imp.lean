import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_holds_imp_at_lib_3249_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (t : Tactus.Box lib.GoalData), /- @rust:lib.rs:3249:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.Imp h t) st = (hp h st → lib.holds hp he lv t.deref st)
