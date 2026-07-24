import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_holds_leaf_at_lib_3689_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (id : Int) (h_id_bound : 0 ≤ id ∧ id < 18446744073709551616), /- @rust:lib.rs:3689:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.Leaf id) st = hp id st
