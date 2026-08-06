import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_holds_leafe_at_lib_4556_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (e : lib.ExprData), /- @rust:tactus-core/lib.rs:4556:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.LeafE e) st = he e st
