import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_holds_all_nil_at_lib_3886_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int), /- @rust:tactus-core/lib.rs:3886:13 -/ ∀ (st : Int → Int), lib.holds_all hp he lv lib.GoalList.Nil st = True
