import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_obligs_nil_at_lib_4569_13_1_stmt : Prop :=
  ∀ (he : lib.ExprData → (Int → Int) → Prop), /- @rust:tactus-core/lib.rs:4569:13 -/ ∀ (st : Int → Int), lib.obligs_safe he lib.RawExpList.Nil st = True
