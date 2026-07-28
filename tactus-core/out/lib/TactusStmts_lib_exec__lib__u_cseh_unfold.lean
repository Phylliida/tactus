import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cseh_unfold_at_lib_4340_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), /- @rust:lib.rs:4340:13 -/ ∀ (st : Int → Int), lib.close_sem_e_hoist hp he lv f st o = lib.close_sem_e_tel hp he lv f f st o
