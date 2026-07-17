import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_assume_at_lib_3361_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616), /- @rust:lib.rs:3361:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Assume e) st = True
