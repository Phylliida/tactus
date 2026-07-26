import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cer_bind_at_lib_4684_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.GoalData), /- @rust:lib.rs:4684:13 -/ lib.residue_fold_e (lib.FrameList.FBind x ty t) g = lib.residue_fold_e t.deref g
