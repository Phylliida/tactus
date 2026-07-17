import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_fapp_fbind_at_lib_3774_13_1_stmt : Prop :=
  ∀ (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.FrameList) (g : lib.FrameList), /- @rust:lib.rs:3774:13 -/ lib.frame_append (lib.FrameList.FBind x ty t) g = lib.FrameList.FBind x ty (Tactus.Box.mk (lib.frame_append t.deref g))
