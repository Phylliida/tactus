import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_close_e_nil_at_lib_3428_13_1_stmt : Prop :=
  ∀ (ob : lib.RawExp), /- @rust:lib.rs:3428:13 -/ lib.close_e lib.FrameList.FNil ob = lib.GoalData.LeafE (lib.render_exp ob)
