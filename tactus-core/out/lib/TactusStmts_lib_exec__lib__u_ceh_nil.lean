import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_ceh_nil_at_lib_3712_13_1_stmt : Prop :=
  ∀ (ob : lib.RawExp), /- @rust:lib.rs:3712:13 -/ lib.close_e_hoist lib.FrameList.FNil ob = lib.GoalData.LeafE (lib.render_exp ob)
