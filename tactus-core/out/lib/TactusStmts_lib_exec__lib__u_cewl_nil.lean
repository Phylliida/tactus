import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cewl_nil_at_lib_4810_13_1_stmt : Prop :=
  ∀ (ob : lib.RawExp), /- @rust:lib.rs:4810:13 -/ lib.close_e_wrap_lead lib.FrameList.FNil ob = lib.GoalData.LeafE (lib.render_exp ob)
