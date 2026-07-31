import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cew_nil_at_lib_5107_13_1_stmt : Prop :=
  ∀ (ob : lib.RawExp), /- @rust:tactus-core/lib.rs:5107:13 -/ lib.close_e_wrap lib.FrameList.FNil ob = lib.GoalData.LeafE (lib.render_exp ob)
