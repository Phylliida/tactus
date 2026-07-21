import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_ceh_unfold_at_lib_4017_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (ob : lib.RawExp), /- @rust:tactus-core/lib.rs:4017:13 -/ lib.close_e_hoist f ob = lib.close_e_tel f (lib.residue_fold_e f (lib.GoalData.LeafE (lib.render_exp ob)))
