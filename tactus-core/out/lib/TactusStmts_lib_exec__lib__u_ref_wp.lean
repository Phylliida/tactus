import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_ref_wp_at_lib_4799_13_1_stmt : Prop :=
  ∀ (c : lib.FnCtxData) (s : lib.StmData), /- @rust:tactus-core/lib.rs:4799:13 -/ lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s
