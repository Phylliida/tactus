import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_ref_wp_at_lib_6053_13_1_stmt : Prop :=
  ∀ (c : lib.FnCtxData) (h_c_bound : 0 ≤ c.closer_default ∧ c.closer_default < 18446744073709551616) (s : lib.StmData), /- @rust:lib.rs:6053:13 -/ lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s
