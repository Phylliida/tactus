import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_assume_at_lib_5235_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616) (hpz : Int) (h_hpz_bound : 0 ≤ hpz ∧ hpz < 18446744073709551616), /- @rust:tactus-core/lib.rs:5235:13 -/ lib.wp_stm pp f (lib.StmData.Assume hn e hpz) = lib.GoalList.Nil
