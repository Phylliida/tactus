import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_aqnl_at_lib_4206_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (b : Tactus.Box lib.StmData) (tq : lib.RawExp), /- @rust:lib.rs:4206:13 -/ lib.wp_stm f (lib.StmData.AssertQueryNl b tq) = lib.goals_append (lib.wp_stm (lib.strip_hyps f) b.deref) (lib.GoalList.Cons (Tactus.Box.mk (lib.close_e (lib.frame_after (lib.strip_hyps f) b.deref) tq)) (Tactus.Box.mk lib.GoalList.Nil))
