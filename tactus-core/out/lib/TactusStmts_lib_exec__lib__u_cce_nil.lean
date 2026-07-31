import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cce_nil_at_lib_5202_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList), /- @rust:tactus-core/lib.rs:5202:13 -/ lib.close_each_e pp f lib.RawExpList.Nil = lib.GoalList.Nil
