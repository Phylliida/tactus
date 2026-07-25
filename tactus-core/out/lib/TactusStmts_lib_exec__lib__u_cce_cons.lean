import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cce_cons_at_lib_4525_13_1_stmt : Prop :=
  ∀ (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList), /- @rust:tactus-core/lib.rs:4525:13 -/ lib.close_each_e f (lib.RawExpList.Cons h t) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref)) (Tactus.Box.mk (lib.close_each_e f t.deref))
