import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cce_cons_at_lib_5205_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList), /- @rust:tactus-core/lib.rs:5205:13 -/ lib.close_each_e pp f (lib.RawExpList.Cons h t) = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e pp f h.deref)) (Tactus.Box.mk (lib.close_each_e pp f t.deref))
