import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_gapp_cons_at_lib_3738_13_1_stmt : Prop :=
  ∀ (h : Tactus.Box lib.GoalData) (t : Tactus.Box lib.GoalList) (b : lib.GoalList), /- @rust:lib.rs:3738:13 -/ lib.goals_append (lib.GoalList.Cons h t) b = lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t.deref b))
