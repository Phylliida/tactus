import TactusStmts_lib_exec__lib__u_gapp_cons
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_gapp_cons_at_lib_3416_13_1 (h : Tactus.Box lib.GoalData) (t : Tactus.Box lib.GoalList) (b : lib.GoalList) :
    /- @rust:lib.rs:3416:13 -/ lib.goals_append (lib.GoalList.Cons h t) b = lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t.deref b)) := by
  tactus_auto
