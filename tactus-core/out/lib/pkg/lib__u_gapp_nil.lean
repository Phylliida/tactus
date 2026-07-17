import TactusStmts_lib_exec__lib__u_gapp_nil
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_gapp_nil_at_lib_3413_13_1 (b : lib.GoalList) :
    /- @rust:lib.rs:3413:13 -/ lib.goals_append lib.GoalList.Nil b = b := by
  tactus_auto
