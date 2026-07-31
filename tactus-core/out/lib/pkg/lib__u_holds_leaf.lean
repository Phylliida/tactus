import TactusStmts_lib_exec__lib__u_holds_leaf
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_holds_leaf_at_lib_4536_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (id : Int) (h_id_bound : 0 ≤ id ∧ id < 18446744073709551616) :
    /- @rust:tactus-core/lib.rs:4536:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.Leaf id) st = hp id st := by
  first | tactus_auto | (intros <;> rfl)
