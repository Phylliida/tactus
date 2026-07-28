import TactusStmts_lib_exec__lib__u_holds_all_cons
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_holds_all_cons_at_lib_4228_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (g : Tactus.Box lib.GoalData) (t : Tactus.Box lib.GoalList) :
    /- @rust:lib.rs:4228:13 -/ ∀ (st : Int → Int), lib.holds_all hp he lv (lib.GoalList.Cons g t) st = (lib.holds hp he lv g.deref st ∧ lib.holds_all hp he lv t.deref st) := by
  first | tactus_auto | (intros <;> rfl)
