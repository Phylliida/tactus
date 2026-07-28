import TactusStmts_lib_exec__lib__u_holds_all_binder
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_holds_all_binder_at_lib_4210_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.GoalData) :
    /- @rust:lib.rs:4210:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.All x ty t) st = (∀ (n : Int), lib.holds hp he lv t.deref (lib.upd st x n)) := by
  first | tactus_auto | (intros <;> rfl)
