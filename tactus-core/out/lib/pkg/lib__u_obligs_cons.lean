import TactusStmts_lib_exec__lib__u_obligs_cons
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_obligs_cons_at_lib_3311_13_1 (he : lib.ExprData → (Int → Int) → Prop) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList) :
    /- @rust:lib.rs:3311:13 -/ ∀ (st : Int → Int), lib.obligs_safe he (lib.RawExpList.Cons h t) st = (he (lib.render_exp h.deref) st ∧ lib.obligs_safe he t.deref st) := by
  first | tactus_auto | (intros <;> rfl)
