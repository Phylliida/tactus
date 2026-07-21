import TactusStmts_lib_exec__lib__u_cset_bind
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cset_bind_at_lib_3687_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:3687:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv (lib.FrameList.FBind x ty t) f0 st o = (∀ (n : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd st x n) o) := by
  first | tactus_auto | (intros <;> rfl)
