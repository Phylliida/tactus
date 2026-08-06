import TactusStmts_lib_exec__lib__u_cset_leth
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cset_leth_at_lib_4701_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (en : Int) (h_en_bound : 0 ≤ en ∧ en < 18446744073709551616) (ep : Int) (h_ep_bound : 0 ≤ ep ∧ ep < 18446744073709551616) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:4701:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv (lib.FrameList.FLetH x ty v en ep t) f0 st o = (∀ (a : Int) (b : Int), lib.close_sem_e_tel hp he lv t.deref f0 (lib.upd (lib.upd st x a) en b) o) := by
  first | tactus_auto | (intros <;> rfl)
