import TactusStmts_lib_exec__lib__u_csoh_leth
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_csoh_leth_at_lib_3585_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (ty : Int) (h_ty_bound : 0 ≤ ty ∧ ty < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (en : Int) (h_en_bound : 0 ≤ en ∧ en < 18446744073709551616) (ep : Int) (h_ep_bound : 0 ≤ ep ∧ ep < 18446744073709551616) (t : Tactus.Box lib.FrameList) (l : lib.RawExpList) :
    /- @rust:lib.rs:3585:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_hoist hp he lv (lib.FrameList.FLetH x ty v en ep t) st l = (∀ (a : Int) (b : Int), lib.close_sem_obligs_hoist hp he lv t.deref (lib.upd (lib.upd st x a) en b) l) := by
  first | tactus_auto | (intros <;> rfl)
