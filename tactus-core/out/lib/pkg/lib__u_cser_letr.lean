import TactusStmts_lib_exec__lib__u_cser_letr
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_cser_letr_at_lib_3746_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (o : lib.RawExp) :
    /- @rust:tactus-core/lib.rs:3746:13 -/ ∀ (st : Int → Int), lib.close_sem_e_res hp he lv (lib.FrameList.FLetR x v t) st o = lib.close_sem_e_res hp he lv t.deref (lib.upd st x (lv v st)) o := by
  first | tactus_auto | (intros <;> rfl)
