import TactusStmts_lib_exec__lib__u_cse_let
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_cse_let_at_lib_3301_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (x : Int) (h_x_bound : 0 ≤ x ∧ x < 18446744073709551616) (v : Int) (h_v_bound : 0 ≤ v ∧ v < 18446744073709551616) (t : Tactus.Box lib.FrameList) (o : lib.RawExp) :
    /- @rust:lib.rs:3301:13 -/ ∀ (st : Int → Int), lib.close_sem_e hp he lv (lib.FrameList.FLet x v t) st o = lib.close_sem_e hp he lv t.deref (lib.upd st x (lv v st)) o := by
  first | tactus_auto | (intros <;> rfl)
