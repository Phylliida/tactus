import TactusStmts_lib_exec__lib__u_esf_assume
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_assume_at_lib_4908_13_1 (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (e : Int) (h_e_bound : 0 ≤ e ∧ e < 18446744073709551616) :
    /- @rust:tactus-core/lib.rs:4908:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Assume hn e) st = True := by
  first | tactus_auto | (intros <;> rfl)
