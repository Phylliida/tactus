import TactusStmts_lib_exec__lib__u_esf_if
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem _tactus_postcondition_u_esf_if_at_lib_3618_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (c : Int) (h_c_bound : 0 ≤ c ∧ c < 18446744073709551616) (nc : Int) (h_nc_bound : 0 ≤ nc ∧ nc < 18446744073709551616) (t : Tactus.Box lib.StmData) (e : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:3618:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.If c nc t e) st = (lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp 0 c (Tactus.Box.mk lib.FrameList.FNil))) t.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp 0 nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref st) := by
  first | tactus_auto | (intros <;> rfl)
