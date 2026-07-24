import TactusStmts_lib_exec__lib__u_esf_if
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_if_at_lib_4221_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (c : Int) (h_c_bound : 0 ≤ c ∧ c < 18446744073709551616) (cn : Int) (h_cn_bound : 0 ≤ cn ∧ cn < 18446744073709551616) (nc : Int) (h_nc_bound : 0 ≤ nc ∧ nc < 18446744073709551616) (ncn : Int) (h_ncn_bound : 0 ≤ ncn ∧ ncn < 18446744073709551616) (cp : Int) (h_cp_bound : 0 ≤ cp ∧ cp < 18446744073709551616) (t : Tactus.Box lib.StmData) (e : Tactus.Box lib.StmData) :
    /- @rust:tactus-core/lib.rs:4221:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.If c cn nc ncn cp t e) st = (lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp cn c cp (Tactus.Box.mk lib.FrameList.FNil))) t.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp ncn nc cp (Tactus.Box.mk lib.FrameList.FNil))) e.deref st) := by
  first | tactus_auto | (intros <;> rfl)
