import TactusStmts_lib_exec__lib__u_esf_ifctor
import TactusDefs_lib_exec
import TactusSearch
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
-- tactus-closer: user
theorem _tactus_postcondition_u_esf_ifctor_at_lib_4623_13_1 (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (pos_binders : Tactus.Box lib.BinderList) (eq_name : Int) (h_eq_name_bound : 0 ≤ eq_name ∧ eq_name < 18446744073709551616) (eq_prop : Int) (h_eq_prop_bound : 0 ≤ eq_prop ∧ eq_prop < 18446744073709551616) (eq_poison : Int) (h_eq_poison_bound : 0 ≤ eq_poison ∧ eq_poison < 18446744073709551616) (neg_name : Int) (h_neg_name_bound : 0 ≤ neg_name ∧ neg_name < 18446744073709551616) (neg_prop : Int) (h_neg_prop_bound : 0 ≤ neg_prop ∧ neg_prop < 18446744073709551616) (neg_poison : Int) (h_neg_poison_bound : 0 ≤ neg_poison ∧ neg_poison < 18446744073709551616) (thn : Tactus.Box lib.StmData) (els : Tactus.Box lib.StmData) :
    /- @rust:lib.rs:4623:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.IfCtor pos_binders eq_name eq_prop eq_poison neg_name neg_prop neg_poison thn els) st = (lib.exec_safe_f hp he lv (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop eq_poison)) thn.deref st ∧ lib.exec_safe_f hp he lv (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop neg_poison (Tactus.Box.mk lib.FrameList.FNil))) els.deref st) := by
  first | tactus_auto | (intros <;> rfl)
