import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_wp_ifctor_at_lib_5252_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (f : lib.FrameList) (pos_binders : Tactus.Box lib.BinderList) (eq_name : Int) (h_eq_name_bound : 0 ≤ eq_name ∧ eq_name < 18446744073709551616) (eq_prop : Int) (h_eq_prop_bound : 0 ≤ eq_prop ∧ eq_prop < 18446744073709551616) (neg_name : Int) (h_neg_name_bound : 0 ≤ neg_name ∧ neg_name < 18446744073709551616) (neg_prop : Int) (h_neg_prop_bound : 0 ≤ neg_prop ∧ neg_prop < 18446744073709551616) (thn : Tactus.Box lib.StmData) (els : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:5252:13 -/ lib.wp_stm pp f (lib.StmData.IfCtor pos_binders eq_name eq_prop neg_name neg_prop thn els) = lib.goals_append (lib.wp_stm pp (lib.frame_append f (lib.ctor_pos_frame pos_binders.deref eq_name eq_prop)) thn.deref) (lib.wp_stm pp (lib.frame_append f (lib.FrameList.FHyp neg_name neg_prop (Tactus.Box.mk lib.FrameList.FNil))) els.deref)
