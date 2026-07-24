import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_assert_at_lib_4169_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (hn : Int) (h_hn_bound : 0 ≤ hn ∧ hn < 18446744073709551616) (h : Int) (h_h_bound : 0 ≤ h ∧ h < 18446744073709551616) (hpz : Int) (h_hpz_bound : 0 ≤ hpz ∧ hpz < 18446744073709551616), /- @rust:tactus-core/lib.rs:4169:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.Assert o hn h hpz) st = lib.close_sem_e hp he lv f st o
