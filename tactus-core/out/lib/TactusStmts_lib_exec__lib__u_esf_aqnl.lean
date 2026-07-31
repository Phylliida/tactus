import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_aqnl_at_lib_4933_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (b : Tactus.Box lib.StmData) (tq : lib.RawExp), /- @rust:tactus-core/lib.rs:4933:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.AssertQueryNl b tq) st = (lib.exec_safe_f pp hp he lv (lib.strip_hyps f) b.deref st ∧ lib.close_sem_e pp hp he lv (lib.frame_after pp (lib.strip_hyps f) b.deref) st tq)
