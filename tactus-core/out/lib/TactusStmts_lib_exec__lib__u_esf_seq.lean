import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_seq_at_lib_5010_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (a : Tactus.Box lib.StmData) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:5010:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Seq a b) st = (lib.exec_safe_f pp hp he lv f a.deref st ∧ lib.exec_safe_f pp hp he lv (lib.frame_after pp f a.deref) b.deref st)
