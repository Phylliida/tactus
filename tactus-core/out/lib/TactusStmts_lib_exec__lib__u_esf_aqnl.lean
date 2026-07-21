import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_aqnl_at_lib_3887_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:3887:13 -/ ∀ (st : Int → Int), lib.exec_safe_f hp he lv f (lib.StmData.AssertQueryNl b) st = lib.exec_safe_f hp he lv (lib.strip_hyps f) b.deref st
