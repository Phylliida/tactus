import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_ret_at_lib_4964_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (es : Tactus.Box lib.RawExpList) (rb : lib.RetBind), /- @rust:tactus-core/lib.rs:4964:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Ret es rb) st = lib.close_sem_obligs pp hp he lv (lib.ret_frame pp f rb) st es.deref
