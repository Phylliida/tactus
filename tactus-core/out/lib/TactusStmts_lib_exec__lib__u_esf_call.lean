import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_call_at_lib_4939_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (reqs : Tactus.Box lib.RawExpList) (post : Tactus.Box lib.FrameList), /- @rust:tactus-core/lib.rs:4939:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.Call reqs post) st = lib.close_sem_obligs pp hp he lv f st reqs.deref
