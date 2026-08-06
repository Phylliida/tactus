import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_esf_deadend_at_lib_4944_13_1_stmt : Prop :=
  ∀ (pp : lib.LeafList) (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (bs : Tactus.Box lib.BinderList) (bds : Tactus.Box lib.ParamBoundList) (b : Tactus.Box lib.StmData), /- @rust:tactus-core/lib.rs:4944:13 -/ ∀ (st : Int → Int), lib.exec_safe_f pp hp he lv f (lib.StmData.DeadEnd bs bds b) st = lib.exec_safe_f pp hp he lv (lib.frame_append f (lib.mod_var_frames bs.deref bds.deref)) b.deref st
