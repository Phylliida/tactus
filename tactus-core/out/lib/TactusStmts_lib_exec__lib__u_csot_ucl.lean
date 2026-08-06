import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_csot_ucl_at_lib_4878_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (l : lib.RawExpList), /- @rust:tactus-core/lib.rs:4878:13 -/ ∀ (st : Int → Int), lib.close_sem_obligs_tel hp he lv (lib.FrameList.FUserCloser t) f0 st l = lib.close_sem_obligs_tel hp he lv t.deref f0 st l
