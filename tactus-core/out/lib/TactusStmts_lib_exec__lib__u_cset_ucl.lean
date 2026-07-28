import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_cset_ucl_at_lib_4375_13_1_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (t : Tactus.Box lib.FrameList) (f0 : lib.FrameList) (o : lib.RawExp), /- @rust:lib.rs:4375:13 -/ ∀ (st : Int → Int), lib.close_sem_e_tel hp he lv (lib.FrameList.FUserCloser t) f0 st o = lib.close_sem_e_tel hp he lv t.deref f0 st o
