import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_precondition_holds_close_e_at_lib_3894_9_2_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → /- @rust:lib.rs:3894:9 -/ lib.has_plain_flet f = 1
@[reducible] noncomputable def _tactus_precondition_holds_close_e_at_lib_3895_9_4_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → (∀ (_tactus_ret_1 : Unit), lib.close_e f o = lib.close_e_wrap f o → /- @rust:lib.rs:3895:9 -/ lib.has_plain_flet f = 1)
@[reducible] noncomputable def _tactus_postcondition_holds_close_e_at_lib_3890_13_6_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), /- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1 → (∀ (_tactus_ret_1 : Unit), lib.close_e f o = lib.close_e_wrap f o → (∀ (_tactus_ret_3 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_wrap hp he lv f st o) → (∀ (_tactus_ret_5 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_wrap f o) st = lib.close_sem_e_wrap hp he lv f st o) → (/- @rust:lib.rs:3890:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f o) st = lib.close_sem_e hp he lv f st o))))
@[reducible] noncomputable def _tactus_precondition_holds_close_e_at_lib_3898_9_8_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → /- @rust:lib.rs:3898:9 -/ ¬(lib.has_plain_flet f = 1)
@[reducible] noncomputable def _tactus_precondition_holds_close_e_at_lib_3899_9_10_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → (∀ (_tactus_ret_7 : Unit), lib.close_e f o = lib.close_e_hoist f o → /- @rust:lib.rs:3899:9 -/ ¬(lib.has_plain_flet f = 1))
@[reducible] noncomputable def _tactus_postcondition_holds_close_e_at_lib_3890_13_12_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp), ¬(/- @rust:lib.rs:3893:8 -/ lib.has_plain_flet f = 1) → (∀ (_tactus_ret_7 : Unit), lib.close_e f o = lib.close_e_hoist f o → (∀ (_tactus_ret_9 : Unit), (∀ (st : Int → Int), lib.close_sem_e hp he lv f st o = lib.close_sem_e_hoist hp he lv f st o) → (∀ (_tactus_ret_11 : Unit), (∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_hoist f o) st = lib.close_sem_e_hoist hp he lv f st o) → (/- @rust:lib.rs:3890:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e f o) st = lib.close_sem_e hp he lv f st o))))
