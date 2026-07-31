import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_holds_close_e_hoist_at_lib_5389_13_4_stmt : Prop :=
  ∀ (hp : Int → (Int → Int) → Prop) (he : lib.ExprData → (Int → Int) → Prop) (lv : Int → (Int → Int) → Int) (f : lib.FrameList) (o : lib.RawExp) (_tactus_ret_1 : Unit) (_h_hoist_1 : lib.close_e_hoist f o = lib.close_e_tel f (lib.residue_fold_e f (lib.GoalData.LeafE (lib.render_exp o)))) (_tactus_ret_2 : Unit) (_h_hoist_2 : ∀ (st : Int → Int), lib.close_sem_e_hoist hp he lv f st o = lib.close_sem_e_tel hp he lv f f st o) (_tactus_ret_3 : Unit) (_h_hoist_3 : ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_tel f (lib.residue_fold_e f (lib.GoalData.LeafE (lib.render_exp o)))) st = lib.close_sem_e_tel hp he lv f f st o), /- @rust:tactus-core/lib.rs:5389:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.close_e_hoist f o) st = lib.close_sem_e_hoist hp he lv f st o
