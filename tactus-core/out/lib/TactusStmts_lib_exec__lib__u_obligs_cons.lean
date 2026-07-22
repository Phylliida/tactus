import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
@[reducible] noncomputable def _tactus_postcondition_u_obligs_cons_at_lib_3723_13_1_stmt : Prop :=
  ∀ (he : lib.ExprData → (Int → Int) → Prop) (h : Tactus.Box lib.RawExp) (t : Tactus.Box lib.RawExpList), /- @rust:tactus-core/lib.rs:3723:13 -/ ∀ (st : Int → Int), lib.obligs_safe he (lib.RawExpList.Cons h t) st = (he (lib.render_exp h.deref) st ∧ lib.obligs_safe he t.deref st)
