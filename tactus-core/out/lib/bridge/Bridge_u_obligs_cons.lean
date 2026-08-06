import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_obligs_cons`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦he⟧
-- leaf 1: ⟦lib.ExprData → (Int → Int) → Prop⟧
-- leaf 2: ⟦h⟧
-- leaf 3: ⟦Tactus.Box lib.RawExp⟧
-- leaf 4: ⟦t⟧
-- leaf 5: ⟦Tactus.Box lib.RawExpList⟧
-- leaf 6: ⟦∀ (st : Int → Int), lib.obligs_safe he (lib.RawExpList.Cons h t) st = (he (lib.render_exp h) st ∧ lib.obligs_safe he t st)⟧
-- leaf 7: ⟦/- @rust:tactus-core/lib.rs:4573:13 -/ ∀ (st : Int → Int), lib.obligs_safe he (lib.RawExpList.Cons h t) st = (he (lib.render_exp h.deref) st ∧ lib.obligs_safe he t.deref st)⟧

@[reducible] def cert_u_obligs_cons_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_obligs_cons_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 7 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_obligs_cons_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_obligs_cons_at_lib_4573_13_1
@[reducible] def cert_u_obligs_cons_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_obligs_cons_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_obligs_cons_ctx cert_u_obligs_cons_sst) cert_u_obligs_cons_goals = 1 := by decide
