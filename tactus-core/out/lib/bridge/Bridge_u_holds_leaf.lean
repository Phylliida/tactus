import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_holds_leaf`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦hp⟧
-- leaf 1: ⟦Int → (Int → Int) → Prop⟧
-- leaf 2: ⟦he⟧
-- leaf 3: ⟦lib.ExprData → (Int → Int) → Prop⟧
-- leaf 4: ⟦lv⟧
-- leaf 5: ⟦Int → (Int → Int) → Int⟧
-- leaf 6: ⟦id⟧
-- leaf 7: ⟦Int⟧
-- leaf 8: ⟦0 ≤ id ∧ id < 18446744073709551616⟧
-- leaf 9: ⟦h_id_bound⟧
-- leaf 10: ⟦∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.Leaf id) st = hp id st⟧
-- leaf 11: ⟦/- @rust:tactus-core/lib.rs:4537:13 -/ ∀ (st : Int → Int), lib.holds hp he lv (lib.GoalData.Leaf id) st = hp id st⟧

@[reducible] def cert_u_holds_leaf_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk (lib.BinderList.Cons 6 7 (Tactus.Box.mk lib.BinderList.Nil)))))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.Bound 9 8 (Tactus.Box.mk lib.ParamBoundList.Nil)))))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 10 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 0)

@[reducible] def cert_u_holds_leaf_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 11 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_holds_leaf_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_holds_leaf_at_lib_4537_13_1
@[reducible] def cert_u_holds_leaf_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.All 6 7 (Tactus.Box.mk (lib.GoalData.All 9 8 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 11))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_holds_leaf_goals = 1 := by decide

-- ── W4a in-gate bridge (bootstrap-38) ──
set_option maxRecDepth 8000
example : lib.goals_eq (lib.ref_wp cert_u_holds_leaf_ctx cert_u_holds_leaf_sst) cert_u_holds_leaf_goals = 1 := by decide
