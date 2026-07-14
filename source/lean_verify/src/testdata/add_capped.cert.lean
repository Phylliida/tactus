import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `add_capped`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦x⟧
-- leaf 1: ⟦Int⟧
-- leaf 2: ⟦0 ≤ x ∧ x < 18446744073709551616⟧
-- leaf 3: ⟦h_x_bound⟧
-- leaf 4: ⟦y⟧
-- leaf 5: ⟦0 ≤ y ∧ y < 18446744073709551616⟧
-- leaf 6: ⟦h_y_bound⟧
-- leaf 7: ⟦x < 1000⟧
-- leaf 8: ⟦h_req0⟧
-- leaf 9: ⟦y < 1000⟧
-- leaf 10: ⟦h_req1⟧
-- leaf 11: ⟦r = x + y⟧
-- leaf 12: ⟦/- @rust:bootstrap-fixture/lib.rs:85:13 -/ r = x + y⟧
-- leaf 13: ⟦r⟧
-- leaf 14: ⟦bootstrap-fixture/lib.rs:85:13⟧
-- leaf 15: ⟦0 ≤ x + y ∧ x + y < 18446744073709551616⟧
-- leaf 16: ⟦/- @rust:bootstrap-fixture/lib.rs:87:17 -/ 0 ≤ x + y ∧ x + y < 18446744073709551616⟧
-- leaf 17: ⟦bootstrap-fixture/lib.rs:87:17⟧
-- leaf 18: ⟦s⟧
-- leaf 19: ⟦x + y⟧
-- leaf 20: ⟦tmp__1⟧
-- leaf 21: ⟦s < 2000⟧
-- leaf 22: ⟦/- @rust:bootstrap-fixture/lib.rs:88:12 -/ tmp__1⟧
-- leaf 23: ⟦bootstrap-fixture/lib.rs:88:12⟧
-- leaf 24: ⟦0 ≤ s + 0 ∧ s + 0 < 18446744073709551616⟧
-- leaf 25: ⟦/- @rust:bootstrap-fixture/lib.rs:89:9 -/ 0 ≤ s + 0 ∧ s + 0 < 18446744073709551616⟧
-- leaf 26: ⟦bootstrap-fixture/lib.rs:89:9⟧
-- leaf 27: ⟦s + 0⟧

@[reducible] def cert_add_capped_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.BinderList.Cons 8 7 (Tactus.Box.mk (lib.BinderList.Cons 10 9 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)))

@[reducible] def cert_add_capped_sst : lib.StmData :=
  (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Span 17 (Tactus.Box.mk (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt))))))) 15)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 15)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 18 19)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 20 21)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Span 23 (Tactus.Box.mk (lib.RawExp.Var 20 lib.TypData.TyBool))) 20)) (Tactus.Box.mk (lib.StmData.Assume 20)))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert (lib.RawExp.Span 26 (Tactus.Box.mk (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 18 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))))))) 24)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 24)) (Tactus.Box.mk (lib.StmData.Assign 18 27)))))))))))))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Span 14 (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.Var 13 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.BinOp 6 lib.TypData.TyInt (Tactus.Box.mk (lib.RawExp.Var 0 lib.TypData.TyInt)) (Tactus.Box.mk (lib.RawExp.Var 4 lib.TypData.TyInt)))))))) (Tactus.Box.mk lib.RawExpList.Nil))) (lib.RetBind.RetLet 13 18))))

example : lib.stm_size cert_add_capped_sst = 20 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_assert_add_capped_at_lib_87_17_1
-- goal 1: _tactus_assert_add_capped_at_lib_88_12_2
-- goal 2: _tactus_assert_add_capped_at_lib_89_9_3
-- goal 3: _tactus_postcondition_add_capped_at_lib_85_13_4
@[reducible] def cert_add_capped_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 17 (Tactus.Box.mk (lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4)))))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4)))) (Tactus.Box.mk (lib.ExprData.Lit 18446744073709551616))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 23 (Tactus.Box.mk (lib.ExprData.Atom 20))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 26 (Tactus.Box.mk (lib.ExprData.BinOp 11 (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 18)) (Tactus.Box.mk (lib.ExprData.Lit 0)))))) (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 18)) (Tactus.Box.mk (lib.ExprData.Lit 0)))) (Tactus.Box.mk (lib.ExprData.Lit 18446744073709551616))))))))))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Imp 15 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Let 20 21 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 20 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Imp 24 (Tactus.Box.mk (lib.GoalData.Let 18 27 (Tactus.Box.mk (lib.GoalData.Let 13 18 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 14 (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.Atom 13)) (Tactus.Box.mk (lib.ExprData.BinOp 6 (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprData.Atom 4))))))))))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))

example : lib.goal_count cert_add_capped_goals = 4 := by decide
