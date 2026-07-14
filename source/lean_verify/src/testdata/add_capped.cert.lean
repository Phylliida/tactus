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
-- leaf 14: ⟦0 ≤ x + y ∧ x + y < 18446744073709551616⟧
-- leaf 15: ⟦/- @rust:bootstrap-fixture/lib.rs:87:17 -/ 0 ≤ x + y ∧ x + y < 18446744073709551616⟧
-- leaf 16: ⟦s⟧
-- leaf 17: ⟦x + y⟧
-- leaf 18: ⟦tmp__1⟧
-- leaf 19: ⟦s < 2000⟧
-- leaf 20: ⟦/- @rust:bootstrap-fixture/lib.rs:88:12 -/ tmp__1⟧
-- leaf 21: ⟦0 ≤ s + 0 ∧ s + 0 < 18446744073709551616⟧
-- leaf 22: ⟦/- @rust:bootstrap-fixture/lib.rs:89:9 -/ 0 ≤ s + 0 ∧ s + 0 < 18446744073709551616⟧
-- leaf 23: ⟦s + 0⟧

@[reducible] def cert_add_capped_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 6 5 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.BinderList.Cons 8 7 (Tactus.Box.mk (lib.BinderList.Cons 10 9 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.LeafList.Cons 11 (Tactus.Box.mk lib.LeafList.Nil)))

@[reducible] def cert_add_capped_sst : lib.StmData :=
  (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 15 14)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 14)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 16 17)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 18 19)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 20 18)) (Tactus.Box.mk (lib.StmData.Assume 18)))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 22 21)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 21)) (Tactus.Box.mk (lib.StmData.Assign 16 23)))))))))))))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 12 (Tactus.Box.mk lib.LeafList.Nil))) (lib.RetBind.RetLet 13 16))))

example : lib.stm_size cert_add_capped_sst = 20 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_assert_add_capped_at_lib_87_17_1
-- goal 1: _tactus_assert_add_capped_at_lib_88_12_2
-- goal 2: _tactus_assert_add_capped_at_lib_89_9_3
-- goal 3: _tactus_postcondition_add_capped_at_lib_85_13_4
@[reducible] def cert_add_capped_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Leaf 15)))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Let 16 17 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Leaf 20)))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Let 16 17 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Imp 18 (Tactus.Box.mk (lib.GoalData.Imp 18 (Tactus.Box.mk (lib.GoalData.Leaf 22)))))))))))))))))))))))))) (Tactus.Box.mk (lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 1 (Tactus.Box.mk (lib.GoalData.All 6 5 (Tactus.Box.mk (lib.GoalData.All 8 7 (Tactus.Box.mk (lib.GoalData.All 10 9 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Imp 14 (Tactus.Box.mk (lib.GoalData.Let 16 17 (Tactus.Box.mk (lib.GoalData.Let 18 19 (Tactus.Box.mk (lib.GoalData.Imp 18 (Tactus.Box.mk (lib.GoalData.Imp 18 (Tactus.Box.mk (lib.GoalData.Imp 21 (Tactus.Box.mk (lib.GoalData.Imp 21 (Tactus.Box.mk (lib.GoalData.Let 16 23 (Tactus.Box.mk (lib.GoalData.Let 13 16 (Tactus.Box.mk (lib.GoalData.Leaf 12)))))))))))))))))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)))))))

example : lib.goal_count cert_add_capped_goals = 4 := by decide
