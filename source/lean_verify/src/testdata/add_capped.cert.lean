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
-- leaf 3: ⟦y⟧
-- leaf 4: ⟦0 ≤ y ∧ y < 18446744073709551616⟧
-- leaf 5: ⟦x < 1000⟧
-- leaf 6: ⟦y < 1000⟧
-- leaf 7: ⟦r = x + y⟧
-- leaf 8: ⟦0 ≤ x + y ∧ x + y < 18446744073709551616⟧
-- leaf 9: ⟦s⟧
-- leaf 10: ⟦x + y⟧
-- leaf 11: ⟦tmp__1⟧
-- leaf 12: ⟦s < 2000⟧
-- leaf 13: ⟦0 ≤ s + 0 ∧ s + 0 < 18446744073709551616⟧
-- leaf 14: ⟦s + 0⟧

@[reducible] def cert_add_capped_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 3 1 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 2 (Tactus.Box.mk (lib.ParamBoundList.Bound 4 (Tactus.Box.mk lib.ParamBoundList.Nil)))) (lib.LeafList.Cons 5 (Tactus.Box.mk (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil)))) (lib.LeafList.Cons 7 (Tactus.Box.mk lib.LeafList.Nil)))

@[reducible] def cert_add_capped_sst : lib.StmData :=
  (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 8)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 8)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 9 10)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assign 11 12)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 11)) (Tactus.Box.mk (lib.StmData.Assume 11)))))) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 13)) (Tactus.Box.mk (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume 13)) (Tactus.Box.mk (lib.StmData.Assign 9 14)))))))))))))) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 7 (Tactus.Box.mk lib.LeafList.Nil))))))

example : lib.stm_size cert_add_capped_sst = 20 := by decide
