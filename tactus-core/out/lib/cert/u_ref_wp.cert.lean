import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_ref_wp`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦c⟧
-- leaf 1: ⟦lib.FnCtxData⟧
-- leaf 2: ⟦0 ≤ c.closer_default ∧ c.closer_default < 18446744073709551616⟧
-- leaf 3: ⟦h_c_bound⟧
-- leaf 4: ⟦s⟧
-- leaf 5: ⟦lib.StmData⟧
-- leaf 6: ⟦lib.ref_wp c s = lib.wp_stm (lib.poisoned_props c) (lib.seed_frame c) s⟧
-- leaf 7: ⟦/- @rust:tactus-core/lib.rs:6382:13 -/ lib.ref_wp c s = lib.wp_stm (lib.poisoned_props c) (lib.seed_frame c) s⟧
-- leaf 8: ⟦lib.ref_wp⟧
-- leaf 9: ⟦lib.GoalList⟧
-- leaf 10: ⟦lib.wp_stm⟧
-- leaf 11: ⟦lib.FrameList⟧
-- leaf 12: ⟦lib.seed_frame⟧
-- leaf 13: ⟦lib.LeafList⟧
-- leaf 14: ⟦lib.poisoned_props⟧
-- leaf 15: ⟦tactus-core/lib.rs:6382:13⟧

@[reducible] def cert_u_ref_wp_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 3 2 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_ref_wp_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Span 15 (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.CallN 8 (lib.TypData.TyNamed 9) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 1) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 5))) (lib.TypData.TyNamed 5) (Tactus.Box.mk lib.RawList.Nil))))))) (Tactus.Box.mk (lib.RawExp.CallN 10 (lib.TypData.TyNamed 9) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Call 14 (lib.TypData.TyNamed 13) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 13) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Call 12 (lib.TypData.TyNamed 11) (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 11) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 5))) (lib.TypData.TyNamed 5) (Tactus.Box.mk lib.RawList.Nil))))))))))))) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_ref_wp_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_ref_wp_at_lib_6382_13_1
@[reducible] def cert_u_ref_wp_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 3 2 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 15 (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.AppN 8 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk lib.ExprList.Nil))))))) (Tactus.Box.mk (lib.ExprData.AppN 10 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.App 14 (Tactus.Box.mk (lib.ExprData.Atom 0)))) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.App 12 (Tactus.Box.mk (lib.ExprData.Atom 0)))) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk lib.ExprList.Nil)))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_ref_wp_goals = 1 := by decide
