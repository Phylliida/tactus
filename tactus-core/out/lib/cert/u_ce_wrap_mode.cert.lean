import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_ce_wrap_mode`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦pp⟧
-- leaf 1: ⟦lib.LeafList⟧
-- leaf 2: ⟦f⟧
-- leaf 3: ⟦lib.FrameList⟧
-- leaf 4: ⟦ob⟧
-- leaf 5: ⟦lib.RawExp⟧
-- leaf 6: ⟦lib.gate_wrap pp f = 1 → lib.close_e pp f ob = lib.close_e_wrap_lead f ob⟧
-- leaf 7: ⟦/- @rust:tactus-core/lib.rs:5114:13 -/ lib.gate_wrap pp f = 1 → lib.close_e pp f ob = lib.close_e_wrap_lead f ob⟧
-- leaf 8: ⟦lib.gate_wrap⟧
-- leaf 9: ⟦lib.close_e⟧
-- leaf 10: ⟦lib.GoalData⟧
-- leaf 11: ⟦lib.close_e_wrap_lead⟧
-- leaf 12: ⟦tactus-core/lib.rs:5114:13⟧

@[reducible] def cert_u_ce_wrap_mode_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_ce_wrap_mode_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Span 12 (Tactus.Box.mk (lib.RawExp.BinOp 13 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.CallN 8 lib.TypData.TyNat (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 1) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 2 (lib.TypData.TyNamed 3))) (lib.TypData.TyNamed 3) (Tactus.Box.mk lib.RawList.Nil))))))) (Tactus.Box.mk (lib.RawExp.Lit 1 lib.TypData.TyNat)))) (Tactus.Box.mk (lib.RawExp.BinOp 0 lib.TypData.TyBool (Tactus.Box.mk (lib.RawExp.CallN 9 (lib.TypData.TyNamed 10) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 0 (lib.TypData.TyNamed 1))) (lib.TypData.TyNamed 1) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 2 (lib.TypData.TyNamed 3))) (lib.TypData.TyNamed 3) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 5))) (lib.TypData.TyNamed 5) (Tactus.Box.mk lib.RawList.Nil))))))))) (Tactus.Box.mk (lib.RawExp.CallN 11 (lib.TypData.TyNamed 10) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 2 (lib.TypData.TyNamed 3))) (lib.TypData.TyNamed 3) (Tactus.Box.mk (lib.RawList.Cons (Tactus.Box.mk (lib.RawExp.Var 4 (lib.TypData.TyNamed 5))) (lib.TypData.TyNamed 5) (Tactus.Box.mk lib.RawList.Nil))))))))))))) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_ce_wrap_mode_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_ce_wrap_mode_at_lib_5114_13_1
@[reducible] def cert_u_ce_wrap_mode_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.SpanMark 12 (Tactus.Box.mk (lib.ExprData.BinOp 13 (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.AppN 8 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 2)) (Tactus.Box.mk lib.ExprList.Nil))))))) (Tactus.Box.mk (lib.ExprData.Lit 1)))) (Tactus.Box.mk (lib.ExprData.BinOp 0 (Tactus.Box.mk (lib.ExprData.AppN 9 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 0)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 2)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk lib.ExprList.Nil))))))))) (Tactus.Box.mk (lib.ExprData.AppN 11 (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 2)) (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom 4)) (Tactus.Box.mk lib.ExprList.Nil)))))))))))))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_ce_wrap_mode_goals = 1 := by decide
