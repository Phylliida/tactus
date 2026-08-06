import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_gapp_cons`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦h⟧
-- leaf 1: ⟦Tactus.Box lib.GoalData⟧
-- leaf 2: ⟦t⟧
-- leaf 3: ⟦Tactus.Box lib.GoalList⟧
-- leaf 4: ⟦b⟧
-- leaf 5: ⟦lib.GoalList⟧
-- leaf 6: ⟦lib.goals_append (lib.GoalList.Cons h t) b = lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t b))⟧
-- leaf 7: ⟦/- @rust:tactus-core/lib.rs:5227:13 -/ lib.goals_append (lib.GoalList.Cons h t) b = lib.GoalList.Cons h (Tactus.Box.mk (lib.goals_append t.deref b))⟧
-- leaf 8: ⟦lib.goals_append⟧

@[reducible] def cert_u_gapp_cons_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk (lib.BinderList.Cons 4 5 (Tactus.Box.mk lib.BinderList.Nil)))))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 6 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_gapp_cons_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 7 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_gapp_cons_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_gapp_cons_at_lib_5227_13_1
@[reducible] def cert_u_gapp_cons_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.All 4 5 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 7))))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_gapp_cons_goals = 1 := by decide
