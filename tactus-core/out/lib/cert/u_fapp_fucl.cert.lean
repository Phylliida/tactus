import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false

-- tactus certificate (stage A) — crate `lib`, fn `u_fapp_fucl`
-- tactus-core-vocab-hash: unvendored
-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis
-- order, let-chains, obligation multiplicity/order). It does NOT certify
-- leaf rendering (stage B/W6), the serializer (it is the TCB), the
-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;
-- a stage-A pass coexisting with a leaf-renderer bug is possible.

-- ── leaf table ──────────────────────────────────────────────
-- leaf 0: ⟦t⟧
-- leaf 1: ⟦Tactus.Box lib.FrameList⟧
-- leaf 2: ⟦g⟧
-- leaf 3: ⟦lib.FrameList⟧
-- leaf 4: ⟦lib.frame_append (lib.FrameList.FUserCloser t) g = lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t g))⟧
-- leaf 5: ⟦/- @rust:tactus-core/lib.rs:6488:13 -/ lib.frame_append (lib.FrameList.FUserCloser t) g = lib.FrameList.FUserCloser (Tactus.Box.mk (lib.frame_append t.deref g))⟧
-- leaf 6: ⟦lib.frame_append⟧

@[reducible] def cert_u_fapp_fucl_ctx : lib.FnCtxData :=
  (lib.FnCtxData.mk lib.BinderList.Nil (lib.BinderList.Cons 0 1 (Tactus.Box.mk (lib.BinderList.Cons 2 3 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.NoBound (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.BinderList.Nil lib.MutParamList.Nil (lib.LeafList.Cons 4 (Tactus.Box.mk lib.LeafList.Nil)) lib.LeafList.Nil lib.PropDeepList.Nil 1)

@[reducible] def cert_u_fapp_fucl_sst : lib.StmData :=
  (lib.StmData.Ret (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk (lib.RawExp.Var 5 lib.TypData.TyBool)) (Tactus.Box.mk lib.RawExpList.Nil))) lib.RetBind.RetNone)

example : lib.stm_size cert_u_fapp_fucl_sst = 2 := by decide

-- ── production goals (N3b) ──────────────────────────────────
-- goal 0: _tactus_postcondition_u_fapp_fucl_at_lib_6488_13_1
@[reducible] def cert_u_fapp_fucl_goals : lib.GoalList :=
  lib.GoalList.Cons (Tactus.Box.mk (lib.GoalData.All 0 1 (Tactus.Box.mk (lib.GoalData.All 2 3 (Tactus.Box.mk (lib.GoalData.LeafE (lib.ExprData.Atom 5))))))) (Tactus.Box.mk lib.GoalList.Nil)

example : lib.goal_count cert_u_fapp_fucl_goals = 1 := by decide
