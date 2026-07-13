import TactusStmts_lib_exec__lib__amended_shapes_kernel_compute
import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
set_option autoImplicit false
theorem lib.amended_shapes_kernel_compute :
    lib.stm_size (lib.StmData.Loop (Tactus.Box.mk (lib.LeafList.Cons 0 (Tactus.Box.mk lib.LeafList.Nil))) 1 2 (Tactus.Box.mk (lib.BinderList.Cons 3 4 (Tactus.Box.mk lib.BinderList.Nil))) (Tactus.Box.mk lib.StmData.Skip)) = 4 ∧ lib.stm_size (lib.StmData.Call (Tactus.Box.mk (lib.LeafList.Cons 0 (Tactus.Box.mk lib.LeafList.Nil))) (Tactus.Box.mk lib.LeafList.Nil) 5 6) = 2 ∧ lib.stm_size (lib.StmData.Ret (Tactus.Box.mk (lib.LeafList.Cons 0 (Tactus.Box.mk (lib.LeafList.Cons 1 (Tactus.Box.mk lib.LeafList.Nil)))))) = 3 ∧ lib.binder_len (lib.BinderList.Cons 1 2 (Tactus.Box.mk lib.BinderList.Nil)) = 1 ∧ lib.param_bound_len (lib.ParamBoundList.Bound 5 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) = 2 ∧ lib.frame_len (lib.FrameList.FBind 1 2 (Tactus.Box.mk (lib.FrameList.FHyp 3 (Tactus.Box.mk (lib.FrameList.FLet 4 5 (Tactus.Box.mk lib.FrameList.FNil)))))) = 3 ∧ lib.fnctx_arity (lib.FnCtxData.mk (lib.BinderList.Cons 0 100 (Tactus.Box.mk lib.BinderList.Nil)) (lib.BinderList.Cons 1 101 (Tactus.Box.mk (lib.BinderList.Cons 2 102 (Tactus.Box.mk lib.BinderList.Nil)))) (lib.ParamBoundList.Bound 200 (Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))) lib.LeafList.Nil (lib.LeafList.Cons 300 (Tactus.Box.mk lib.LeafList.Nil))) = 2 := by

  decide
