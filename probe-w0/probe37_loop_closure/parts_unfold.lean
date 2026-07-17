-- ══ definitional-unfold (rfl) lemmas — used with `simp only`. ══
section Unfold
variable (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int) (st : St)

-- box derefs (generic)
@[simp] theorem u_box_gd (x : lib.GoalData) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_fl (x : lib.FrameList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_gl (x : lib.GoalList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_sd (x : lib.StmData) : (Tactus.Box.mk x).deref = x := rfl

-- emitted reference: frame_append (tail-append) + frame_after Assume/Assert/DeadEnd.
@[simp] theorem u_fapp_fnil (g) : lib.frame_append lib.FrameList.FNil g = g := rfl
@[simp] theorem u_fapp_fbind (id typ t g) :
    lib.frame_append (lib.FrameList.FBind id typ t) g
      = lib.FrameList.FBind id typ (Tactus.Box.mk (lib.frame_append t.deref g)) := rfl
@[simp] theorem u_fa_assume (f e) :
    lib.frame_after f (lib.StmData.Assume e)
      = lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) := rfl
@[simp] theorem u_fa_assert (f o h) :
    lib.frame_after f (lib.StmData.Assert o h)
      = lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) := rfl
-- W5e load-bearing fact: a DeadEnd contributes NOTHING to the continuation frame.
@[simp] theorem u_fa_deadend (f b) :
    lib.frame_after f (lib.StmData.DeadEnd b) = f := rfl
-- Seq threads frame_after through both sub-statements (needed to compute
-- `frame_after f (closure)` = `frame_after f (Seq (DeadEnd _) (Assume ext))`).
@[simp] theorem u_fa_seq (f a b) :
    lib.frame_after f (lib.StmData.Seq a b)
      = lib.frame_after (lib.frame_after f a.deref) b.deref := rfl

-- emitted reference: close_e / close_each_e
@[simp] theorem u_close_FNil (o) :
    lib.close_e lib.FrameList.FNil o = lib.GoalData.LeafE (lib.render_exp o) := rfl
@[simp] theorem u_close_FBind (x ty t o) :
    lib.close_e (lib.FrameList.FBind x ty t) o
      = lib.GoalData.All x ty (Tactus.Box.mk (lib.close_e t.deref o)) := rfl
@[simp] theorem u_close_FHyp (h t o) :
    lib.close_e (lib.FrameList.FHyp h t) o
      = lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e t.deref o)) := rfl
@[simp] theorem u_close_FLet (x v t o) :
    lib.close_e (lib.FrameList.FLet x v t) o
      = lib.GoalData.Let x v (Tactus.Box.mk (lib.close_e t.deref o)) := rfl
@[simp] theorem u_cce_nil (f) : lib.close_each_e f lib.RawExpList.Nil = lib.GoalList.Nil := rfl
@[simp] theorem u_cce_cons (f h t) :
    lib.close_each_e f (lib.RawExpList.Cons h t)
      = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref))
          (Tactus.Box.mk (lib.close_each_e f t.deref)) := rfl

-- emitted reference: wp_stm arms
@[simp] theorem u_wp_skip (f) : lib.wp_stm f lib.StmData.Skip = lib.GoalList.Nil := rfl
@[simp] theorem u_wp_assume (f e) : lib.wp_stm f (lib.StmData.Assume e) = lib.GoalList.Nil := rfl
@[simp] theorem u_wp_assign (f x rhs) : lib.wp_stm f (lib.StmData.Assign x rhs) = lib.GoalList.Nil := rfl
@[simp] theorem u_wp_assert (f o h) :
    lib.wp_stm f (lib.StmData.Assert o h)
      = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) := rfl
@[simp] theorem u_wp_call (f reqs post) :
    lib.wp_stm f (lib.StmData.Call reqs post) = lib.close_each_e f reqs.deref := rfl
@[simp] theorem u_wp_ret (f es rb) :
    lib.wp_stm f (lib.StmData.Ret es rb) = lib.close_each_e (lib.ret_frame f rb) es.deref := rfl
@[simp] theorem u_wp_deadend (f b) :
    lib.wp_stm f (lib.StmData.DeadEnd b) = lib.wp_stm f b.deref := rfl
@[simp] theorem u_wp_seq (f a b) :
    lib.wp_stm f (lib.StmData.Seq a b)
      = lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref) := rfl
@[simp] theorem u_wp_if (f c nc t e) :
    lib.wp_stm f (lib.StmData.If c nc t e)
      = lib.goals_append
          (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref)
          (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) := rfl
@[simp] theorem u_wp_loop (f inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body) :
    lib.wp_stm f (lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body)
      = lib.goals_append (lib.close_each_e f inv_obligs.deref)
          (lib.goals_append
            (lib.wp_stm (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref)
            (lib.goals_append
              (lib.close_each_e (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref) inv_obligs.deref)
              (lib.GoalList.Cons
                (Tactus.Box.mk (lib.close_e (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref) decrease_oblig))
                (Tactus.Box.mk lib.GoalList.Nil)))) := rfl

@[simp] theorem u_gapp_nil (b) : lib.goals_append lib.GoalList.Nil b = b := rfl
@[simp] theorem u_gapp_cons (g t b) :
    lib.goals_append (lib.GoalList.Cons g t) b
      = lib.GoalList.Cons g (Tactus.Box.mk (lib.goals_append t.deref b)) := rfl

-- our semantic defs
@[simp] theorem u_holds_leaf (id) : holds hp he lv (lib.GoalData.Leaf id) st = hp id st := rfl
@[simp] theorem u_holds_leafE (e) :
    holds hp he lv (lib.GoalData.LeafE e) st = he e st := rfl
@[simp] theorem u_holds_imp (h t) :
    holds hp he lv (lib.GoalData.Imp h t) st = (hp h st → holds hp he lv t.deref st) := rfl
@[simp] theorem u_holds_all (x ty t) :
    holds hp he lv (lib.GoalData.All x ty t) st
      = (∀ n : Int, holds hp he lv t.deref (upd st x n)) := rfl
@[simp] theorem u_holds_let (x v t) :
    holds hp he lv (lib.GoalData.Let x v t) st
      = holds hp he lv t.deref (upd st x (lv v st)) := rfl
@[simp] theorem u_holdsAll_nil : holdsAll hp he lv lib.GoalList.Nil st = True := rfl
@[simp] theorem u_holdsAll_cons (g t) :
    holdsAll hp he lv (lib.GoalList.Cons g t) st
      = (holds hp he lv g.deref st ∧ holdsAll hp he lv t.deref st) := rfl
@[simp] theorem u_cs_FNil (body) : closeSem hp he lv lib.FrameList.FNil st body = body st := rfl
@[simp] theorem u_cs_FBind (x ty t body) :
    closeSem hp he lv (lib.FrameList.FBind x ty t) st body
      = (∀ n : Int, closeSem hp he lv t.deref (upd st x n) body) := rfl
@[simp] theorem u_cs_FHyp (h t body) :
    closeSem hp he lv (lib.FrameList.FHyp h t) st body
      = (hp h st → closeSem hp he lv t.deref st body) := rfl
@[simp] theorem u_cs_FLet (x v t body) :
    closeSem hp he lv (lib.FrameList.FLet x v t) st body
      = closeSem hp he lv t.deref (upd st x (lv v st)) body := rfl
@[simp] theorem u_obl_nil : obligsSafe he lib.RawExpList.Nil st = True := rfl
@[simp] theorem u_obl_cons (h t) :
    obligsSafe he (lib.RawExpList.Cons h t) st
      = (he (lib.render_exp h.deref) st ∧ obligsSafe he t.deref st) := rfl

-- execSafeF arms
@[simp] theorem u_exec_skip (f) : execSafeF hp he lv f lib.StmData.Skip st = True := rfl
@[simp] theorem u_exec_assume (f e) : execSafeF hp he lv f (lib.StmData.Assume e) st = True := rfl
@[simp] theorem u_exec_assign (f x rhs) : execSafeF hp he lv f (lib.StmData.Assign x rhs) st = True := rfl
@[simp] theorem u_exec_assert (f o h) :
    execSafeF hp he lv f (lib.StmData.Assert o h) st
      = closeSem hp he lv f st (fun st' => he (lib.render_exp o) st') := rfl
@[simp] theorem u_exec_call (f reqs post) :
    execSafeF hp he lv f (lib.StmData.Call reqs post) st
      = closeSem hp he lv f st (fun st' => obligsSafe he reqs.deref st') := rfl
@[simp] theorem u_exec_ret (f es rb) :
    execSafeF hp he lv f (lib.StmData.Ret es rb) st
      = closeSem hp he lv (lib.ret_frame f rb) st (fun st' => obligsSafe he es.deref st') := rfl
@[simp] theorem u_exec_deadend (f b) :
    execSafeF hp he lv f (lib.StmData.DeadEnd b) st = execSafeF hp he lv f b.deref st := rfl
@[simp] theorem u_exec_if (f c nc t e) :
    execSafeF hp he lv f (lib.StmData.If c nc t e) st
      = (execSafeF hp he lv (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref st
          ∧ execSafeF hp he lv (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref st) := rfl
@[simp] theorem u_exec_seq (f a b) :
    execSafeF hp he lv f (lib.StmData.Seq a b) st
      = (execSafeF hp he lv f a.deref st
          ∧ execSafeF hp he lv (lib.frame_after f a.deref) b.deref st) := rfl
@[simp] theorem u_exec_loop (f inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body) :
    execSafeF hp he lv f (lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body) st
      = (closeSem hp he lv f st (fun st' => obligsSafe he inv_obligs.deref st')
          ∧ (execSafeF hp he lv (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref st
              ∧ (closeSem hp he lv (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref) st (fun st' => obligsSafe he inv_obligs.deref st')
                  ∧ closeSem hp he lv (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref) st (fun st' => he (lib.render_exp decrease_oblig) st')))) := rfl
end Unfold
