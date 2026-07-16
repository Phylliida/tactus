import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5c PROBE (board bootstrap-51) — SOUNDNESS of the reference WP on the
-- FULL statement vocabulary INCLUDING `Loop` (init/maintain/decrease + the
-- havoc'd maintain/use telescopes), proven over the REAL emitted
-- `lib.wp_stm` / `lib.frame_after` / `lib.close_e` / `lib.close_each_e` /
-- `lib.loop_maintain_frame` (tactus-core/out/lib), NO tactus-core rebuild.
--
-- KEY DESIGN LIFT over W5b (probe23) — the "havoc fork" (board bootstrap-51):
--   A Loop's continuation frame is `loop_use_frame f = frame_append
--   (havoc_lets f binders) useTail`, and `havoc_lets` DROPS the modified
--   locals' pre-loop `let`s from the MIDDLE of `f`. So `frame_after f (Loop)`
--   is NOT `frame_append f Δ` — the W5b `frameDelta`/`frame_after_eq_append`
--   lift (a monotone right-append) BREAKS at Loop. Resolution (Opt-2, agreed
--   with Danielle's local model): the operational-safety predicate CARRIES the
--   incoming frame — `execSafeF f s st` — and mirrors `wp_stm f s`'s frame
--   threading structurally. The Loop arm then havocs `f` internally (via the
--   emitted `loop_maintain_frame`), and the four goal groups are each
--   `holdsAll (close_each_e <frame> obligs)` for an OPAQUE frame ∈ {f, mframe,
--   endf} — the existing `holdsAll_close_each_e` bridge handles ANY frame, so
--   `mframe`/the havoc are never decomposed. The obstruction dissolves.
--
-- CONSEQUENCES of frame-carrying execSafeF:
--   • execSafeF is TOTAL on StmData (all 10 constructors) ⇒ the theorem sheds
--     `inFragment` entirely: soundness now holds over the WHOLE vocabulary.
--   • W5b's `frameDelta` / `frame_after_eq_append` / `closeSem_frame_after` /
--     `frame_append_assoc` / `frame_append_fnil_right` / `closeSem_append` /
--     `closeSem_ret_frame` / `retApply` / `diverges` / `is_skip` machinery is
--     all DROPPED — Seq/If/Ret carry the threaded frame directly.
--
-- Valuation-parametric (open Q §5.5 = option b): THREE opaque leaf oracles.
--   hp : Int → St → Prop        opaque prop leaves (hyps + Leaf obligations)
--   he : ExprData → St → Prop    deep obligation exprs (render_exp stays OPAQUE)
--   lv : Int → St → Int          let-value leaves (FLet / GoalData.Let / RetLet)
--
-- THEOREM (wp_stm_sound):
--   holdsAll (wp_stm f s) st ↔ execSafeF f s st           (sound AND faithful)
-- Design + model: DESIGN-W5-soundness.md §1–4 (W5c row) + board bootstrap-51.
-- ══════════════════════════════════════════════════════════════════════

namespace W5c

abbrev St := Int → Int

def upd (st : St) (x n : Int) : St := fun k => if k = x then n else st k

-- ── §2.1 goal denotation (Val-level toProp), faithful on every arm ──
def holds (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (g : lib.GoalData) (st : St) : Prop :=
  match g with
  | lib.GoalData.Leaf id => hp id st
  | lib.GoalData.LeafE e => he e st
  | lib.GoalData.Imp h t => hp h st → holds hp he lv t.deref st
  | lib.GoalData.All x _ t => ∀ n : Int, holds hp he lv t.deref (upd st x n)
  | lib.GoalData.Let x v t => holds hp he lv t.deref (upd st x (lv v st))
termination_by structural g

def holdsAll (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (gs : lib.GoalList) (st : St) : Prop :=
  match gs with
  | lib.GoalList.Nil => True
  | lib.GoalList.Cons g t => holds hp he lv g.deref st ∧ holdsAll hp he lv t.deref st
termination_by structural gs

-- ── the general frame telescope interpretation (FBind→∀, FHyp→→, FLet→let) ──
def closeSem (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (f : lib.FrameList) (st : St) (body : St → Prop) : Prop :=
  match f with
  | lib.FrameList.FNil => body st
  | lib.FrameList.FBind x _ t => ∀ n : Int, closeSem hp he lv t.deref (upd st x n) body
  | lib.FrameList.FHyp h t => hp h st → closeSem hp he lv t.deref st body
  | lib.FrameList.FLet x v t => closeSem hp he lv t.deref (upd st x (lv v st)) body
termination_by structural f

-- ── the conjunction of DEEP obligations in a RawExpList at a state (the
--    semantic content of a `close_each_e` list — Call reqs / Ret enss /
--    Loop init + maintain-reclose invariants) ──
def obligsSafe (he : lib.ExprData → St → Prop) (l : lib.RawExpList) (st : St) : Prop :=
  match l with
  | lib.RawExpList.Nil => True
  | lib.RawExpList.Cons h t => he (lib.render_exp h.deref) st ∧ obligsSafe he t.deref st
termination_by structural l

-- ══ §2.2 operational safety — FRAME-CARRYING (the W5c lift). `execSafeF f s st`
--    mirrors `wp_stm f s`'s frame threading: each obligation is closed under
--    the frame that precedes it via `closeSem`, sequential composition threads
--    `frame_after`, and the Loop havocs `f` internally through the emitted
--    `loop_maintain_frame`. Non-circular: the leaf arms require the ACTUAL
--    obligation (`he (render_exp …)`), never `True` (see non-vacuity witnesses).
noncomputable def execSafeF (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assign _ _ => True
  | lib.StmData.Assert o _ => closeSem hp he lv f st (fun st' => he (lib.render_exp o) st')
  | lib.StmData.Call reqs _ => closeSem hp he lv f st (fun st' => obligsSafe he reqs.deref st')
  | lib.StmData.Ret es rb =>
      closeSem hp he lv (lib.ret_frame f rb) st (fun st' => obligsSafe he es.deref st')
  | lib.StmData.DeadEnd b => execSafeF hp he lv f b.deref st
  | lib.StmData.If c nc t e =>
      execSafeF hp he lv (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref st
        ∧ execSafeF hp he lv (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref st
  | lib.StmData.Seq a b =>
      execSafeF hp he lv f a.deref st
        ∧ execSafeF hp he lv (lib.frame_after f a.deref) b.deref st
  | lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body =>
      let mframe := lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val
      let endf := lib.frame_after mframe body.deref
      closeSem hp he lv f st (fun st' => obligsSafe he inv_obligs.deref st')
        ∧ (execSafeF hp he lv mframe body.deref st
            ∧ (closeSem hp he lv endf st (fun st' => obligsSafe he inv_obligs.deref st')
                ∧ closeSem hp he lv endf st (fun st' => he (lib.render_exp decrease_oblig) st')))
termination_by structural s

-- ══ definitional-unfold (rfl) lemmas — used with `simp only`. ══
section Unfold
variable (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int) (st : St)

-- box derefs (generic)
@[simp] theorem u_box_gd (x : lib.GoalData) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_fl (x : lib.FrameList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_gl (x : lib.GoalList) : (Tactus.Box.mk x).deref = x := rfl

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
-- the Loop arm: the four goal groups (init ++ body ++ maintain-reclose ++ decrease).
-- `let`s reduce definitionally ⇒ this is `rfl`.
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

-- ══ closeSem structural lemmas (congruence / triviality / conjunction / mono) ══

theorem closeSem_congr (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (st : St) (P Q : St → Prop)
    (h : ∀ st', P st' ↔ Q st') :
    closeSem hp he lv f st P ↔ closeSem hp he lv f st Q := by
  match f with
  | lib.FrameList.FNil => simp only [u_cs_FNil]; exact h st
  | lib.FrameList.FBind x ty t =>
      simp only [u_cs_FBind]
      constructor
      · intro hh n; exact (closeSem_congr hp he lv t.deref (upd st x n) P Q h).mp (hh n)
      · intro hh n; exact (closeSem_congr hp he lv t.deref (upd st x n) P Q h).mpr (hh n)
  | lib.FrameList.FHyp hh t =>
      simp only [u_cs_FHyp]
      constructor
      · intro k a; exact (closeSem_congr hp he lv t.deref st P Q h).mp (k a)
      · intro k a; exact (closeSem_congr hp he lv t.deref st P Q h).mpr (k a)
  | lib.FrameList.FLet x v t =>
      simp only [u_cs_FLet]
      exact closeSem_congr hp he lv t.deref (upd st x (lv v st)) P Q h
termination_by f
decreasing_by all_goals (simp_all; omega)

theorem closeSem_triv (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (st : St) :
    closeSem hp he lv f st (fun _ => True) := by
  match f with
  | lib.FrameList.FNil => simp only [u_cs_FNil]
  | lib.FrameList.FBind x ty t =>
      simp only [u_cs_FBind]; intro n; exact closeSem_triv hp he lv t.deref (upd st x n)
  | lib.FrameList.FHyp h t =>
      simp only [u_cs_FHyp]; intro _; exact closeSem_triv hp he lv t.deref st
  | lib.FrameList.FLet x v t =>
      simp only [u_cs_FLet]; exact closeSem_triv hp he lv t.deref (upd st x (lv v st))
termination_by f
decreasing_by all_goals (simp_all; omega)

theorem closeSem_mono (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (st : St) (P Q : St → Prop)
    (himp : ∀ st', P st' → Q st') (hP : closeSem hp he lv f st P) :
    closeSem hp he lv f st Q := by
  match f with
  | lib.FrameList.FNil => simp only [u_cs_FNil] at hP ⊢; exact himp st hP
  | lib.FrameList.FBind x ty t =>
      simp only [u_cs_FBind] at hP ⊢
      intro n; exact closeSem_mono hp he lv t.deref (upd st x n) P Q himp (hP n)
  | lib.FrameList.FHyp h t =>
      simp only [u_cs_FHyp] at hP ⊢
      intro a; exact closeSem_mono hp he lv t.deref st P Q himp (hP a)
  | lib.FrameList.FLet x v t =>
      simp only [u_cs_FLet] at hP ⊢
      exact closeSem_mono hp he lv t.deref (upd st x (lv v st)) P Q himp hP
termination_by f
decreasing_by all_goals (simp_all; omega)

theorem closeSem_and (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (st : St) (P Q : St → Prop)
    (hP : closeSem hp he lv f st P) (hQ : closeSem hp he lv f st Q) :
    closeSem hp he lv f st (fun st' => P st' ∧ Q st') := by
  match f with
  | lib.FrameList.FNil =>
      simp only [u_cs_FNil] at hP hQ ⊢; exact ⟨hP, hQ⟩
  | lib.FrameList.FBind x ty t =>
      simp only [u_cs_FBind] at hP hQ ⊢
      intro n; exact closeSem_and hp he lv t.deref (upd st x n) P Q (hP n) (hQ n)
  | lib.FrameList.FHyp h t =>
      simp only [u_cs_FHyp] at hP hQ ⊢
      intro a; exact closeSem_and hp he lv t.deref st P Q (hP a) (hQ a)
  | lib.FrameList.FLet x v t =>
      simp only [u_cs_FLet] at hP hQ ⊢
      exact closeSem_and hp he lv t.deref (upd st x (lv v st)) P Q hP hQ
termination_by f
decreasing_by all_goals (simp_all; omega)

-- closeSem distributes over ∧ as an IFF (forward = closeSem_and, backward = mono×2)
theorem closeSem_and_iff (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (st : St) (P Q : St → Prop) :
    closeSem hp he lv f st (fun st' => P st' ∧ Q st')
      ↔ (closeSem hp he lv f st P ∧ closeSem hp he lv f st Q) := by
  constructor
  · intro h
    exact ⟨closeSem_mono hp he lv f st _ P (fun st' hh => hh.1) h,
           closeSem_mono hp he lv f st _ Q (fun st' hh => hh.2) h⟩
  · intro ⟨hP, hQ⟩; exact closeSem_and hp he lv f st P Q hP hQ

-- ── Lemma A (close): a frame-closed obligation holds iff the obligation expr
--    holds under the frame's ∀/→/let telescope. render_exp stays opaque (he). ──
theorem holds_close_e (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (o : lib.RawExp) (st : St) :
    holds hp he lv (lib.close_e f o) st
      ↔ closeSem hp he lv f st (fun st' => he (lib.render_exp o) st') := by
  match f with
  | lib.FrameList.FNil => simp only [u_close_FNil, u_holds_leafE, u_cs_FNil]
  | lib.FrameList.FBind x ty t =>
      simp only [u_close_FBind, u_holds_all, u_cs_FBind]
      constructor
      · intro hh n; exact (holds_close_e hp he lv t.deref o (upd st x n)).mp (hh n)
      · intro hh n; exact (holds_close_e hp he lv t.deref o (upd st x n)).mpr (hh n)
  | lib.FrameList.FHyp h t =>
      simp only [u_close_FHyp, u_holds_imp, u_cs_FHyp]
      constructor
      · intro k a; exact (holds_close_e hp he lv t.deref o st).mp (k a)
      · intro k a; exact (holds_close_e hp he lv t.deref o st).mpr (k a)
  | lib.FrameList.FLet x v t =>
      simp only [u_close_FLet, u_holds_let, u_cs_FLet]
      exact holds_close_e hp he lv t.deref o (upd st x (lv v st))
termination_by f
decreasing_by all_goals (simp_all; omega)

-- ── Lemma D (goals_append) ──
theorem holdsAll_append (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (a b : lib.GoalList) (st : St) :
    holdsAll hp he lv (lib.goals_append a b) st
      ↔ holdsAll hp he lv a st ∧ holdsAll hp he lv b st := by
  match a with
  | lib.GoalList.Nil => simp
  | lib.GoalList.Cons g t =>
      simp only [u_gapp_cons, u_holdsAll_cons]
      rw [holdsAll_append hp he lv t.deref b st]
      simp only [and_assoc]
termination_by a
decreasing_by all_goals (simp_all; omega)

-- ── close_each_e bridge: a closed obligation list holds iff every obligation
--    holds under the telescope (the Call reqs / Ret enss / Loop init +
--    maintain-reclose soundness core; works for ANY frame — incl. the havoc'd
--    mframe/endf, so the Loop's havoc is never decomposed) ──
theorem holdsAll_close_each_e (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (l : lib.RawExpList) (st : St) :
    holdsAll hp he lv (lib.close_each_e f l) st
      ↔ closeSem hp he lv f st (fun st' => obligsSafe he l st') := by
  match l with
  | lib.RawExpList.Nil =>
      simp only [u_cce_nil, u_holdsAll_nil]
      constructor
      · intro _
        exact (closeSem_congr hp he lv f st (fun _ => True) _
                 (fun st' => by simp only [u_obl_nil])).mp (closeSem_triv hp he lv f st)
      · intro _; trivial
  | lib.RawExpList.Cons h t =>
      simp only [u_cce_cons, u_holdsAll_cons]
      rw [holds_close_e hp he lv f h.deref st, holdsAll_close_each_e hp he lv f t.deref st]
      rw [← closeSem_and_iff hp he lv f st]
      exact closeSem_congr hp he lv f st _ _ (fun st' => by simp only [u_obl_cons])
termination_by l
decreasing_by all_goals (simp_all; omega)

-- ══ MAIN: reference-WP soundness (AND faithfulness) on the FULL StmData
--    vocabulary — Skip/Assume/Assign/Assert/Call/Ret/DeadEnd/If/Seq/Loop —
--    over an ARBITRARY frame telescope. No `inFragment` restriction. ══
theorem wp_stm_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (s : lib.StmData) (f : lib.FrameList) (st : St) :
    holdsAll hp he lv (lib.wp_stm f s) st ↔ execSafeF hp he lv f s st := by
  match s with
  | lib.StmData.Skip => simp only [u_wp_skip, u_holdsAll_nil, u_exec_skip]
  | lib.StmData.Assume e => simp only [u_wp_assume, u_holdsAll_nil, u_exec_assume]
  | lib.StmData.Assign x rhs => simp only [u_wp_assign, u_holdsAll_nil, u_exec_assign]
  | lib.StmData.Assert o h =>
      simp only [u_wp_assert, u_holdsAll_cons, u_holdsAll_nil, and_true, u_exec_assert]
      exact holds_close_e hp he lv f o st
  | lib.StmData.Call reqs post =>
      simp only [u_wp_call, u_exec_call]
      exact holdsAll_close_each_e hp he lv f reqs.deref st
  | lib.StmData.Ret es rb =>
      simp only [u_wp_ret, u_exec_ret]
      exact holdsAll_close_each_e hp he lv (lib.ret_frame f rb) es.deref st
  | lib.StmData.DeadEnd b =>
      simp only [u_wp_deadend, u_exec_deadend]
      exact wp_stm_sound hp he lv b.deref f st
  | lib.StmData.Seq a b =>
      simp only [u_wp_seq, u_exec_seq]
      rw [holdsAll_append hp he lv _ _ st]
      rw [wp_stm_sound hp he lv a.deref f st,
          wp_stm_sound hp he lv b.deref (lib.frame_after f a.deref) st]
  | lib.StmData.If c nc t e =>
      simp only [u_wp_if, u_exec_if]
      rw [holdsAll_append hp he lv _ _ st]
      rw [wp_stm_sound hp he lv t.deref
            (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) st,
          wp_stm_sound hp he lv e.deref
            (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) st]
  | lib.StmData.Loop inv_hyps inv_obligs binders binder_bounds cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig body =>
      simp only [u_wp_loop, u_exec_loop]
      rw [holdsAll_append hp he lv _ _ st, holdsAll_append hp he lv _ _ st,
          holdsAll_append hp he lv _ _ st]
      -- init + maintain-reclose via the close_each_e bridge; body via IH; decrease
      -- via holds_close_e (singleton list).
      rw [holdsAll_close_each_e hp he lv f inv_obligs.deref st]
      rw [wp_stm_sound hp he lv body.deref
            (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) st]
      rw [holdsAll_close_each_e hp he lv
            (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref)
            inv_obligs.deref st]
      simp only [u_holdsAll_cons, u_holdsAll_nil, and_true]
      rw [holds_close_e hp he lv
            (lib.frame_after (lib.loop_maintain_frame f inv_hyps.deref binders.deref binder_bounds.deref cond_name cond_ann d_old_name d_old_val) body.deref)
            decrease_oblig st]
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── top-level: ref_wp soundness (seeded through the genuine seed_frame). ──
theorem ref_wp_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (c : lib.FnCtxData) (s : lib.StmData) (st : St) :
    holdsAll hp he lv (lib.ref_wp c s) st ↔ execSafeF hp he lv (lib.seed_frame c) s st := by
  have hrw : lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s := rfl
  rw [hrw]
  exact wp_stm_sound hp he lv s (lib.seed_frame c) st

-- ══ NON-VACUITY witnesses. ══

-- (1) Loop INIT: the invariant obligation must hold on ENTRY, at the pre-loop
--     state (opaque `he`, so it can only come from the emitted init goal).
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (inv_hyps binders : lib.BinderList) (binder_bounds : lib.ParamBoundList)
    (ob : lib.RawExp) (cond_name cond_ann neg_cond_ann d_old_name d_old_val : Int)
    (decrease_oblig : lib.RawExp) (body : lib.StmData) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Loop (Tactus.Box.mk inv_hyps)
                 (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk ob) (Tactus.Box.mk lib.RawExpList.Nil)))
                 (Tactus.Box.mk binders) (Tactus.Box.mk binder_bounds)
                 cond_name cond_ann neg_cond_ann d_old_name d_old_val decrease_oblig
                 (Tactus.Box.mk body))) st) :
    he (lib.render_exp ob) st := by
  have hsound := (wp_stm_sound hp he lv _ lib.FrameList.FNil st).mp hg
  simp only [u_exec_loop, u_cs_FNil, u_obl_cons, u_obl_nil, and_true] at hsound
  exact hsound.1

-- (2) Loop DECREASE: the decrease obligation must hold at the body-end state
--     `closeSem endf` (opaque `he`); here with FNil pre-loop frame the maintain
--     frame is still non-trivial, so we witness the decrease goal is delivered.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (inv_hyps binders : lib.BinderList) (binder_bounds : lib.ParamBoundList)
    (cond_name cond_ann neg_cond_ann d_old_name d_old_val : Int)
    (dec : lib.RawExp) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Loop (Tactus.Box.mk inv_hyps)
                 (Tactus.Box.mk lib.RawExpList.Nil)
                 (Tactus.Box.mk binders) (Tactus.Box.mk binder_bounds)
                 cond_name cond_ann neg_cond_ann d_old_name d_old_val dec
                 (Tactus.Box.mk lib.StmData.Skip))) st) :
    closeSem hp he lv
      (lib.frame_after (lib.loop_maintain_frame lib.FrameList.FNil inv_hyps binders binder_bounds cond_name cond_ann d_old_name d_old_val) lib.StmData.Skip)
      st (fun st' => he (lib.render_exp dec) st') := by
  have hsound := (wp_stm_sound hp he lv _ lib.FrameList.FNil st).mp hg
  simp only [u_exec_loop] at hsound
  exact hsound.2.2.2

end W5c

-- axiom closure (regression guard): the soundness theorems close over ONLY the
-- standard logical axioms — no `Classical.choice` (render_exp stays opaque),
-- no `sorryAx`, no smuggled axioms.
#print axioms W5c.wp_stm_sound   -- expect [propext, Quot.sound]
#print axioms W5c.ref_wp_sound   -- expect [propext, Quot.sound]
