import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5e PROBE (board bootstrap-53) — SOUNDNESS of the reference WP for
-- CLOSURES, proven over the REAL emitted `lib.wp_stm` / `lib.frame_after` /
-- `lib.frame_append` / `lib.close_e` (tactus-core/out/lib), NO tactus-core
-- rebuild.
--
-- CARRIES OVER the full W5c core (probe24, via probe25): the frame-carrying
-- `execSafeF`, the iff soundness theorem `wp_stm_sound : holdsAll (wp_stm f s) st
-- ↔ execSafeF f s st` TOTAL over the whole StmData vocabulary (Skip/Assume/
-- Assign/Assert/Call/Ret/DeadEnd/If/Seq/Loop) over an ARBITRARY frame telescope.
-- W5e — like W5d (prophecy) — adds NO new StmData arm: a closure is modeled
-- ENTIRELY by the EXISTING `DeadEnd` + `Assume` constructors.
--
-- HOW VERUS ACTUALLY ENCODES A CLOSURE (verified from the verus source, NOT
-- reasoned from first principles):
--   An exec/proof closure `NonSpecClosure{params,body,requires,ensures,ret,
--   external_spec}` (verus/source/vir/src/ast.rs:1058) lowers to exactly TWO
--   SST statements (ast_to_sst.rs:1964–2003):
--     1. `ClosureInner{body}` — which sst_to_air.rs:2548–2566 compiles to
--        `StmtX::DeadEnd(body)` (modulo prepended captured-var typ-invariant
--        Assumes). The body itself (exec_closure_body_stms, ast_to_sst.rs:3556)
--        is ordinary statements: `Assume(req)` for each requires, the body, then
--        `init_var(ret)` + `Assert(ens)` for each ensures. Pure W5a–c vocabulary.
--     2. `Assume(external_spec)` — the contract the surrounding world may assume
--        about the closure OBJECT after creation (∀ args, ClosureReq→ClosureEns).
--   So a closure  ≈  `Seq (DeadEnd body) (Assume ext)`.  Both constructors are
--   already in the vocabulary; there is NO closure-specific StmData constructor.
--   (Spec closures `ExprX::Closure` lower to a pure `BndX::Lambda` expression —
--   an opaque `he∘render_exp` leaf — preceded only by ordinary spec-precondition
--   Asserts; no new statement structure either.)
--
-- THE LOAD-BEARING EMITTED FACTS (both `rfl`, restated as u_* below):
--   • `frame_after f (DeadEnd b) = f`      — a DeadEnd contributes NOTHING to the
--     continuation frame: the closure body's local hyps (its `requires`, its
--     params) are QUARANTINED — they never contaminate downstream obligations.
--     This ISOLATION is exactly what makes it sound to verify the body under its
--     own `requires` without those requires leaking to sibling code.
--   • `wp_stm f (DeadEnd b) = wp_stm f b`  — the body's obligations are emitted
--     under the ENCLOSING frame `f` (the closure captures the outer context).
--
-- SO the three W5e facts (all instantiations of the W5c iff):
--   1. closure_creation_sound : the reference WP for `Seq (DeadEnd body) (Assume
--      ext)` reduces EXACTLY to `execSafeF f body st` — the closure-creation
--      obligation is precisely the body obligation under `f`; the external-spec
--      Assume and the DeadEnd wrapper add no obligation.
--   2. closure_deadend_isolates : `Seq (DeadEnd (Assume q)) (Assert P)` leaves P
--      UNGATED by q, whereas the bare `Seq (Assume q) (Assert P)` GATES P by q —
--      the DeadEnd genuinely quarantines the body's assumption (the W5e analog of
--      W5d's temporal-placement witness). The two reduced forms DIFFER.
--   3. closure_forwards_contract : after the closure, the continuation DOES see
--      the external_spec — `Seq (closure) (Assert P)` gates P by `hp ext` — the
--      Assume threads the closure contract forward (the analog of the resolve
--      pin). Plus the closure body obligation is delivered alongside.
--   + a ∀-PARAMS witness: the closure body obligation is checked for EVERY
--      valuation of a param id (they are fresh ids covered by the outer ∀ st, NOT
--      the creation-time value) — refutes "closure verified for one param value".
--
-- Valuation-parametric (open Q §5.5 = option b): THREE opaque leaf oracles.
--   hp : Int → St → Prop        opaque prop leaves (hyps + Leaf obligations)
--   he : ExprData → St → Prop    deep obligation exprs (render_exp stays OPAQUE)
--   lv : Int → St → Int          let-value leaves (FLet / GoalData.Let / RetLet)
--
-- Design + model: DESIGN-W5-soundness.md §4 (W5e row) + board bootstrap-53.
-- Extends probe25 (W5d).
-- ══════════════════════════════════════════════════════════════════════

namespace W5e

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

-- ── the conjunction of DEEP obligations in a RawExpList at a state ──
def obligsSafe (he : lib.ExprData → St → Prop) (l : lib.RawExpList) (st : St) : Prop :=
  match l with
  | lib.RawExpList.Nil => True
  | lib.RawExpList.Cons h t => he (lib.render_exp h.deref) st ∧ obligsSafe he t.deref st
termination_by structural l

-- ══ §2.2 operational safety — FRAME-CARRYING (the W5c lift). ══
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

-- ── Lemma A (close) ──
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

-- ── close_each_e bridge ──
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
--    vocabulary over an ARBITRARY frame telescope. No `inFragment`. ══
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

-- ══════════════════════════════════════════════════════════════════════
-- W5e: CLOSURES — modeled by the EXISTING `DeadEnd` + `Assume` constructors.
-- No new StmData arm; a closure IS `Seq (DeadEnd body) (Assume external_spec)`.
-- ══════════════════════════════════════════════════════════════════════

-- A closure (creation site), read off the Verus lowering: verify the body in
-- ISOLATION (a `DeadEnd`), then `Assume` the external contract the surrounding
-- world may rely on. `body` is an OPAQUE StmData (its internals — assume reqs;
-- body; assert enss — are ordinary W5a–c statements); `ext` is the opaque
-- external-spec hypothesis id.
def closureProg (body : lib.StmData) (ext : Int) : lib.StmData :=
  lib.StmData.Seq
    (Tactus.Box.mk (lib.StmData.DeadEnd (Tactus.Box.mk body)))
    (Tactus.Box.mk (lib.StmData.Assume ext))

-- ── W5e MAIN (closure_creation_sound). The reference WP for a closure creation
--    reduces EXACTLY to the body obligation under the ENCLOSING frame `f`:
--    the DeadEnd wrapper and the external-spec Assume add no obligation of their
--    own. Proven by instantiating the W5c iff + unfolding Seq/DeadEnd/Assume and
--    the emitted `frame_after (DeadEnd _) = f`.
theorem closure_creation_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (body : lib.StmData) (ext : Int) (st : St) :
    holdsAll hp he lv (lib.wp_stm f (closureProg body ext)) st
      ↔ execSafeF hp he lv f body st := by
  rw [wp_stm_sound hp he lv (closureProg body ext) f st]
  simp only [closureProg, u_exec_seq, u_exec_deadend, u_fa_deadend, u_exec_assume, and_true]

-- ── W5e ISOLATION (closure_deadend_isolates). The closure body's local
--    assumption does NOT leak to the continuation. `Seq (DeadEnd (Assume q))
--    (Assert P)` leaves the assert UNGATED by q — the DeadEnd quarantines the
--    body's hypothesis (`frame_after (DeadEnd _) = f`). Stated at `f = FNil`
--    (as W5d stated placement at the concrete `prophecyFrame`) for a clean form.
theorem closure_deadend_isolates (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (q h : Int) (obl : lib.RawExp) (st : St) :
    holdsAll hp he lv (lib.wp_stm lib.FrameList.FNil
        (lib.StmData.Seq
          (Tactus.Box.mk (lib.StmData.DeadEnd (Tactus.Box.mk (lib.StmData.Assume q))))
          (Tactus.Box.mk (lib.StmData.Assert obl h)))) st
      ↔ he (lib.render_exp obl) st := by
  rw [wp_stm_sound hp he lv _ lib.FrameList.FNil st]
  simp only [u_exec_seq, u_exec_deadend, u_exec_assume, true_and,
             u_fa_deadend, u_exec_assert, u_cs_FNil]

-- ── CONTRAST (seq_assume_gates). The BARE `Seq (Assume q) (Assert P)` (no
--    DeadEnd) GATES the assert by q — `frame_after (Assume q) = FHyp q`. The two
--    reduced forms DIFFER (ungated vs gated), which they could NOT if the DeadEnd
--    failed to quarantine the body's assumption. This is the W5e analog of W5d's
--    temporal-placement witness.
theorem seq_assume_gates (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (q h : Int) (obl : lib.RawExp) (st : St) :
    holdsAll hp he lv (lib.wp_stm lib.FrameList.FNil
        (lib.StmData.Seq
          (Tactus.Box.mk (lib.StmData.Assume q))
          (Tactus.Box.mk (lib.StmData.Assert obl h)))) st
      ↔ (hp q st → he (lib.render_exp obl) st) := by
  rw [wp_stm_sound hp he lv _ lib.FrameList.FNil st]
  simp only [u_exec_seq, u_exec_assume, true_and, u_fa_assume,
             u_fapp_fnil, u_exec_assert, u_cs_FHyp, u_cs_FNil]

-- ── W5e CONTRACT FORWARDING (closure_forwards_contract). After the closure, the
--    continuation DOES see the external_spec: `Seq (closure body ext) (Assert P)`
--    delivers the body obligation AND gates the continuation assert by `hp ext`
--    (`frame_after f (closure) = frame_after f (Assume ext) = FHyp ext`). The
--    Assume threads the contract forward — the analog of W5d's resolve pin.
theorem closure_forwards_contract (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (body : lib.StmData) (ext h : Int) (obl : lib.RawExp) (st : St) :
    holdsAll hp he lv (lib.wp_stm lib.FrameList.FNil
        (lib.StmData.Seq
          (Tactus.Box.mk (closureProg body ext))
          (Tactus.Box.mk (lib.StmData.Assert obl h)))) st
      ↔ (execSafeF hp he lv lib.FrameList.FNil body st
          ∧ (hp ext st → he (lib.render_exp obl) st)) := by
  rw [wp_stm_sound hp he lv _ lib.FrameList.FNil st]
  simp only [closureProg, u_exec_seq, u_exec_deadend, u_fa_deadend, u_exec_assume,
             and_true, u_fa_seq, u_fa_assume, u_fapp_fnil, u_exec_assert,
             u_cs_FHyp, u_cs_FNil]

-- ══ WITNESSES. ══

-- (1) ∀-PARAMS (refutes the "closure verified for one param value only" worry).
--     The closure body obligation is checked for EVERY valuation of a param id
--     `p` — the param is a fresh id covered by the outer ∀ st, NOT the
--     creation-time value. From the emitted goals holding at EVERY state, the
--     body obligation holds at the arbitrary param valuation `upd st p n`, ∀ n.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (p ext h : Int) (obl : lib.RawExp) (st : St) (n : Int)
    (hsafe : ∀ st', holdsAll hp he lv
              (lib.wp_stm lib.FrameList.FNil
                (closureProg (lib.StmData.Assert obl h) ext)) st') :
    he (lib.render_exp obl) (upd st p n) := by
  have hb := (closure_creation_sound hp he lv lib.FrameList.FNil
                (lib.StmData.Assert obl h) ext (upd st p n)).mp (hsafe (upd st p n))
  simpa only [u_exec_assert, u_cs_FNil] using hb

-- (2) NON-VACUITY of the body obligation (opaque `he` — it can only come from the
--     emitted body goal). If closure creation were modeled as `True`, this would
--     be underivable.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (f : lib.FrameList) (ext h : Int) (obl : lib.RawExp) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm f (closureProg (lib.StmData.Assert obl h) ext)) st) :
    closeSem hp he lv f st (fun st' => he (lib.render_exp obl) st') := by
  have hb := (closure_creation_sound hp he lv f (lib.StmData.Assert obl h) ext st).mp hg
  simpa only [u_exec_assert] using hb

-- (3) ISOLATION vs FORWARDING, side by side (the DeadEnd quarantines; the trailing
--     Assume forwards). The two reduced forms are genuinely distinct — ungated
--     obligation from the DeadEnd-wrapped body assumption, gated obligation from
--     the bare assume — proving the DeadEnd is not vacuous.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (q h : Int) (obl : lib.RawExp) (st : St) :
    (holdsAll hp he lv (lib.wp_stm lib.FrameList.FNil
        (lib.StmData.Seq
          (Tactus.Box.mk (lib.StmData.DeadEnd (Tactus.Box.mk (lib.StmData.Assume q))))
          (Tactus.Box.mk (lib.StmData.Assert obl h)))) st
       ↔ he (lib.render_exp obl) st)
    ∧ (holdsAll hp he lv (lib.wp_stm lib.FrameList.FNil
        (lib.StmData.Seq
          (Tactus.Box.mk (lib.StmData.Assume q))
          (Tactus.Box.mk (lib.StmData.Assert obl h)))) st
       ↔ (hp q st → he (lib.render_exp obl) st)) :=
  ⟨closure_deadend_isolates hp he lv q h obl st,
   seq_assume_gates hp he lv q h obl st⟩

end W5e

-- axiom closure (regression guard): the soundness theorems close over ONLY the
-- standard logical axioms — no `Classical.choice` (render_exp stays opaque),
-- no `sorryAx`, no smuggled axioms.
#print axioms W5e.wp_stm_sound            -- expect [propext, Quot.sound]
#print axioms W5e.ref_wp_sound            -- expect [propext, Quot.sound]
#print axioms W5e.closure_creation_sound  -- expect [propext, Quot.sound]
#print axioms W5e.closure_deadend_isolates -- expect [propext, Quot.sound]
#print axioms W5e.seq_assume_gates        -- expect [propext, Quot.sound]
#print axioms W5e.closure_forwards_contract -- expect [propext, Quot.sound]
