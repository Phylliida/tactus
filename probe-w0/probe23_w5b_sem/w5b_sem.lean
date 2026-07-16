import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5b PROBE (board bootstrap-50) — SOUNDNESS of the reference WP on the
-- fragment {Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd},
-- proven over the REAL emitted `lib.wp_stm`/`lib.frame_after`/`lib.close_e`/
-- `lib.close_each_e`/`lib.ret_frame`/`lib.goals_append`/`lib.frame_append`/
-- `lib.diverges`/`lib.is_skip` (tactus-core/out/lib), no tactus-core rebuild.
-- EXTENDS the landed W5a-1 probe (probe22) with the CALL and RET arms + the
-- now-LIVE `If` fall-through:
--
--   • `Call { reqs, post }` — `wp_stm` closes each requires obligation
--     (`close_each_e f reqs`); `frame_after` appends the post-call frame
--     `post` VERBATIM. `post` may BIND variables (the ∀-path
--     `FBind(dest) FHyp(ens)`), which W5a-1's single-Prop `addedHyp` could
--     not model. So the `Seq` continuation is generalised from
--     `addedHyp a st → body st` to `closeSem (frameDelta a) st body`, folding
--     the WHOLE frame delta a statement appends. This subsumes W5a-1
--     (an FHyp delta reproduces `addedHyp`) and covers `post` uniformly.
--   • `Ret(es, rb)` — `wp_stm` closes each ensures under `ret_frame f rb`
--     (the return-value binding). Operationally, on return the ret var is
--     bound (`RetLet`) and all ensures obligations must hold.
--   • `If` fall-through LIVE — `frameDelta (If) = if diverges t = 1 ∧
--     is_skip e = 1 then FHyp nc FNil else FNil`. `Ret`/`DeadEnd` now make
--     `diverges = 1` reachable in-fragment, so `if C { ret } rest` forwards
--     `¬C` into the continuation (W5a-1 collapsed this; now it BITES).
--
-- KEY DESIGN LIFT over W5a-1: the frame-threading Lemma B is now a corollary
-- of `frame_after f a = frame_append f (frameDelta a)` (`frame_after_eq_append`,
-- needing a new `frame_append_assoc`) + probe22's `closeSem_append`. This
-- RETIRES probe22's recursive `closeSem_frame_after` + `addedHyp` +
-- `diverges_zero_of_inFragment`.
--
-- Valuation-parametric (open Q §5.5 = option b): THREE opaque leaf oracles,
-- the theorem quantifies over all of them.
--   hp : Int → St → Prop        opaque prop leaves (hyps + Leaf obligations)
--   he : ExprData → St → Prop    deep obligation exprs (render_exp stays OPAQUE)
--   lv : Int → St → Int          let-value leaves (FLet / GoalData.Let / RetLet)
--
-- THEOREM (wp_stm_sound):
--   inFragment s → holdsAll (wp_stm f s) st → closeSem f st (execSafe s ·)
-- Design + model: DESIGN-W5-soundness.md §1–3 (§4 W5b row).
--
-- IDIOM NOTE (unchanged from probe21/22): the emitted structural defs reduce
-- DEFINITIONALLY on constructors but `simp [lib.close_e]` cannot generate their
-- equational theorems ("invalid projection"). So we unfold via explicit `rfl`
-- lemmas (`u_*`) + `simp only`, never `simp [defName]`. Prelude is Mathlib-free.
-- ══════════════════════════════════════════════════════════════════════

namespace W5b

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
--    semantic content of a `close_each_e` list — Call reqs / Ret enss) ──
def obligsSafe (he : lib.ExprData → St → Prop) (l : lib.RawExpList) (st : St) : Prop :=
  match l with
  | lib.RawExpList.Nil => True
  | lib.RawExpList.Cons h t => he (lib.render_exp h.deref) st ∧ obligsSafe he t.deref st
termination_by structural l

-- ── the frame delta a statement appends (mirrors `frame_after`'s per-stmt
--    append; `frame_after f s = frame_append f (frameDelta s)` in-fragment).
--    `noncomputable` only because `lib.diverges` (used in the If arm) is. ──
noncomputable def frameDelta (s : lib.StmData) : lib.FrameList :=
  match s with
  | lib.StmData.Skip => lib.FrameList.FNil
  | lib.StmData.Assume e => lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)
  | lib.StmData.Assert _ h => lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)
  | lib.StmData.Assign x rhs => lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)
  | lib.StmData.Call _ post => post.deref
  | lib.StmData.DeadEnd _ => lib.FrameList.FNil
  | lib.StmData.Ret _ _ => lib.FrameList.FNil
  | lib.StmData.If _ nc t e =>
      if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1
        then lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil)
        else lib.FrameList.FNil
  | lib.StmData.Seq a b => lib.frame_append (frameDelta a.deref) (frameDelta b.deref)
  | _ => lib.FrameList.FNil
termination_by structural s

-- ── the fragment ──
def inFragment (s : lib.StmData) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assert _ _ => True
  | lib.StmData.Assign _ _ => True
  | lib.StmData.Call _ _ => True
  | lib.StmData.Ret _ _ => True
  | lib.StmData.DeadEnd b => inFragment b.deref
  | lib.StmData.Seq a b => inFragment a.deref ∧ inFragment b.deref
  | lib.StmData.If _ _ t e => inFragment t.deref ∧ inFragment e.deref
  | _ => False
termination_by structural s

-- ── §2.2 operational safety ──
--  execSafe: an Assert faults iff its obligation is false; a Call is safe iff
--  its requires obligations hold at the call; a Ret is safe iff its ensures
--  obligations hold in the return-bound state; a DeadEnd is safe iff its body
--  is; an If requires each branch safe under its guard leaf; a Seq threads the
--  head's frame delta (`closeSem (frameDelta a)`) over the tail's safety.
def execSafe (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assign _ _ => True
  | lib.StmData.Assert o _ => he (lib.render_exp o) st
  | lib.StmData.Call reqs _ => obligsSafe he reqs.deref st
  | lib.StmData.Ret es rb =>
      (match rb with
       | lib.RetBind.RetNone => obligsSafe he es.deref st
       | lib.RetBind.RetLet name val => obligsSafe he es.deref (upd st name (lv val st)))
  | lib.StmData.DeadEnd b => execSafe hp he lv b.deref st
  | lib.StmData.If c nc t e =>
      (hp c st → execSafe hp he lv t.deref st) ∧ (hp nc st → execSafe hp he lv e.deref st)
  | lib.StmData.Seq a b =>
      execSafe hp he lv a.deref st
        ∧ closeSem hp he lv (frameDelta a.deref) st (fun st' => execSafe hp he lv b.deref st')
  | _ => True
termination_by structural s

-- ══ definitional-unfold (rfl) lemmas — used with `simp only`. ══
section Unfold
variable (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int) (st : St)

-- box derefs (generic)
@[simp] theorem u_box_gd (x : lib.GoalData) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_fl (x : lib.FrameList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_gl (x : lib.GoalList) : (Tactus.Box.mk x).deref = x := rfl

-- emitted reference: close_e / frame_append / close_each_e
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
@[simp] theorem u_fapp_FNil (g) : lib.frame_append lib.FrameList.FNil g = g := rfl
@[simp] theorem u_fapp_FBind (x ty t g) :
    lib.frame_append (lib.FrameList.FBind x ty t) g
      = lib.FrameList.FBind x ty (Tactus.Box.mk (lib.frame_append t.deref g)) := rfl
@[simp] theorem u_fapp_FHyp (h t g) :
    lib.frame_append (lib.FrameList.FHyp h t) g
      = lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) := rfl
@[simp] theorem u_fapp_FLet (x v t g) :
    lib.frame_append (lib.FrameList.FLet x v t) g
      = lib.FrameList.FLet x v (Tactus.Box.mk (lib.frame_append t.deref g)) := rfl
@[simp] theorem u_cce_nil (f) : lib.close_each_e f lib.RawExpList.Nil = lib.GoalList.Nil := rfl
@[simp] theorem u_cce_cons (f h t) :
    lib.close_each_e f (lib.RawExpList.Cons h t)
      = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f h.deref))
          (Tactus.Box.mk (lib.close_each_e f t.deref)) := rfl

-- emitted reference: wp_stm arms
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

-- emitted reference: ret_frame
@[simp] theorem u_rf_none (f) : lib.ret_frame f lib.RetBind.RetNone = f := rfl
@[simp] theorem u_rf_let (f name val) :
    lib.ret_frame f (lib.RetBind.RetLet name val)
      = lib.frame_append f (lib.FrameList.FLet name val (Tactus.Box.mk lib.FrameList.FNil)) := rfl

-- emitted reference: frame_after arms
@[simp] theorem u_fafter_skip (f) : lib.frame_after f lib.StmData.Skip = f := rfl
@[simp] theorem u_fafter_assume (f e) :
    lib.frame_after f (lib.StmData.Assume e)
      = lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) := rfl
@[simp] theorem u_fafter_assert (f o h) :
    lib.frame_after f (lib.StmData.Assert o h)
      = lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) := rfl
@[simp] theorem u_fafter_assign (f x rhs) :
    lib.frame_after f (lib.StmData.Assign x rhs)
      = lib.frame_append f (lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil)) := rfl
@[simp] theorem u_fafter_call (f reqs post) :
    lib.frame_after f (lib.StmData.Call reqs post) = lib.frame_append f post.deref := rfl
@[simp] theorem u_fafter_deadend (f b) : lib.frame_after f (lib.StmData.DeadEnd b) = f := rfl
@[simp] theorem u_fafter_ret (f es rb) : lib.frame_after f (lib.StmData.Ret es rb) = f := rfl
@[simp] theorem u_fafter_seq (f a b) :
    lib.frame_after f (lib.StmData.Seq a b)
      = lib.frame_after (lib.frame_after f a.deref) b.deref := rfl
theorem u_fafter_if (f c nc t e) :
    lib.frame_after f (lib.StmData.If c nc t e)
      = (if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1
           then lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))
           else f) := rfl

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
@[simp] theorem u_fd_skip : frameDelta lib.StmData.Skip = lib.FrameList.FNil := rfl
@[simp] theorem u_fd_assume (e) :
    frameDelta (lib.StmData.Assume e) = lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil) := rfl
@[simp] theorem u_fd_assert (o h) :
    frameDelta (lib.StmData.Assert o h) = lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil) := rfl
@[simp] theorem u_fd_assign (x rhs) :
    frameDelta (lib.StmData.Assign x rhs) = lib.FrameList.FLet x rhs (Tactus.Box.mk lib.FrameList.FNil) := rfl
@[simp] theorem u_fd_call (reqs post) :
    frameDelta (lib.StmData.Call reqs post) = post.deref := rfl
@[simp] theorem u_fd_deadend (b) : frameDelta (lib.StmData.DeadEnd b) = lib.FrameList.FNil := rfl
@[simp] theorem u_fd_ret (es rb) : frameDelta (lib.StmData.Ret es rb) = lib.FrameList.FNil := rfl
theorem u_fd_if (c nc t e) :
    frameDelta (lib.StmData.If c nc t e)
      = (if lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1
           then lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil)
           else lib.FrameList.FNil) := rfl
@[simp] theorem u_fd_seq (a b) :
    frameDelta (lib.StmData.Seq a b)
      = lib.frame_append (frameDelta a.deref) (frameDelta b.deref) := rfl
@[simp] theorem u_inf_deadend (b) : inFragment (lib.StmData.DeadEnd b) = inFragment b.deref := rfl
@[simp] theorem u_inf_seq (a b) :
    inFragment (lib.StmData.Seq a b) = (inFragment a.deref ∧ inFragment b.deref) := rfl
@[simp] theorem u_inf_if (c nc t e) :
    inFragment (lib.StmData.If c nc t e) = (inFragment t.deref ∧ inFragment e.deref) := rfl
@[simp] theorem u_exec_skip : execSafe hp he lv lib.StmData.Skip st = True := rfl
@[simp] theorem u_exec_assume (e) : execSafe hp he lv (lib.StmData.Assume e) st = True := rfl
@[simp] theorem u_exec_assign (x rhs) : execSafe hp he lv (lib.StmData.Assign x rhs) st = True := rfl
@[simp] theorem u_exec_assert (o h) :
    execSafe hp he lv (lib.StmData.Assert o h) st = he (lib.render_exp o) st := rfl
@[simp] theorem u_exec_call (reqs post) :
    execSafe hp he lv (lib.StmData.Call reqs post) st = obligsSafe he reqs.deref st := rfl
@[simp] theorem u_exec_ret_none (es) :
    execSafe hp he lv (lib.StmData.Ret es lib.RetBind.RetNone) st = obligsSafe he es.deref st := rfl
@[simp] theorem u_exec_ret_let (es name val) :
    execSafe hp he lv (lib.StmData.Ret es (lib.RetBind.RetLet name val)) st
      = obligsSafe he es.deref (upd st name (lv val st)) := rfl
@[simp] theorem u_exec_deadend (b) :
    execSafe hp he lv (lib.StmData.DeadEnd b) st = execSafe hp he lv b.deref st := rfl
@[simp] theorem u_exec_if (c nc t e) :
    execSafe hp he lv (lib.StmData.If c nc t e) st
      = ((hp c st → execSafe hp he lv t.deref st) ∧ (hp nc st → execSafe hp he lv e.deref st)) := rfl
@[simp] theorem u_exec_seq (a b) :
    execSafe hp he lv (lib.StmData.Seq a b) st
      = (execSafe hp he lv a.deref st
          ∧ closeSem hp he lv (frameDelta a.deref) st (fun st' => execSafe hp he lv b.deref st')) := rfl
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

-- ── Lemma C (frame_append composes closeSem) ──
theorem closeSem_append (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f g : lib.FrameList) (st : St) (body : St → Prop) :
    closeSem hp he lv (lib.frame_append f g) st body
      ↔ closeSem hp he lv f st (fun st' => closeSem hp he lv g st' body) := by
  match f with
  | lib.FrameList.FNil => simp only [u_fapp_FNil, u_cs_FNil]
  | lib.FrameList.FBind x ty t =>
      simp only [u_fapp_FBind, u_cs_FBind]
      constructor
      · intro hh n; exact (closeSem_append hp he lv t.deref g (upd st x n) body).mp (hh n)
      · intro hh n; exact (closeSem_append hp he lv t.deref g (upd st x n) body).mpr (hh n)
  | lib.FrameList.FHyp h t =>
      simp only [u_fapp_FHyp, u_cs_FHyp]
      constructor
      · intro k a; exact (closeSem_append hp he lv t.deref g st body).mp (k a)
      · intro k a; exact (closeSem_append hp he lv t.deref g st body).mpr (k a)
  | lib.FrameList.FLet x v t =>
      simp only [u_fapp_FLet, u_cs_FLet]
      exact closeSem_append hp he lv t.deref g (upd st x (lv v st)) body
termination_by f
decreasing_by all_goals (simp_all; omega)

-- ── frame_append is associative (needed for frameDelta's Seq arm) ──
theorem frame_append_assoc (f g h : lib.FrameList) :
    lib.frame_append (lib.frame_append f g) h = lib.frame_append f (lib.frame_append g h) := by
  match f with
  | lib.FrameList.FNil => simp only [u_fapp_FNil]
  | lib.FrameList.FBind x ty t =>
      simp only [u_fapp_FBind]; rw [frame_append_assoc t.deref g h]
  | lib.FrameList.FHyp hh t =>
      simp only [u_fapp_FHyp]; rw [frame_append_assoc t.deref g h]
  | lib.FrameList.FLet x v t =>
      simp only [u_fapp_FLet]; rw [frame_append_assoc t.deref g h]
termination_by f
decreasing_by all_goals (simp_all; omega)

-- ── frame_append right identity (FNil on the RIGHT; NOT definitional —
--    frame_append recurses on the FIRST arg). ──
theorem frame_append_fnil_right (f : lib.FrameList) :
    lib.frame_append f lib.FrameList.FNil = f := by
  match f with
  | lib.FrameList.FNil => simp only [u_fapp_FNil]
  | lib.FrameList.FBind x ty t =>
      simp only [u_fapp_FBind]; rw [frame_append_fnil_right t.deref]
  | lib.FrameList.FHyp hh t =>
      simp only [u_fapp_FHyp]; rw [frame_append_fnil_right t.deref]
  | lib.FrameList.FLet x v t =>
      simp only [u_fapp_FLet]; rw [frame_append_fnil_right t.deref]
termination_by f
decreasing_by all_goals (simp_all; omega)

-- ── frame_after IS a frame_append of the statement's frame delta (in-fragment).
--    This is the design lift: it makes Lemma B a corollary of Lemma C. ──
theorem frame_after_eq_append (f : lib.FrameList) (s : lib.StmData) (hs : inFragment s) :
    lib.frame_after f s = lib.frame_append f (frameDelta s) := by
  match s with
  | lib.StmData.Skip => simp only [u_fafter_skip, u_fd_skip, frame_append_fnil_right]
  | lib.StmData.Assume e => simp only [u_fafter_assume, u_fd_assume]
  | lib.StmData.Assert o h => simp only [u_fafter_assert, u_fd_assert]
  | lib.StmData.Assign x rhs => simp only [u_fafter_assign, u_fd_assign]
  | lib.StmData.Call reqs post => simp only [u_fafter_call, u_fd_call]
  | lib.StmData.DeadEnd b => simp only [u_fafter_deadend, u_fd_deadend, frame_append_fnil_right]
  | lib.StmData.Ret es rb => simp only [u_fafter_ret, u_fd_ret, frame_append_fnil_right]
  | lib.StmData.If c nc t e =>
      rw [u_fafter_if, u_fd_if]
      by_cases hP : (lib.diverges t.deref = 1 ∧ lib.is_skip e.deref = 1)
      · rw [if_pos hP, if_pos hP]
      · rw [if_neg hP, if_neg hP, frame_append_fnil_right]
  | lib.StmData.Seq a b =>
      have ha : inFragment a.deref ∧ inFragment b.deref := by simpa using hs
      rw [u_fafter_seq]
      rw [frame_after_eq_append (lib.frame_after f a.deref) b.deref ha.2]
      rw [frame_after_eq_append f a.deref ha.1]
      rw [u_fd_seq, frame_append_assoc]
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact hs.elim
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── Lemma B (generalised): frame_after threads exactly the frame delta.
--    Now a one-liner from frame_after_eq_append + closeSem_append. ──
theorem closeSem_frame_after (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (a : lib.StmData) (st : St) (body : St → Prop)
    (ha : inFragment a) :
    closeSem hp he lv (lib.frame_after f a) st body
      ↔ closeSem hp he lv f st (fun st' => closeSem hp he lv (frameDelta a) st' body) := by
  rw [frame_after_eq_append f a ha]
  exact closeSem_append hp he lv f (frameDelta a) st body

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
--    holds under the telescope (the Call reqs / Ret enss soundness core) ──
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

-- ── Ret bridge: closing under `ret_frame f rb` = closing under `f` with the
--    return binding applied to the state (RetLet binds ret := lv val). ──
def retApply (lv : Int → St → Int) (rb : lib.RetBind) (st : St) : St :=
  match rb with
  | lib.RetBind.RetNone => st
  | lib.RetBind.RetLet name val => upd st name (lv val st)

theorem closeSem_ret_frame (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (rb : lib.RetBind) (st : St) (body : St → Prop) :
    closeSem hp he lv (lib.ret_frame f rb) st body
      ↔ closeSem hp he lv f st (fun st' => body (retApply lv rb st')) := by
  match rb with
  | lib.RetBind.RetNone =>
      simp only [u_rf_none, retApply]
  | lib.RetBind.RetLet name val =>
      simp only [u_rf_let]
      rw [closeSem_append hp he lv f _ st body]
      exact closeSem_congr hp he lv f st _ _ (fun st' => by
        simp only [u_cs_FLet, u_cs_FNil, retApply])

-- ══ MAIN: reference-WP soundness on {Skip,Assume,Assert,Assign,Seq,If,Call,
--    Ret,DeadEnd} over an ARBITRARY frame telescope. ══
theorem wp_stm_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (s : lib.StmData) (f : lib.FrameList) (st : St)
    (hs : inFragment s) (hg : holdsAll hp he lv (lib.wp_stm f s) st) :
    closeSem hp he lv f st (fun st' => execSafe hp he lv s st') := by
  match s with
  | lib.StmData.Skip =>
      have : (fun st' => execSafe hp he lv lib.StmData.Skip st') = (fun _ : St => True) := by
        funext st'; simp
      rw [this]; exact closeSem_triv hp he lv f st
  | lib.StmData.Assume e =>
      have : (fun st' => execSafe hp he lv (lib.StmData.Assume e) st') = (fun _ : St => True) := by
        funext st'; simp
      rw [this]; exact closeSem_triv hp he lv f st
  | lib.StmData.Assign x rhs =>
      have : (fun st' => execSafe hp he lv (lib.StmData.Assign x rhs) st') = (fun _ : St => True) := by
        funext st'; simp
      rw [this]; exact closeSem_triv hp he lv f st
  | lib.StmData.Assert o h =>
      simp only [u_wp_assert, u_holdsAll_cons, u_holdsAll_nil, and_true] at hg
      rw [holds_close_e hp he lv f o st] at hg
      exact (closeSem_congr hp he lv f st _ _ (fun st' => by simp)).mpr hg
  | lib.StmData.Call reqs post =>
      simp only [u_wp_call] at hg
      rw [holdsAll_close_each_e hp he lv f reqs.deref st] at hg
      exact (closeSem_congr hp he lv f st _ _ (fun st' => by simp)).mpr hg
  | lib.StmData.Ret es rb =>
      simp only [u_wp_ret] at hg
      rw [holdsAll_close_each_e hp he lv (lib.ret_frame f rb) es.deref st] at hg
      rw [closeSem_ret_frame hp he lv f rb st _] at hg
      refine (closeSem_congr hp he lv f st _ _ (fun st' => ?_)).mp hg
      cases rb with
      | RetNone => simp only [retApply, u_exec_ret_none]
      | RetLet name val => simp only [retApply, u_exec_ret_let]
  | lib.StmData.DeadEnd b =>
      have hb : inFragment b.deref := by simpa using hs
      simp only [u_wp_deadend] at hg
      have ih := wp_stm_sound hp he lv b.deref f st hb hg
      refine (closeSem_congr hp he lv f st _ _ (fun st' => ?_)).mp ih
      simp only [u_exec_deadend]
  | lib.StmData.Seq a b =>
      have hs' : inFragment a.deref ∧ inFragment b.deref := by simpa using hs
      simp only [u_wp_seq] at hg
      rw [holdsAll_append hp he lv _ _ st] at hg
      have iha := wp_stm_sound hp he lv a.deref f st hs'.1 hg.1
      have ihb := wp_stm_sound hp he lv b.deref (lib.frame_after f a.deref) st hs'.2 hg.2
      rw [closeSem_frame_after hp he lv f a.deref st _ hs'.1] at ihb
      have hcomb := closeSem_and hp he lv f st _ _ iha ihb
      refine (closeSem_congr hp he lv f st _ _ (fun st' => ?_)).mp hcomb
      simp only [u_exec_seq]
  | lib.StmData.If c nc t e =>
      have hs' : inFragment t.deref ∧ inFragment e.deref := by simpa using hs
      simp only [u_wp_if] at hg
      rw [holdsAll_append hp he lv _ _ st] at hg
      have iht := wp_stm_sound hp he lv t.deref
        (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) st hs'.1 hg.1
      have ihe := wp_stm_sound hp he lv e.deref
        (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) st hs'.2 hg.2
      rw [closeSem_append hp he lv f _ st _] at iht
      rw [closeSem_append hp he lv f _ st _] at ihe
      have iht' : closeSem hp he lv f st (fun st' => hp c st' → execSafe hp he lv t.deref st') :=
        (closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])).mp iht
      have ihe' : closeSem hp he lv f st (fun st' => hp nc st' → execSafe hp he lv e.deref st') :=
        (closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])).mp ihe
      have hcomb := closeSem_and hp he lv f st _ _ iht' ihe'
      refine (closeSem_congr hp he lv f st _ _ (fun st' => ?_)).mp hcomb
      simp only [u_exec_if]
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact hs.elim
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── top-level: ref_wp soundness for a fn whose body is in the fragment. ──
theorem ref_wp_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (c : lib.FnCtxData) (s : lib.StmData) (st : St)
    (hs : inFragment s) (hg : holdsAll hp he lv (lib.ref_wp c s) st) :
    closeSem hp he lv (lib.seed_frame c) st (fun st' => execSafe hp he lv s st') := by
  have hrw : lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s := rfl
  rw [hrw] at hg
  exact wp_stm_sound hp he lv s (lib.seed_frame c) st hs hg

-- ══ NON-VACUITY witnesses. ══

-- (1) Call: the requires obligation must hold at the call site (opaque `he`,
--     so it can only come from the emitted `close_each_e` goal).
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (o : lib.RawExp) (post : lib.FrameList) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Call
                 (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk o) (Tactus.Box.mk lib.RawExpList.Nil)))
                 (Tactus.Box.mk post))) st) :
    he (lib.render_exp o) st := by
  have hsound := wp_stm_sound hp he lv _ lib.FrameList.FNil st (by exact trivial) hg
  simp only [u_cs_FNil, u_exec_call, u_obl_cons, u_obl_nil, and_true] at hsound
  exact hsound

-- (2) Ret with a return binding: the ensures obligation must hold in the
--     RETURN-BOUND state `upd st name (lv val st)` (the RetLet semantics).
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (o : lib.RawExp) (name val : Int) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Ret
                 (Tactus.Box.mk (lib.RawExpList.Cons (Tactus.Box.mk o) (Tactus.Box.mk lib.RawExpList.Nil)))
                 (lib.RetBind.RetLet name val))) st) :
    he (lib.render_exp o) (upd st name (lv val st)) := by
  have hsound := wp_stm_sound hp he lv _ lib.FrameList.FNil st (by exact trivial) hg
  simp only [u_cs_FNil, u_exec_ret_let, u_obl_cons, u_obl_nil, and_true] at hsound
  exact hsound

-- (3) If fall-through LIVE: `if c { ret o } (else Skip)` forwards `¬c` into
--     the continuation. Here we witness that the diverging-then + Skip-else
--     If's frame delta is exactly `FHyp nc FNil` (the `¬cond` forwarding),
--     which W5a-1 could only collapse to FNil.
example (c nc : Int) (o : lib.RawExp) :
    frameDelta (lib.StmData.If c nc
                 (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone))
                 (Tactus.Box.mk lib.StmData.Skip))
      = lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil) := by
  rw [u_fd_if, if_pos (show
    lib.diverges (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone)).deref = 1
      ∧ lib.is_skip (Tactus.Box.mk lib.StmData.Skip).deref = 1 from ⟨rfl, rfl⟩)]

-- (4) Seq after a diverging-then If: the continuation `b` is required safe
--     only UNDER `hp nc` (the forwarded ¬cond), witnessing the live
--     fall-through inside execSafe's Seq threading.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (c nc : Int) (o : lib.RawExp) (h : Int) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Seq
                 (Tactus.Box.mk (lib.StmData.If c nc
                    (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone))
                    (Tactus.Box.mk lib.StmData.Skip)))
                 (Tactus.Box.mk (lib.StmData.Assert o h)))) st) :
    hp nc st → he (lib.render_exp o) st := by
  have hsound := wp_stm_sound hp he lv _ lib.FrameList.FNil st
    (by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> exact trivial) hg
  simp only [u_cs_FNil, u_exec_seq] at hsound
  -- the If diverges (then=Ret) & else is Skip, so frameDelta = FHyp nc FNil
  rw [u_fd_if, if_pos (show
    lib.diverges (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.RawExpList.Nil) lib.RetBind.RetNone)).deref = 1
      ∧ lib.is_skip (Tactus.Box.mk lib.StmData.Skip).deref = 1 from ⟨rfl, rfl⟩)] at hsound
  simp only [u_cs_FHyp, u_cs_FNil, u_exec_assert] at hsound
  exact hsound.2

end W5b

-- axiom closure (regression guard): the soundness theorems close over ONLY the
-- standard logical axioms — no `Classical.choice` (render_exp stays opaque),
-- no `sorryAx`, no smuggled axioms.
#print axioms W5b.wp_stm_sound   -- expect [propext, Quot.sound]
#print axioms W5b.ref_wp_sound   -- expect [propext, Quot.sound]
