import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5a-1 PROBE (board bootstrap-49) — SOUNDNESS of the reference WP on the
-- straight-line + BRANCHING fragment {Skip, Assume, Assert, Seq, If},
-- proven over the REAL emitted `lib.wp_stm`/`lib.frame_after`/`lib.close_e`/
-- `lib.goals_append`/`lib.diverges`/`lib.is_skip` (tactus-core/out/lib), the
-- analog of probe14 for the bridge — no tactus-core rebuild. This EXTENDS the
-- landed W5a-0 probe (probe21) with:
--   • `If` (flat two-way, matching `wp_stm`'s If arm),
--   • the seed frame's `FBind`/∀ params + `FLet` lets — via a GENERAL frame
--     telescope interpretation `closeSem`, which LIFTS the theorem past
--     W5a-0's `isHypFrame` restriction entirely,
--   • the real `∀`/`upd` (All) and `let` (Let) denotation for `holds`,
--   • `ref_wp_sound` at the top level over the genuine `lib.seed_frame`
--     (all-`FBind` telescope: typ_params ++ params/bounds ++ reqs).
-- Design + model: DESIGN-W5-soundness.md §1–3 (§3 generalised: `frameHyps
-- f st → execSafe s st` becomes `closeSem f st (execSafe s ·)`, which folds
-- FBind→∀, FHyp→→, FLet→let — the W5a-0 hyp-frame statement is the special
-- case where the telescope is all FHyp).
--
-- Valuation-parametric (open Q §5.5 = option b): THREE opaque leaf oracles,
-- the theorem quantifies over all of them.
--   hp : Int → St → Prop        opaque prop leaves (hyps + Leaf obligations)
--   he : ExprData → St → Prop    deep obligation exprs (render_exp stays OPAQUE)
--   lv : Int → St → Int          let-value leaves (FLet / GoalData.Let)
--
-- THEOREM (wp_stm_sound):
--   inFragment s → holdsAll (wp_stm f s) st → closeSem f st (execSafe s ·)
-- i.e. if the emitted goals all hold, then under the frame's ∀/→/let
-- telescope every assert's obligation holds — WP soundness for the fragment,
-- leaf interpretation entirely opaque, NO frame-shape restriction.
--
-- IDIOM NOTE (unchanged from probe21): the emitted structural defs reduce
-- DEFINITIONALLY on constructors but `simp [lib.close_e]` cannot generate their
-- equational theorems ("invalid projection"). So we unfold via explicit `rfl`
-- lemmas (`u_*`) + `simp only`, never `simp [defName]`. Prelude is Mathlib-free
-- (no `tauto`): propositional shuffles use `simp only [and_assoc]`/`[and_imp]`.
-- ══════════════════════════════════════════════════════════════════════

namespace W5a1

abbrev St := Int → Int

def upd (st : St) (x n : Int) : St := fun k => if k = x then n else st k

-- ── §2.1 goal denotation (Val-level toProp). NOW FAITHFUL on every arm:
--    All → ∀ (upd), Let → let-value (upd ∘ lv). Reached under FBind/FLet. ──
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

-- ── the GENERAL frame telescope interpretation (§3, generalised). Folds a
--    frame around a state-indexed body `St → Prop`: FBind → ∀, FHyp → →,
--    FLet → let. `closeSem f st (execSafe s ·)` is the honest "under the
--    frame's binders/hyps/lets, `s` is safe" — subsumes W5a-0's
--    `frameHyps f st → execSafe s st` (all-FHyp special case). ──
def closeSem (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (f : lib.FrameList) (st : St) (body : St → Prop) : Prop :=
  match f with
  | lib.FrameList.FNil => body st
  | lib.FrameList.FBind x _ t => ∀ n : Int, closeSem hp he lv t.deref (upd st x n) body
  | lib.FrameList.FHyp h t => hp h st → closeSem hp he lv t.deref st body
  | lib.FrameList.FLet x v t => closeSem hp he lv t.deref (upd st x (lv v st)) body
termination_by structural f

-- ── the fragment: now includes If (both branches in-fragment) ──
def inFragment (s : lib.StmData) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assert _ _ => True
  | lib.StmData.Seq a b => inFragment a.deref ∧ inFragment b.deref
  | lib.StmData.If _ _ t e => inFragment t.deref ∧ inFragment e.deref
  | _ => False
termination_by structural s

-- ── §2.2 operational safety ──
--  addedHyp: the fact `frame_after` threads downstream. For an in-fragment If
--  it is `True`: the fall-through `¬cond`-forwarding of `frame_after`'s If arm
--  fires ONLY when the then-branch DIVERGES (Ret/DeadEnd) and the else is Skip
--  — divergence primitives are OUT of this fragment (`diverges_zero_of_inFragment`),
--  so in-fragment `frame_after f (If) = f`, i.e. no downstream fact. The general
--  fall-through `¬cond` is W5b (Ret/DeadEnd). This is the faithful in-fragment
--  reading, not a simplification: an in-fragment If genuinely merges nothing.
def addedHyp (hp : Int → St → Prop) (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Assume e => hp e st
  | lib.StmData.Assert _ h => hp h st
  | lib.StmData.Skip => True
  | lib.StmData.Seq a b => addedHyp hp a.deref st ∧ addedHyp hp b.deref st
  | lib.StmData.If _ _ _ _ => True
  | _ => True
termination_by structural s

--  execSafe: an Assert faults iff its obligation is false; Seq threads the
--  downstream hyp; an If is safe iff EACH branch is safe under its guard leaf
--  (`c` for then, `nc` for else) — the honest two-way reading (we do not know
--  which branch runs, so both are required under their respective conditions).
def execSafe (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assert o _ => he (lib.render_exp o) st
  | lib.StmData.Seq a b =>
      execSafe hp he a.deref st ∧ (addedHyp hp a.deref st → execSafe hp he b.deref st)
  | lib.StmData.If c nc t e =>
      (hp c st → execSafe hp he t.deref st) ∧ (hp nc st → execSafe hp he e.deref st)
  | _ => True
termination_by structural s

-- ══ definitional-unfold (rfl) lemmas — used with `simp only`. ══
section Unfold
variable (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int) (st : St)

-- emitted reference defs
@[simp] theorem u_box (x : lib.GoalData) : (Tactus.Box.mk x).deref = x := rfl
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
@[simp] theorem u_wp_assert (f o h) :
    lib.wp_stm f (lib.StmData.Assert o h)
      = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) := rfl
@[simp] theorem u_wp_seq (f a b) :
    lib.wp_stm f (lib.StmData.Seq a b)
      = lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref) := rfl
@[simp] theorem u_wp_if (f c nc t e) :
    lib.wp_stm f (lib.StmData.If c nc t e)
      = lib.goals_append
          (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp c (Tactus.Box.mk lib.FrameList.FNil))) t.deref)
          (lib.wp_stm (lib.frame_append f (lib.FrameList.FHyp nc (Tactus.Box.mk lib.FrameList.FNil))) e.deref) := rfl
@[simp] theorem u_fafter_skip (f) : lib.frame_after f lib.StmData.Skip = f := rfl
@[simp] theorem u_fafter_assume (f e) :
    lib.frame_after f (lib.StmData.Assume e)
      = lib.frame_append f (lib.FrameList.FHyp e (Tactus.Box.mk lib.FrameList.FNil)) := rfl
@[simp] theorem u_fafter_assert (f o h) :
    lib.frame_after f (lib.StmData.Assert o h)
      = lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil)) := rfl
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
-- diverges / is_skip (for the fall-through exclusion on the fragment)
@[simp] theorem u_div_skip : lib.diverges lib.StmData.Skip = 0 := rfl
@[simp] theorem u_div_assume (e) : lib.diverges (lib.StmData.Assume e) = 0 := rfl
@[simp] theorem u_div_assert (o h) : lib.diverges (lib.StmData.Assert o h) = 0 := rfl
@[simp] theorem u_div_seq (a b) :
    lib.diverges (lib.StmData.Seq a b)
      = (if lib.diverges a.deref = 1 ∨ lib.diverges b.deref = 1 then 1 else 0) := rfl
@[simp] theorem u_div_if (c nc t e) :
    lib.diverges (lib.StmData.If c nc t e)
      = (if lib.diverges t.deref = 1 ∧ lib.diverges e.deref = 1 then 1 else 0) := rfl

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
@[simp] theorem u_inf_seq (a b) :
    inFragment (lib.StmData.Seq a b) = (inFragment a.deref ∧ inFragment b.deref) := rfl
@[simp] theorem u_inf_if (c nc t e) :
    inFragment (lib.StmData.If c nc t e) = (inFragment t.deref ∧ inFragment e.deref) := rfl
@[simp] theorem u_added_skip : addedHyp hp lib.StmData.Skip st = True := rfl
@[simp] theorem u_added_assume (e) : addedHyp hp (lib.StmData.Assume e) st = hp e st := rfl
@[simp] theorem u_added_assert (o h) : addedHyp hp (lib.StmData.Assert o h) st = hp h st := rfl
@[simp] theorem u_added_seq (a b) :
    addedHyp hp (lib.StmData.Seq a b) st
      = (addedHyp hp a.deref st ∧ addedHyp hp b.deref st) := rfl
@[simp] theorem u_added_if (c nc t e) :
    addedHyp hp (lib.StmData.If c nc t e) st = True := rfl
@[simp] theorem u_exec_skip : execSafe hp he lib.StmData.Skip st = True := rfl
@[simp] theorem u_exec_assume (e) : execSafe hp he (lib.StmData.Assume e) st = True := rfl
@[simp] theorem u_exec_assert (o h) :
    execSafe hp he (lib.StmData.Assert o h) st = he (lib.render_exp o) st := rfl
@[simp] theorem u_exec_seq (a b) :
    execSafe hp he (lib.StmData.Seq a b) st
      = (execSafe hp he a.deref st ∧ (addedHyp hp a.deref st → execSafe hp he b.deref st)) := rfl
@[simp] theorem u_exec_if (c nc t e) :
    execSafe hp he (lib.StmData.If c nc t e) st
      = ((hp c st → execSafe hp he t.deref st) ∧ (hp nc st → execSafe hp he e.deref st)) := rfl
end Unfold

-- ══ closeSem structural lemmas (congruence / triviality / conjunction) ══

-- pointwise-iff bodies give equal closeSem (needed to shuffle `True → ·`)
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

-- a body that is unconditionally True closes any telescope
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

-- closeSem distributes over ∧ (FBind ∀, FHyp →, FLet subst all preserve it)
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

-- an in-fragment statement never diverges (no Ret/DeadEnd) — kills the
-- `frame_after` If fall-through, so an in-fragment If forwards nothing.
theorem diverges_zero_of_inFragment (s : lib.StmData) (hs : inFragment s) :
    lib.diverges s = 0 := by
  match s with
  | lib.StmData.Skip => simp
  | lib.StmData.Assume e => simp
  | lib.StmData.Assert o h => simp
  | lib.StmData.Seq a b =>
      have hs' : inFragment a.deref ∧ inFragment b.deref := by simpa using hs
      have ha := diverges_zero_of_inFragment a.deref hs'.1
      have hb := diverges_zero_of_inFragment b.deref hs'.2
      simp only [u_div_seq, ha, hb]
      rw [if_neg (by omega)]
  | lib.StmData.If c nc t e =>
      have hs' : inFragment t.deref ∧ inFragment e.deref := by simpa using hs
      have ht := diverges_zero_of_inFragment t.deref hs'.1
      have hee := diverges_zero_of_inFragment e.deref hs'.2
      simp only [u_div_if, ht, hee]
      rw [if_neg (by omega)]
  | lib.StmData.Assign _ _ => exact hs.elim
  | lib.StmData.Call _ _ => exact hs.elim
  | lib.StmData.DeadEnd _ => exact hs.elim
  | lib.StmData.Ret _ _ => exact hs.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact hs.elim
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── Lemma B (frame_after threads exactly addedHyp) over the fragment ──
theorem closeSem_frame_after (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (f : lib.FrameList) (a : lib.StmData) (st : St) (body : St → Prop)
    (ha : inFragment a) :
    closeSem hp he lv (lib.frame_after f a) st body
      ↔ closeSem hp he lv f st (fun st' => addedHyp hp a st' → body st') := by
  match a with
  | lib.StmData.Skip =>
      simp only [u_fafter_skip, u_added_skip]
      exact closeSem_congr hp he lv f st body _ (fun st' => by simp)
  | lib.StmData.Assume e =>
      simp only [u_fafter_assume, u_added_assume]
      rw [closeSem_append hp he lv f _ st body]
      exact closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])
  | lib.StmData.Assert o h =>
      simp only [u_fafter_assert, u_added_assert]
      rw [closeSem_append hp he lv f _ st body]
      exact closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])
  | lib.StmData.Seq a b =>
      have ha' : inFragment a.deref ∧ inFragment b.deref := by simpa using ha
      simp only [u_fafter_seq, u_added_seq]
      rw [closeSem_frame_after hp he lv (lib.frame_after f a.deref) b.deref st body ha'.2]
      rw [closeSem_frame_after hp he lv f a.deref st _ ha'.1]
      exact closeSem_congr hp he lv f st _ _ (fun st' => by
        constructor
        · intro k ⟨hka, hkb⟩; exact k hka hkb
        · intro k hka hkb; exact k ⟨hka, hkb⟩)
  | lib.StmData.If c nc t e =>
      have ha' : inFragment t.deref ∧ inFragment e.deref := by simpa using ha
      have ht : lib.diverges t.deref = 0 :=
        diverges_zero_of_inFragment t.deref ha'.1
      simp only [u_added_if]
      rw [u_fafter_if, if_neg (by omega)]
      exact closeSem_congr hp he lv f st body _ (fun st' => by simp)
  | lib.StmData.Assign _ _ => exact ha.elim
  | lib.StmData.Call _ _ => exact ha.elim
  | lib.StmData.DeadEnd _ => exact ha.elim
  | lib.StmData.Ret _ _ => exact ha.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact ha.elim
termination_by a
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

-- ══ MAIN: reference-WP soundness on the {Skip,Assume,Assert,Seq,If} fragment
--    over an ARBITRARY frame telescope (no isHypFrame restriction). ══
theorem wp_stm_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (s : lib.StmData) (f : lib.FrameList) (st : St)
    (hs : inFragment s) (hg : holdsAll hp he lv (lib.wp_stm f s) st) :
    closeSem hp he lv f st (fun st' => execSafe hp he s st') := by
  match s with
  | lib.StmData.Skip =>
      have : (fun st' => execSafe hp he lib.StmData.Skip st') = (fun _ : St => True) := by
        funext st'; simp
      rw [this]; exact closeSem_triv hp he lv f st
  | lib.StmData.Assume e =>
      have : (fun st' => execSafe hp he (lib.StmData.Assume e) st') = (fun _ : St => True) := by
        funext st'; simp
      rw [this]; exact closeSem_triv hp he lv f st
  | lib.StmData.Assert o h =>
      simp only [u_wp_assert, u_holdsAll_cons, u_holdsAll_nil, and_true] at hg
      rw [holds_close_e hp he lv f o st] at hg
      exact (closeSem_congr hp he lv f st _ _ (fun st' => by simp)).mpr hg
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
      have iht' : closeSem hp he lv f st (fun st' => hp c st' → execSafe hp he t.deref st') :=
        (closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])).mp iht
      have ihe' : closeSem hp he lv f st (fun st' => hp nc st' → execSafe hp he e.deref st') :=
        (closeSem_congr hp he lv f st _ _ (fun st' => by simp [u_cs_FHyp, u_cs_FNil])).mp ihe
      have hcomb := closeSem_and hp he lv f st _ _ iht' ihe'
      refine (closeSem_congr hp he lv f st _ _ (fun st' => ?_)).mp hcomb
      simp only [u_exec_if]
  | lib.StmData.Assign _ _ => exact hs.elim
  | lib.StmData.Call _ _ => exact hs.elim
  | lib.StmData.DeadEnd _ => exact hs.elim
  | lib.StmData.Ret _ _ => exact hs.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact hs.elim
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── top-level: ref_wp soundness for a fn whose body is in the fragment. The
--    genuine `lib.seed_frame` is an all-FBind telescope (typ_params ++
--    params/bounds ++ reqs); closeSem folds it as ∀-quantifiers — NO
--    isHypFrame restriction (the W5a-0 lift). ──
theorem ref_wp_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (lv : Int → St → Int) (c : lib.FnCtxData) (s : lib.StmData) (st : St)
    (hs : inFragment s) (hg : holdsAll hp he lv (lib.ref_wp c s) st) :
    closeSem hp he lv (lib.seed_frame c) st (fun st' => execSafe hp he s st') := by
  have hrw : lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s := rfl
  rw [hrw] at hg
  exact wp_stm_sound hp he lv s (lib.seed_frame c) st hs hg

-- ══ NON-VACUITY witnesses: the theorem BITES on concrete programs, with the
--    oracles fully opaque (so the obligation can only come from the goal). ══

-- (1) `if c { assert o }` (else Skip): from the single emitted goal (the then
--     branch's assert, closed under `c`), the obligation follows UNDER `hp c`.
--     The else (Skip) contributes no goal; execSafe's else conjunct is trivial.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (c nc : Int) (o : lib.RawExp) (h : Int) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.If c nc
                 (Tactus.Box.mk (lib.StmData.Assert o h))
                 (Tactus.Box.mk lib.StmData.Skip))) st) :
    hp c st → he (lib.render_exp o) st := by
  have hsound := wp_stm_sound hp he lv _ lib.FrameList.FNil st
    (by show (True ∧ True); exact ⟨trivial, trivial⟩) hg
  simp only [u_cs_FNil, u_exec_if, u_exec_assert, u_exec_skip] at hsound
  exact hsound.1

-- (2) ∀-param seed: with a single FBind `x`, the obligation must hold for ALL
--     valuations of `x` — the honest ∀ over a seed param. `he` opaque, so the
--     universally-quantified obligation genuinely comes from the emitted All-goal.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (lv : Int → St → Int)
    (x ty : Int) (o : lib.RawExp) (h : Int) (st : St)
    (hg : holdsAll hp he lv
            (lib.wp_stm (lib.FrameList.FBind x ty (Tactus.Box.mk lib.FrameList.FNil))
              (lib.StmData.Assert o h)) st) :
    ∀ n : Int, he (lib.render_exp o) (upd st x n) := by
  have hsound := wp_stm_sound hp he lv (lib.StmData.Assert o h)
    (lib.FrameList.FBind x ty (Tactus.Box.mk lib.FrameList.FNil)) st trivial hg
  simpa only [u_cs_FBind, u_cs_FNil, u_exec_assert] using hsound

end W5a1

-- axiom closure (regression guard): the soundness theorems close over ONLY the
-- standard logical axioms — no `Classical.choice` (render_exp stays opaque),
-- no `sorryAx`, no smuggled axioms.
#print axioms W5a1.wp_stm_sound   -- [propext, Quot.sound]
#print axioms W5a1.ref_wp_sound   -- [propext, Quot.sound]
