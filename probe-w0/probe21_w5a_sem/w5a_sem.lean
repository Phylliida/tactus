import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5a-0 PROBE (board bootstrap-49) — SOUNDNESS of the reference WP on the
-- straight-line fragment {Skip, Assume, Assert, Seq}, proven over the REAL
-- emitted `lib.wp_stm`/`lib.frame_after`/`lib.close_e`/`lib.goals_append`
-- (tactus-core/out/lib), the analog of probe14 for the bridge — no tactus-core
-- rebuild. Design + model: DESIGN-W5-soundness.md §1–3.
--
-- Valuation-parametric (open Q §5.5 = option b): the semantics takes leaf
-- oracles and the theorem quantifies over all of them.
--   hp : Int → St → Prop        opaque prop leaves (hyps + Leaf obligations)
--   he : ExprData → St → Prop    deep obligation exprs (render_exp stays OPAQUE)
-- W5a-0 restricts frames to FHyp/FNil (isHypFrame): the fragment's frame_after
-- only ever appends FHyp, so hyp-frames are closed under it. FLet (Assign) and
-- FBind/∀ (seed params) enter at W5a-1; here All/Let goal arms are unreached
-- and given a placeholder denotation (documented).
--
-- THEOREM (wp_stm_sound):
--   inFragment s → isHypFrame f → holdsAll (wp_stm f s) st → frameHyps f st
--     → execSafe s st
-- i.e. if the emitted goals all hold, every assert's obligation holds under its
-- accumulated hypothesis context — WP soundness for the fragment, with the leaf
-- interpretation entirely opaque.
--
-- IDIOM NOTE: the emitted structural defs reduce DEFINITIONALLY on constructors
-- but `simp [lib.close_e]` cannot generate their equational theorems ("invalid
-- projection x✝.2.1"). So we unfold via explicit `rfl` lemmas (`u_*`) and
-- `simp only [those]`, never `simp [defName]`.
-- ══════════════════════════════════════════════════════════════════════

namespace W5a0

abbrev St := Int → Int

-- ── §2.1 goal denotation (Val-level toProp). Imp/LeafE/Leaf are faithful;
--    All/Let are unreached under isHypFrame (W5a-1 gives them ∀/let). ──
def holds (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (g : lib.GoalData) (st : St) : Prop :=
  match g with
  | lib.GoalData.Leaf id => hp id st
  | lib.GoalData.LeafE e => he e st
  | lib.GoalData.Imp h t => hp h st → holds hp he t.deref st
  | lib.GoalData.All _ _ t => holds hp he t.deref st        -- W5a-1: ∀ n, … (upd)
  | lib.GoalData.Let _ _ t => holds hp he t.deref st        -- W5a-1: let x := v
termination_by structural g

def holdsAll (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (gs : lib.GoalList) (st : St) : Prop :=
  match gs with
  | lib.GoalList.Nil => True
  | lib.GoalList.Cons g t => holds hp he g.deref st ∧ holdsAll hp he t.deref st
termination_by structural gs

def frameHyps (hp : Int → St → Prop) (f : lib.FrameList) (st : St) : Prop :=
  match f with
  | lib.FrameList.FNil => True
  | lib.FrameList.FHyp h t => hp h st ∧ frameHyps hp t.deref st
  | lib.FrameList.FBind _ _ t => frameHyps hp t.deref st
  | lib.FrameList.FLet _ _ t => frameHyps hp t.deref st
termination_by structural f

def isHypFrame (f : lib.FrameList) : Prop :=
  match f with
  | lib.FrameList.FNil => True
  | lib.FrameList.FHyp _ t => isHypFrame t.deref
  | lib.FrameList.FBind _ _ _ => False
  | lib.FrameList.FLet _ _ _ => False
termination_by structural f

def inFragment (s : lib.StmData) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assert _ _ => True
  | lib.StmData.Seq a b => inFragment a.deref ∧ inFragment b.deref
  | _ => False
termination_by structural s

-- ── §2.2 operational safety (no re-derivation of the frame) ──
def addedHyp (hp : Int → St → Prop) (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Assume e => hp e st
  | lib.StmData.Assert _ h => hp h st
  | lib.StmData.Skip => True
  | lib.StmData.Seq a b => addedHyp hp a.deref st ∧ addedHyp hp b.deref st
  | _ => True
termination_by structural s

def execSafe (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (s : lib.StmData) (st : St) : Prop :=
  match s with
  | lib.StmData.Skip => True
  | lib.StmData.Assume _ => True
  | lib.StmData.Assert o _ => he (lib.render_exp o) st
  | lib.StmData.Seq a b =>
      execSafe hp he a.deref st ∧ (addedHyp hp a.deref st → execSafe hp he b.deref st)
  | _ => True
termination_by structural s

-- ══ definitional-unfold (rfl) lemmas — used with `simp only`, since
--    `simp [defName]` can't generate equational theorems for these defs. ══
section Unfold
variable (hp : Int → St → Prop) (he : lib.ExprData → St → Prop) (st : St)

-- emitted reference defs
@[simp] theorem u_box (x : lib.GoalData) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_close_FNil (o) :
    lib.close_e lib.FrameList.FNil o = lib.GoalData.LeafE (lib.render_exp o) := rfl
@[simp] theorem u_close_FHyp (h t o) :
    lib.close_e (lib.FrameList.FHyp h t) o
      = lib.GoalData.Imp h (Tactus.Box.mk (lib.close_e t.deref o)) := rfl
@[simp] theorem u_fapp_FNil (g) : lib.frame_append lib.FrameList.FNil g = g := rfl
@[simp] theorem u_fapp_FHyp (h t g) :
    lib.frame_append (lib.FrameList.FHyp h t) g
      = lib.FrameList.FHyp h (Tactus.Box.mk (lib.frame_append t.deref g)) := rfl
@[simp] theorem u_wp_assert (f o h) :
    lib.wp_stm f (lib.StmData.Assert o h)
      = lib.GoalList.Cons (Tactus.Box.mk (lib.close_e f o)) (Tactus.Box.mk lib.GoalList.Nil) := rfl
@[simp] theorem u_wp_seq (f a b) :
    lib.wp_stm f (lib.StmData.Seq a b)
      = lib.goals_append (lib.wp_stm f a.deref) (lib.wp_stm (lib.frame_after f a.deref) b.deref) := rfl
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
@[simp] theorem u_gapp_nil (b) : lib.goals_append lib.GoalList.Nil b = b := rfl
@[simp] theorem u_gapp_cons (g t b) :
    lib.goals_append (lib.GoalList.Cons g t) b
      = lib.GoalList.Cons g (Tactus.Box.mk (lib.goals_append t.deref b)) := rfl

-- our semantic defs
@[simp] theorem u_holds_leafE (e) :
    holds hp he (lib.GoalData.LeafE e) st = he e st := rfl
@[simp] theorem u_holds_imp (h t) :
    holds hp he (lib.GoalData.Imp h t) st = (hp h st → holds hp he t.deref st) := rfl
@[simp] theorem u_holdsAll_nil : holdsAll hp he lib.GoalList.Nil st = True := rfl
@[simp] theorem u_holdsAll_cons (g t) :
    holdsAll hp he (lib.GoalList.Cons g t) st
      = (holds hp he g.deref st ∧ holdsAll hp he t.deref st) := rfl
@[simp] theorem u_fh_FNil : frameHyps hp lib.FrameList.FNil st = True := rfl
@[simp] theorem u_fh_FHyp (h t) :
    frameHyps hp (lib.FrameList.FHyp h t) st = (hp h st ∧ frameHyps hp t.deref st) := rfl
@[simp] theorem u_ihf_FNil : isHypFrame lib.FrameList.FNil = True := rfl
@[simp] theorem u_ihf_FHyp (h t) :
    isHypFrame (lib.FrameList.FHyp h t) = isHypFrame t.deref := rfl
@[simp] theorem u_ihf_FBind (a b t) : isHypFrame (lib.FrameList.FBind a b t) = False := rfl
@[simp] theorem u_ihf_FLet (a b t) : isHypFrame (lib.FrameList.FLet a b t) = False := rfl
@[simp] theorem u_inf_seq (a b) :
    inFragment (lib.StmData.Seq a b) = (inFragment a.deref ∧ inFragment b.deref) := rfl
@[simp] theorem u_added_skip : addedHyp hp lib.StmData.Skip st = True := rfl
@[simp] theorem u_added_assume (e) : addedHyp hp (lib.StmData.Assume e) st = hp e st := rfl
@[simp] theorem u_added_assert (o h) : addedHyp hp (lib.StmData.Assert o h) st = hp h st := rfl
@[simp] theorem u_added_seq (a b) :
    addedHyp hp (lib.StmData.Seq a b) st
      = (addedHyp hp a.deref st ∧ addedHyp hp b.deref st) := rfl
@[simp] theorem u_exec_skip : execSafe hp he lib.StmData.Skip st = True := rfl
@[simp] theorem u_exec_assume (e) : execSafe hp he (lib.StmData.Assume e) st = True := rfl
@[simp] theorem u_exec_assert (o h) :
    execSafe hp he (lib.StmData.Assert o h) st = he (lib.render_exp o) st := rfl
@[simp] theorem u_exec_seq (a b) :
    execSafe hp he (lib.StmData.Seq a b) st
      = (execSafe hp he a.deref st ∧ (addedHyp hp a.deref st → execSafe hp he b.deref st)) := rfl
end Unfold

-- ── Lemma A (close): a hyp-frame-closed obligation holds iff, when the frame's
--    hyps hold, the obligation expr holds. render_exp stays opaque (under he). ──
theorem holds_close_e (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (f : lib.FrameList) (o : lib.RawExp) (st : St) (hf : isHypFrame f) :
    holds hp he (lib.close_e f o) st ↔ (frameHyps hp f st → he (lib.render_exp o) st) := by
  match f with
  | lib.FrameList.FNil => simp
  | lib.FrameList.FHyp h t =>
      have hft : isHypFrame t.deref := hf
      simp only [u_close_FHyp, u_holds_imp, u_fh_FHyp]
      rw [holds_close_e hp he t.deref o st hft]
      simp only [and_imp]
  | lib.FrameList.FBind _ _ _ => exact hf.elim
  | lib.FrameList.FLet _ _ _ => exact hf.elim
termination_by f
decreasing_by all_goals (simp_all; omega)

-- ── Lemma C (frame_append) over hyp-frames ──
theorem frameHyps_append (hp : Int → St → Prop) (f g : lib.FrameList) (st : St)
    (hf : isHypFrame f) :
    frameHyps hp (lib.frame_append f g) st ↔ frameHyps hp f st ∧ frameHyps hp g st := by
  match f with
  | lib.FrameList.FNil => simp
  | lib.FrameList.FHyp h t =>
      have hft : isHypFrame t.deref := hf
      simp only [u_fapp_FHyp, u_fh_FHyp]
      rw [frameHyps_append hp t.deref g st hft]
      simp only [and_assoc]
  | lib.FrameList.FBind _ _ _ => exact hf.elim
  | lib.FrameList.FLet _ _ _ => exact hf.elim
termination_by f
decreasing_by all_goals (simp_all; omega)

-- appending a single FHyp keeps a hyp-frame a hyp-frame
theorem isHypFrame_append_hyp (f : lib.FrameList) (h : Int) (hf : isHypFrame f) :
    isHypFrame (lib.frame_append f (lib.FrameList.FHyp h (Tactus.Box.mk lib.FrameList.FNil))) := by
  match f with
  | lib.FrameList.FNil => simp
  | lib.FrameList.FHyp h' t =>
      have hft : isHypFrame t.deref := hf
      simp only [u_fapp_FHyp, u_ihf_FHyp]
      exact isHypFrame_append_hyp t.deref h hft
  | lib.FrameList.FBind _ _ _ => exact hf.elim
  | lib.FrameList.FLet _ _ _ => exact hf.elim
termination_by f
decreasing_by all_goals (simp_all; omega)

-- frame_after preserves hyp-frames on the fragment
theorem isHypFrame_frame_after (f : lib.FrameList) (a : lib.StmData)
    (hf : isHypFrame f) (ha : inFragment a) :
    isHypFrame (lib.frame_after f a) := by
  match a with
  | lib.StmData.Skip => simpa using hf
  | lib.StmData.Assume e => simp only [u_fafter_assume]; exact isHypFrame_append_hyp f e hf
  | lib.StmData.Assert o h => simp only [u_fafter_assert]; exact isHypFrame_append_hyp f h hf
  | lib.StmData.Seq a b =>
      have ha' : inFragment a.deref ∧ inFragment b.deref := by simpa using ha
      simp only [u_fafter_seq]
      exact isHypFrame_frame_after (lib.frame_after f a.deref) b.deref
        (isHypFrame_frame_after f a.deref hf ha'.1) ha'.2
  | lib.StmData.Assign _ _ => exact ha.elim
  | lib.StmData.Call _ _ => exact ha.elim
  | lib.StmData.DeadEnd _ => exact ha.elim
  | lib.StmData.Ret _ _ => exact ha.elim
  | lib.StmData.If _ _ _ _ => exact ha.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact ha.elim
termination_by a
decreasing_by all_goals (simp_all; omega)

-- ── Lemma B (frame_after adds addedHyp) over hyp-frames on the fragment ──
theorem frameHyps_frame_after (hp : Int → St → Prop) (f : lib.FrameList)
    (a : lib.StmData) (st : St) (hf : isHypFrame f) (ha : inFragment a) :
    frameHyps hp (lib.frame_after f a) st ↔ frameHyps hp f st ∧ addedHyp hp a st := by
  match a with
  | lib.StmData.Skip => simp
  | lib.StmData.Assume e =>
      simp only [u_fafter_assume, u_added_assume]
      rw [frameHyps_append hp f _ st hf]; simp
  | lib.StmData.Assert o h =>
      simp only [u_fafter_assert, u_added_assert]
      rw [frameHyps_append hp f _ st hf]; simp
  | lib.StmData.Seq a b =>
      have ha' : inFragment a.deref ∧ inFragment b.deref := by simpa using ha
      have hfa : isHypFrame (lib.frame_after f a.deref) := isHypFrame_frame_after f a.deref hf ha'.1
      simp only [u_fafter_seq, u_added_seq]
      rw [frameHyps_frame_after hp (lib.frame_after f a.deref) b.deref st hfa ha'.2]
      rw [frameHyps_frame_after hp f a.deref st hf ha'.1]
      simp only [and_assoc]
  | lib.StmData.Assign _ _ => exact ha.elim
  | lib.StmData.Call _ _ => exact ha.elim
  | lib.StmData.DeadEnd _ => exact ha.elim
  | lib.StmData.Ret _ _ => exact ha.elim
  | lib.StmData.If _ _ _ _ => exact ha.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact ha.elim
termination_by a
decreasing_by all_goals (simp_all; omega)

-- ── Lemma D (goals_append) ──
theorem holdsAll_append (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (a b : lib.GoalList) (st : St) :
    holdsAll hp he (lib.goals_append a b) st ↔ holdsAll hp he a st ∧ holdsAll hp he b st := by
  match a with
  | lib.GoalList.Nil => simp
  | lib.GoalList.Cons g t =>
      simp only [u_gapp_cons, u_holdsAll_cons]
      rw [holdsAll_append hp he t.deref b st]
      simp only [and_assoc]
termination_by a
decreasing_by all_goals (simp_all; omega)

-- ══ MAIN: reference-WP soundness on the straight-line fragment ══
theorem wp_stm_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (s : lib.StmData) (f : lib.FrameList) (st : St)
    (hs : inFragment s) (hf : isHypFrame f)
    (hg : holdsAll hp he (lib.wp_stm f s) st) (hfr : frameHyps hp f st) :
    execSafe hp he s st := by
  match s with
  | lib.StmData.Skip => simp
  | lib.StmData.Assume e => simp
  | lib.StmData.Assert o h =>
      simp only [u_exec_assert]
      simp only [u_wp_assert, u_holdsAll_cons, u_holdsAll_nil, and_true] at hg
      rw [holds_close_e hp he f o st hf] at hg
      exact hg hfr
  | lib.StmData.Seq a b =>
      have hs' : inFragment a.deref ∧ inFragment b.deref := by simpa using hs
      simp only [u_exec_seq]
      simp only [u_wp_seq] at hg
      rw [holdsAll_append hp he _ _ st] at hg
      refine ⟨wp_stm_sound hp he a.deref f st hs'.1 hf hg.1 hfr, ?_⟩
      intro hadd
      have hfa : isHypFrame (lib.frame_after f a.deref) := isHypFrame_frame_after f a.deref hf hs'.1
      have hfra : frameHyps hp (lib.frame_after f a.deref) st := by
        rw [frameHyps_frame_after hp f a.deref st hf hs'.1]; exact ⟨hfr, hadd⟩
      exact wp_stm_sound hp he b.deref (lib.frame_after f a.deref) st hs'.2 hfa hg.2 hfra
  | lib.StmData.Assign _ _ => exact hs.elim
  | lib.StmData.Call _ _ => exact hs.elim
  | lib.StmData.DeadEnd _ => exact hs.elim
  | lib.StmData.Ret _ _ => exact hs.elim
  | lib.StmData.If _ _ _ _ => exact hs.elim
  | lib.StmData.Loop _ _ _ _ _ _ _ _ _ _ _ => exact hs.elim
termination_by s
decreasing_by all_goals (simp_all; omega)

-- ── top-level: ref_wp soundness for a fn whose body is in the fragment and
--    whose seed frame is a hyp-frame (no ∀-params / lets — the W5a-0 scope) ──
theorem ref_wp_sound (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (c : lib.FnCtxData) (s : lib.StmData) (st : St)
    (hs : inFragment s) (hf : isHypFrame (lib.seed_frame c))
    (hg : holdsAll hp he (lib.ref_wp c s) st) (hfr : frameHyps hp (lib.seed_frame c) st) :
    execSafe hp he s st := by
  have hrw : lib.ref_wp c s = lib.wp_stm (lib.seed_frame c) s := rfl
  rw [hrw] at hg
  exact wp_stm_sound hp he s (lib.seed_frame c) st hs hf hg hfr

-- ══ NON-VACUITY witnesses (probe discipline): the theorem BITES on concrete
--    programs — the emitted goal genuinely delivers the assert's obligation,
--    with the oracle `he` fully opaque (so `he (render_exp o) st` is NOT a
--    tautology; it can only come from the goal hypothesis). ══

-- (1) lone `assert o`: from the single emitted goal, the obligation `he
--     (render_exp o) st` follows. `inFragment`/`isHypFrame`/`frameHyps` of the
--     base cases are defeq `True` (`trivial`); `execSafe (Assert o h) st` is
--     defeq the goal.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (o : lib.RawExp) (h : Int) (st : St)
    (hg : holdsAll hp he
            (lib.wp_stm lib.FrameList.FNil (lib.StmData.Assert o h)) st) :
    he (lib.render_exp o) st :=
  wp_stm_sound hp he (lib.StmData.Assert o h) lib.FrameList.FNil st
    trivial trivial hg trivial

-- (2) `assume e; assert o`: the obligation is delivered UNDER the assumption e —
--     exactly the hypothesis threading `frame_after` performs. The `.2` projects
--     `execSafe (Seq …) = True ∧ (hp e st → he (render_exp o) st)`.
example (hp : Int → St → Prop) (he : lib.ExprData → St → Prop)
    (e : Int) (o : lib.RawExp) (h : Int) (st : St)
    (hg : holdsAll hp he
            (lib.wp_stm lib.FrameList.FNil
              (lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assume e))
                               (Tactus.Box.mk (lib.StmData.Assert o h)))) st) :
    hp e st → he (lib.render_exp o) st :=
  (wp_stm_sound hp he _ lib.FrameList.FNil st
    (by show True ∧ True; exact ⟨trivial, trivial⟩) trivial hg trivial).2

end W5a0

-- axiom closure (regression guard): the soundness theorems close over ONLY the
-- standard logical axioms — no `Classical.choice` (render_exp stays opaque, so
-- its noncomputability never enters), no `sorryAx`, no smuggled axioms.
#print axioms W5a0.wp_stm_sound   -- [propext, Quot.sound]
#print axioms W5a0.ref_wp_sound   -- [propext, Quot.sound]
