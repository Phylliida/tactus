import TactusDefs_lib_exec
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

-- ══════════════════════════════════════════════════════════════════════
-- W5f PROBE (board bootstrap-54) — the ADEQUACY SPINE: lift the Val-level
-- goal denotation `holds` (proven sound at the Val level by W5a–e / probe21–26)
-- up to the USER-FACING `Prop`s the user actually proves. Proven over the REAL
-- emitted `lib.wp_stm` / `lib.ref_wp` / `lib.render_exp` / `lib.type_of` /
-- `lib.needs_nat_coercion` / … (tactus-core/out/lib), NO tactus-core rebuild.
--
-- CARRIES OVER the full W5e core (probe26): the frame-carrying `execSafeF` and
-- the iff soundness theorem `wp_stm_sound : holdsAll (wp_stm f s) st ↔
-- execSafeF f s st` TOTAL over the whole StmData vocabulary, over an ARBITRARY
-- frame telescope, with the goal denotation `holds` PARAMETRIC over three
-- opaque leaf oracles (hp/he/lv). That is W5 v1: soundness at the Val level.
--
-- WHAT W5f ADDS (DESIGN-W5-soundness.md §2.1 note + §4 W5f row; master plan
-- §4.3 "adequacy spine"): W5 v1 states soundness with hp/he/lv OPAQUE. W5f
-- PINS a concrete interpretation of the leaf oracles and shows the resulting
-- `holds` denotes the user-facing `Prop`. THE DESIGN DECISION (this probe, cross-
-- checked w/ Danielle's local model 2026-07-15):
--
--   toProp := `holds` with the oracle triple PINNED to concrete interpretations.
--   The structural arms (Imp/All/Let) then bridge in ONE generic induction; ALL
--   genuine content concentrates in (a) a concrete leaf denotation `edenote`
--   and (b) per-user-type binder-embedding lemmas at the All arm. This keeps the
--   state space from exploding: the spine induction is generic (proved once), and
--   each user datatype contributes exactly ONE embedding lemma, not a re-proof.
--
-- THE SymEnv REALIZATION (why `edenote` is env-grounded, not hardcoded): the
-- emitted `ExprData.BinOp` opcode is an INTERNED u64 id (the serializer's string
-- table), NOT a fixed enum — `render_exp` rides it straight through opaquely. So
-- a FAITHFUL leaf denotation cannot know "op 2 means <" globally; it must ground
-- the interned ids through a `SymEnv` — exactly the per-crate environment literal
-- of master plan §4.3 / probe4_denote P4/P5. `edenote (E : SymEnv)` replaces W5's
-- OPACITY (`he` a free oracle) with concrete LOOKUP (`E.opk`, `E.av`, …); the
-- SymEnv is a concrete generated literal that kernel-reduces, so the leaf bridge
-- closes by `rfl`/`simp` (the P4 argument), catching nothing new about
-- determinism but pinning MEANING.
--
-- CO-DESIGN WITH W6 (now DONE): W5 was valuation-parametric precisely so the
-- oracle interpretation could be DEFERRED (DESIGN-W5-soundness §1, option b). W6
-- landed `render_exp : RawExp → ExprData` (deep expression rendering). W5f pins
-- `he := edenote ∘ (id on ExprData)` and consumes W6's `render_exp` as the
-- data-level bridge: `edenote E (render_exp re)` denotes exactly the user Prop —
-- so the highest-value silent-unsoundness class (the `as nat` cast / unsigned-
-- overflow refinement, DESIGN-W6-stageB §2) gets a DENOTATIONAL check here.
--
-- THE FOUR W5f FACTS this probe establishes:
--   1. adequacy_leaf_cmp     : `edenote E (render_exp (x < 10))` denotes exactly
--      `E.av x st < 10` — over the REAL render_exp (exercises the BinOp arm:
--      ref-deref balance + nat-coercion decisions, both no-ops here, Bool result).
--   2. adequacy_leaf_overflow: `edenote E (render_exp (HasType 64 e))` denotes
--      exactly `0 ≤ E.av e st ∧ E.av e st < 2^64` — over the REAL render_exp
--      (exercises the G6 unsigned-overflow EXPANSION + `pow2`, the §2 cast class).
--   3. toProp_all_embed      : the per-user-type binder embedding at the All arm
--      — the emitted `∀ (n:Int)` goal (Val model quantifies over ALL of Int)
--      IMPLIES the user-facing `∀ (u:U)` goal for any embedding `emb : U ↪ Int`,
--      THROUGH the state-thread `upd st x (emb u)` (the model-flagged trap: a
--      nested leaf reads the bound value; instantiating n := emb u decodes it
--      correctly). Sound by over-approximation. Composes through nesting.
--   4. soundness_concrete    : the carried `ref_wp_sound` INSTANTIATED at the
--      concrete oracle triple — "the emitted goals, read CONCRETELY via edenote,
--      hold" ⟺ "operational safety". The Val-level drift-detector lifted to
--      concrete user obligations.
--
-- Design + model: DESIGN-W5-soundness.md §2.1/§4 (W5f) + master plan §4.3/§8.5 +
-- board bootstrap-54. Extends probe26 (W5e). SymEnv shape follows probe4_denote.
-- ══════════════════════════════════════════════════════════════════════

namespace W5f

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
-- W5f LAYER: the adequacy spine. Concrete SymEnv-grounded leaf denotation +
-- the four adequacy facts. The Val-level core above stays UNTOUCHED (parametric
-- soundness); W5f is a THIN denotational bridge that pins the oracles.
-- ══════════════════════════════════════════════════════════════════════

-- Operator kinds: the FIXED-meaning logical/arithmetic operators. The SymEnv's
-- job is only to say WHICH interned opcode is which kind (a per-crate literal);
-- each kind then has a fixed Lean denotation. Mirrors probe4_denote's edenote.
inductive OpKind
  | add | sub | mul                       -- Int-valued arithmetic
  | eqI | ne | lt | le | gt | ge          -- comparisons (→ Prop)
  | andC | orC | impC                     -- logical connectives (→ Prop)
  | other                                 -- anything else (sort-error sentinel)
deriving DecidableEq

-- The per-crate symbol environment: grounds the interned ids of the emitted
-- goal language. A concrete generated literal (here left abstract as a structure
-- so the spine is proved for ANY such environment; a real crate supplies a
-- match-literal, cf. probe4_denote's SymEnv). §4.3 / probe4 P5.
structure SymEnv where
  av   : Int → St → Int        -- atom id → Int value in state (var reads, let ids)
  avP  : Int → St → Prop       -- atom id → Prop reading (bool var / opaque hyp leaf)
  opk  : Int → OpKind          -- interned BinOp opcode → its operator kind
  fn   : Int → Int → Int       -- App fn id → UNARY spec-fn interp (RawExp.Call)
  fnN  : Int → List Int → Int  -- AppN fn id → N-ARY spec-fn interp (RawExp.CallN)  [W5f v2]
  proj : Int → Int → Int       -- FieldProj (base value, field id) → projected value
  -- W5f v2 Match decode (board bootstrap-56): the flat-Int St model stores every
  -- datatype value as an Int, so a faithful `match` must DECODE that Int back to
  -- (constructor tag, field values). Two oracles pinned by the concrete crate
  -- literal CONSISTENTLY with the emitter's constructor encoding — same P5 oracle
  -- discipline as fn/fnN (a plain lookup; no fuel). `ctorTag`: scrutinee Int → its
  -- constructor id. `ctorField`: (scrutinee Int, 0-based field index) → field value.
  ctorTag   : Int → Int
  ctorField : Int → Nat → Int
-- THE GROUNDING (W5f v2, board bootstrap-55): a FAITHFUL leaf denotation does NOT
-- interpret spec-fn bodies with an in-Lean DefData evaluator — that can't be a
-- structural `def` (a recursive spec fn's body re-enters its own call ⇒ needs fuel
-- / a fixpoint). Instead — exactly the P5 shape (probe5_symenv.lean) — the concrete
-- per-crate SymEnv literal PINS `fn`/`fnN` to the ALREADY-EMITTED Lean spec fns
-- (`crateEnv.fn | tri_id => lib.tri | …`). Recursion + termination live in the
-- emitted defs (certified structural by W1.5); `eval`/`evalList` stay STRUCTURAL —
-- each App/AppN arm is ONE oracle application over recursively-eval'd args. The
-- rfl-bridge closes because the concrete env literal kernel-reduces (P5:
-- `gdenote crateEnv … = (… myDouble x …) := by rfl`). Consequence: a match-bodied
-- fn (`tri`) is grounded through `fn tri_id = lib.tri`, so a CALL to it denotes
-- `lib.tri (av n)` WITHOUT `eval` interpreting the `Match` node (the match is
-- inside `lib.tri`, which reduces on its own).

-- ── binder-threading for a matched arm (board bootstrap-56) ──
-- `bindArm E v bs i st` threads the arm's pattern binders into the state: the
-- k-th binder id in `bs` (starting from field index `i`) is bound to the decoded
-- field value `E.ctorField v (i+k)`, via `upd`. Standalone structural fold over
-- `BinderIdList` (NOT part of the eval mutual family — it never calls eval).
def bindArm (E : SymEnv) (v : Int) (bs : lib.BinderIdList) (i : Nat) (st : St) : St :=
  match bs with
  | lib.BinderIdList.Nil => st
  | lib.BinderIdList.Cons b rest => bindArm E v rest.deref (i + 1) (upd st b (E.ctorField v i))
termination_by structural bs

-- ── the concrete VALUE denotation of the Int-producing ExprData fragment ──
-- W5f v2: `eval`/`evalList`/`evalArms` are a MUTUAL STRUCTURAL triple over the
-- ExprData/ExprList/ArmList mutual inductive family. `AppN` folds its arg list;
-- `Match` decodes its scrutinee's constructor tag (`ctorTag`) and walks the arms,
-- threading the matched arm's binders (`bindArm`, via `ctorField`) into the body
-- denotation. Comparison / logical ops carry a DECIDABLE Bool-as-Int value (`if P
-- then 1 else 0`, P decidable on Int ⇒ no `Classical`) so an Ite whose condition
-- is a comparison denotes faithfully: `eval c ≠ 0 ↔ edenote c`.
mutual
def eval (E : SymEnv) (e : lib.ExprData) (st : St) : Int :=
  match e with
  | lib.ExprData.Atom id => E.av id st
  | lib.ExprData.Lit v => v
  | lib.ExprData.LitBool b => (b : Int)
  | lib.ExprData.Cast k x =>
      (match k with
       | lib.CastKind.IntToNat => ((eval E x.deref st).toNat : Int)   -- ↑(e).toNat = max e 0
       | lib.CastKind.NatToInt => eval E x.deref st)
  | lib.ExprData.BinOp op l r =>
      (match E.opk op with
       | OpKind.add => eval E l.deref st + eval E r.deref st
       | OpKind.sub => eval E l.deref st - eval E r.deref st
       | OpKind.mul => eval E l.deref st * eval E r.deref st
       -- comparisons / connectives in VALUE position → decidable Bool-as-Int:
       | OpKind.eqI => if eval E l.deref st = eval E r.deref st then 1 else 0
       | OpKind.ne  => if eval E l.deref st ≠ eval E r.deref st then 1 else 0
       | OpKind.lt  => if eval E l.deref st < eval E r.deref st then 1 else 0
       | OpKind.le  => if eval E l.deref st ≤ eval E r.deref st then 1 else 0
       | OpKind.gt  => if eval E l.deref st > eval E r.deref st then 1 else 0
       | OpKind.ge  => if eval E l.deref st ≥ eval E r.deref st then 1 else 0
       | OpKind.andC => if eval E l.deref st ≠ 0 ∧ eval E r.deref st ≠ 0 then 1 else 0
       | OpKind.orC  => if eval E l.deref st ≠ 0 ∨ eval E r.deref st ≠ 0 then 1 else 0
       | OpKind.impC => if (eval E l.deref st ≠ 0 → eval E r.deref st ≠ 0) then 1 else 0
       | OpKind.other => 0)
  | lib.ExprData.App f a => E.fn f (eval E a.deref st)
  | lib.ExprData.FieldProj x fld => E.proj (eval E x.deref st) fld
  | lib.ExprData.SpanMark _ x => eval E x.deref st                     -- span comment is meaning-transparent
  | lib.ExprData.Let n v b => eval E b.deref (upd st n (eval E v.deref st))
  | lib.ExprData.Not x => if eval E x.deref st ≠ 0 then 0 else 1       -- Bool negation as value
  | lib.ExprData.Ite c t e => if eval E c.deref st ≠ 0 then eval E t.deref st else eval E e.deref st
  | lib.ExprData.AppN f args => E.fnN f (evalList E args.deref st)     -- N-ARY grounding
  | lib.ExprData.Match s arms => evalArms E (eval E s.deref st) arms.deref st  -- faithful: decode tag, walk arms
  | lib.ExprData.Forall _ _ _ => 0                                     -- quantifier in value position: sentinel
  | lib.ExprData.Exists _ _ _ => 0
termination_by structural e

def evalList (E : SymEnv) (l : lib.ExprList) (st : St) : List Int :=
  match l with
  | lib.ExprList.Nil => []
  | lib.ExprList.Cons h t => eval E h.deref st :: evalList E t.deref st
termination_by structural l

-- Walk the arm list picking the arm whose constructor id matches the decoded
-- scrutinee tag `v`; on a hit, denote the body with the arm's binders threaded
-- (`bindArm`). No arm matched ⇒ sentinel 0 (a well-typed exhaustive `match` always
-- hits; this is the total-function default). Mutual with eval (recurses into arm
-- bodies) and structural on the ArmList.
def evalArms (E : SymEnv) (v : Int) (arms : lib.ArmList) (st : St) : Int :=
  match arms with
  | lib.ArmList.Nil => 0
  | lib.ArmList.Cons c bs body tl =>
      if E.ctorTag v = c then eval E body.deref (bindArm E v bs 0 st)
      else evalArms E v tl.deref st
termination_by structural arms
end

-- ── the concrete PROP denotation of the Prop-producing ExprData fragment ──
-- W5f v2 Match (board bootstrap-56): `edenote`/`edenoteArms` are a MUTUAL pair
-- (prop-position mirror of eval/evalArms). A `Match` in prop position decodes the
-- scrutinee tag (via the value-level `eval`) and denotes the matched arm's body as
-- a Prop, binders threaded by `bindArm`.
mutual
def edenote (E : SymEnv) (e : lib.ExprData) (st : St) : Prop :=
  match e with
  | lib.ExprData.BinOp op l r =>
      (match E.opk op with
       | OpKind.lt => eval E l.deref st < eval E r.deref st
       | OpKind.le => eval E l.deref st ≤ eval E r.deref st
       | OpKind.gt => eval E l.deref st > eval E r.deref st
       | OpKind.ge => eval E l.deref st ≥ eval E r.deref st
       | OpKind.eqI => eval E l.deref st = eval E r.deref st
       | OpKind.ne => eval E l.deref st ≠ eval E r.deref st
       | OpKind.andC => edenote E l.deref st ∧ edenote E r.deref st
       | OpKind.orC => edenote E l.deref st ∨ edenote E r.deref st
       | OpKind.impC => edenote E l.deref st → edenote E r.deref st
       | _ => eval E l.deref st ≠ 0)                                   -- arith op in Prop position: sentinel (unreachable in a well-sorted goal)
  | lib.ExprData.Not x => ¬ edenote E x.deref st
  | lib.ExprData.LitBool b => b = 1
  | lib.ExprData.Atom id => E.avP id st                               -- bool var / opaque hyp leaf
  | lib.ExprData.SpanMark _ x => edenote E x.deref st
  | lib.ExprData.Cast _ x => edenote E x.deref st                      -- cast in Prop position: transparent
  | lib.ExprData.Lit v => v ≠ 0                                        -- int literal as Prop (bool-as-int): truthiness
  | lib.ExprData.App _ _ => eval E e st ≠ 0                            -- Bool-returning unary call: truthiness
  | lib.ExprData.FieldProj _ _ => eval E e st ≠ 0
  | lib.ExprData.Let n v b => edenote E b.deref (upd st n (eval E v.deref st))
  -- W5f v2 body fragment (faithful):
  | lib.ExprData.Ite c t e => if eval E c.deref st ≠ 0 then edenote E t.deref st else edenote E e.deref st
  | lib.ExprData.AppN _ _ => eval E e st ≠ 0                           -- Bool-returning N-ary call: truthiness
  | lib.ExprData.Forall x _ b => ∀ n : Int, edenote E b.deref (upd st x n)   -- genuine ∀ (over Int; sound over-approx)
  | lib.ExprData.Exists x _ b => ∃ n : Int, edenote E b.deref (upd st x n)   -- genuine ∃
  | lib.ExprData.Match s arms => edenoteArms E (eval E s.deref st) arms.deref st  -- faithful: decode tag, walk arms
termination_by structural e

-- Prop-position arm walk (mirror of evalArms). No arm matched ⇒ `True` (vacuous
-- default; a well-typed exhaustive match always hits).
def edenoteArms (E : SymEnv) (v : Int) (arms : lib.ArmList) (st : St) : Prop :=
  match arms with
  | lib.ArmList.Nil => True
  | lib.ArmList.Cons c bs body tl =>
      if E.ctorTag v = c then edenote E body.deref (bindArm E v bs 0 st)
      else edenoteArms E v tl.deref st
termination_by structural arms
end

-- box-deref rfl helpers for the deep expression types (mirror the W5e u_box_*).
@[simp] theorem u_box_ed (x : lib.ExprData) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_re (x : lib.RawExp) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_al (x : lib.ArmList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_bil (x : lib.BinderIdList) : (Tactus.Box.mk x).deref = x := rfl
@[simp] theorem u_box_ral (x : lib.RawArmList) : (Tactus.Box.mk x).deref = x := rfl

-- hand `:= rfl` unfold lemmas for eval/edenote (their `termination_by structural`
-- form blocks simp's auto equation-lemma generation — the W5e u_holds_*/u_cs_*
-- idiom, here for the leaf denotation). Only the arms the leaf bridges exercise.
theorem u_eval_atom (E : SymEnv) (id : Int) (st : St) :
    eval E (lib.ExprData.Atom id) st = E.av id st := rfl
theorem u_eval_lit (E : SymEnv) (v : Int) (st : St) :
    eval E (lib.ExprData.Lit v) st = v := rfl
theorem u_edenote_binop (E : SymEnv) (op : Int) (l r : Tactus.Box lib.ExprData) (st : St) :
    edenote E (lib.ExprData.BinOp op l r) st =
      (match E.opk op with
       | OpKind.lt => eval E l.deref st < eval E r.deref st
       | OpKind.le => eval E l.deref st ≤ eval E r.deref st
       | OpKind.gt => eval E l.deref st > eval E r.deref st
       | OpKind.ge => eval E l.deref st ≥ eval E r.deref st
       | OpKind.eqI => eval E l.deref st = eval E r.deref st
       | OpKind.ne => eval E l.deref st ≠ eval E r.deref st
       | OpKind.andC => edenote E l.deref st ∧ edenote E r.deref st
       | OpKind.orC => edenote E l.deref st ∨ edenote E r.deref st
       | OpKind.impC => edenote E l.deref st → edenote E r.deref st
       | _ => eval E l.deref st ≠ 0) := rfl

-- W5f v2 unfold lemmas (same `:= rfl` idiom) for the widened body-fragment arms.
theorem u_eval_app (E : SymEnv) (f : Int) (a : Tactus.Box lib.ExprData) (st : St) :
    eval E (lib.ExprData.App f a) st = E.fn f (eval E a.deref st) := rfl
theorem u_eval_appn (E : SymEnv) (f : Int) (args : Tactus.Box lib.ExprList) (st : St) :
    eval E (lib.ExprData.AppN f args) st = E.fnN f (evalList E args.deref st) := rfl
theorem u_eval_ite (E : SymEnv) (c t e : Tactus.Box lib.ExprData) (st : St) :
    eval E (lib.ExprData.Ite c t e) st
      = (if eval E c.deref st ≠ 0 then eval E t.deref st else eval E e.deref st) := rfl
theorem u_evalList_nil (E : SymEnv) (st : St) :
    evalList E lib.ExprList.Nil st = [] := rfl
theorem u_evalList_cons (E : SymEnv) (h : Tactus.Box lib.ExprData) (t : Tactus.Box lib.ExprList) (st : St) :
    evalList E (lib.ExprList.Cons h t) st = eval E h.deref st :: evalList E t.deref st := rfl
theorem u_edenote_ite (E : SymEnv) (c t e : Tactus.Box lib.ExprData) (st : St) :
    edenote E (lib.ExprData.Ite c t e) st
      = (if eval E c.deref st ≠ 0 then edenote E t.deref st else edenote E e.deref st) := rfl
theorem u_edenote_forall (E : SymEnv) (x : Int) (ty : lib.TypData) (b : Tactus.Box lib.ExprData) (st : St) :
    edenote E (lib.ExprData.Forall x ty b) st = (∀ n : Int, edenote E b.deref (upd st x n)) := rfl
theorem u_edenote_exists (E : SymEnv) (x : Int) (ty : lib.TypData) (b : Tactus.Box lib.ExprData) (st : St) :
    edenote E (lib.ExprData.Exists x ty b) st = (∃ n : Int, edenote E b.deref (upd st x n)) := rfl
theorem u_edenote_appn (E : SymEnv) (f : Int) (args : Tactus.Box lib.ExprList) (st : St) :
    edenote E (lib.ExprData.AppN f args) st = (eval E (lib.ExprData.AppN f args) st ≠ 0) := rfl

-- W5f v2 Match-decode unfold lemmas (same `:= rfl` idiom).
theorem u_edenote_atom (E : SymEnv) (id : Int) (st : St) :
    edenote E (lib.ExprData.Atom id) st = E.avP id st := rfl
theorem u_bindArm_nil (E : SymEnv) (v : Int) (i : Nat) (st : St) :
    bindArm E v lib.BinderIdList.Nil i st = st := rfl
theorem u_bindArm_cons (E : SymEnv) (v b : Int) (rest : Tactus.Box lib.BinderIdList) (i : Nat) (st : St) :
    bindArm E v (lib.BinderIdList.Cons b rest) i st
      = bindArm E v rest.deref (i + 1) (upd st b (E.ctorField v i)) := rfl
theorem u_eval_match (E : SymEnv) (s : Tactus.Box lib.ExprData) (arms : Tactus.Box lib.ArmList) (st : St) :
    eval E (lib.ExprData.Match s arms) st = evalArms E (eval E s.deref st) arms.deref st := rfl
theorem u_evalArms_nil (E : SymEnv) (v : Int) (st : St) :
    evalArms E v lib.ArmList.Nil st = 0 := rfl
theorem u_evalArms_cons (E : SymEnv) (v c : Int) (bs : lib.BinderIdList)
    (body : Tactus.Box lib.ExprData) (tl : Tactus.Box lib.ArmList) (st : St) :
    evalArms E v (lib.ArmList.Cons c bs body tl) st
      = (if E.ctorTag v = c then eval E body.deref (bindArm E v bs 0 st)
         else evalArms E v tl.deref st) := rfl
theorem u_edenote_match (E : SymEnv) (s : Tactus.Box lib.ExprData) (arms : Tactus.Box lib.ArmList) (st : St) :
    edenote E (lib.ExprData.Match s arms) st = edenoteArms E (eval E s.deref st) arms.deref st := rfl
theorem u_edenoteArms_nil (E : SymEnv) (v : Int) (st : St) :
    edenoteArms E v lib.ArmList.Nil st = True := rfl
theorem u_edenoteArms_cons (E : SymEnv) (v c : Int) (bs : lib.BinderIdList)
    (body : Tactus.Box lib.ExprData) (tl : Tactus.Box lib.ArmList) (st : St) :
    edenoteArms E v (lib.ArmList.Cons c bs body tl) st
      = (if E.ctorTag v = c then edenote E body.deref (bindArm E v bs 0 st)
         else edenoteArms E v tl.deref st) := rfl

-- ══ FACT 1 — adequacy_leaf_cmp. The reference renderer applied to a Bool-result
--    comparison `x < 10` (Int operands) DENOTES exactly `E.av x st < 10`. Proven
--    over the REAL `lib.render_exp` (its BinOp arm: ref-deref balance = no-op on
--    Int operands; nat-coercion = no-op under a Bool result type). ══
theorem adequacy_leaf_cmp (E : SymEnv) (xId ltId : Int) (st : St)
    (hop : E.opk ltId = OpKind.lt) :
    edenote E (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))) st
      ↔ (E.av xId st < 10) := by
  -- render_exp reduces by rfl (structural) to the concrete BinOp; then the leaf
  -- denotation unfolds through u_edenote_binop + hop + the eval atom/lit lemmas.
  have hr : lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))
      = lib.ExprData.BinOp ltId (Tactus.Box.mk (lib.ExprData.Atom xId))
          (Tactus.Box.mk (lib.ExprData.Lit 10)) := rfl
  rw [hr]
  simp only [u_edenote_binop, hop, u_eval_atom, u_eval_lit]

-- ══ FACT 2 — adequacy_leaf_overflow. The reference renderer applied to a G6
--    unsigned-overflow refinement `HasType 64 e` DENOTES exactly the production
--    expansion `0 ≤ e ∧ e < 2^64`. Over the REAL `lib.render_exp` (the G6 arm
--    reuses one rendered `e` in both conjuncts) + `lib.pow2`. This is the §2
--    cast/overflow class — the highest-value silent-unsoundness surface — now
--    checked DENOTATIONALLY, not just structurally. Opcodes: And=11 Le=3 Lt=2. ══
theorem adequacy_leaf_overflow (E : SymEnv) (eId : Int) (st : St)
    (hAnd : E.opk 11 = OpKind.andC) (hLe : E.opk 3 = OpKind.le) (hLt : E.opk 2 = OpKind.lt) :
    edenote E (lib.render_exp
      (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.Var eId lib.TypData.TyInt)))) st
      ↔ (0 ≤ E.av eId st ∧ E.av eId st < 18446744073709551616) := by
  -- render_exp reduces (structural) to the concrete And/Le/Lt expansion (pow2 64
  -- = 2^64); u_edenote_binop unfolds all three BinOps, hAnd/hLe/hLt pick the arms.
  have hr : lib.render_exp
      (lib.RawExp.HasType 64 (Tactus.Box.mk (lib.RawExp.Var eId lib.TypData.TyInt)))
      = lib.ExprData.BinOp 11
          (Tactus.Box.mk (lib.ExprData.BinOp 3 (Tactus.Box.mk (lib.ExprData.Lit 0))
            (Tactus.Box.mk (lib.ExprData.Atom eId))))
          (Tactus.Box.mk (lib.ExprData.BinOp 2 (Tactus.Box.mk (lib.ExprData.Atom eId))
            (Tactus.Box.mk (lib.ExprData.Lit 18446744073709551616)))) := rfl
  rw [hr]
  simp only [u_edenote_binop, hAnd, hLe, hLt, u_eval_atom, u_eval_lit]

-- ══ the concrete oracle triple: pin hp/he/lv to the SymEnv interpretation. ══
--    he := edenote (deep obligation exprs get their concrete meaning);
--    hp := E.avP (opaque hyp / bool leaves → their Prop reading);
--    lv := E.av  (let-value leaves → their Int value).
def hpOf (E : SymEnv) : Int → St → Prop := fun id st => E.avP id st
def heOf (E : SymEnv) : lib.ExprData → St → Prop := fun e st => edenote E e st
def lvOf (E : SymEnv) : Int → St → Int := fun id st => E.av id st

-- toProp: the user-facing goal denotation = `holds` at the concrete triple.
def toProp (E : SymEnv) (g : lib.GoalData) (st : St) : Prop :=
  holds (hpOf E) (heOf E) (lvOf E) g st

-- ══ the GENERIC structural spine (adequacy_spine). The Val-level `holds` at the
--    concrete oracle triple IS `toProp` — the structural arms map through in ONE
--    step (definitional). Stated as a theorem (not just `rfl` inline) to mark the
--    generic-spine contract: `toProp` may later diverge structurally (SymEnv
--    binders) while the leaf work stays factored into `edenote` + the embedding. ══
theorem adequacy_spine (E : SymEnv) (g : lib.GoalData) (st : St) :
    holds (hpOf E) (heOf E) (lvOf E) g st ↔ toProp E g st := Iff.rfl

-- ══ FACT 3 — toProp_all_embed. The per-user-type binder embedding at the All
--    arm. The emitted `∀ (n : Int)` goal (the Val model quantifies over ALL of
--    Int) IMPLIES the user-facing `∀ (u : U)` goal for ANY embedding emb : U ↪
--    Int — sound by over-approximation. The model-flagged TRAP (a nested leaf in
--    the body reads the bound value from the threaded state) is resolved HERE:
--    instantiating n := emb u threads `upd st x (emb u)` into the body, so the
--    leaf reads the correctly-decoded value. Composes through nesting because the
--    body `t` is arbitrary. ══
theorem toProp_all_embed {U : Type} (E : SymEnv) (emb : U → Int)
    (x ty : Int) (t : lib.GoalData) (st : St)
    (h : toProp E (lib.GoalData.All x ty (Tactus.Box.mk t)) st) :
    ∀ u : U, toProp E t (upd st x (emb u)) := by
  -- unfold the All arm via the core's u_holds_all (holds is structural → use the
  -- hand rfl lemma, not `simp only [holds]`); then instantiate n := emb u.
  simp only [toProp, u_holds_all] at h
  intro u
  simp only [toProp]
  exact h (emb u)

-- Concrete instantiation of the embedding at U := Nat, emb := Int.ofNat — the
-- unsigned/overflow-refined quantifier (`∀ (m : u64)` renders as `∀ (m : Int),
-- 0 ≤ m → m < 2^64 → …` in the Val model; the user reads `∀ (m : Nat/u64)`). The
-- Val-level ∀-over-Int goal delivers the Nat-domain user goal. Not degenerate:
-- Int.ofNat is a genuine non-identity embedding.
example (E : SymEnv) (x ty : Int) (t : lib.GoalData) (st : St)
    (h : toProp E (lib.GoalData.All x ty (Tactus.Box.mk t)) st) :
    ∀ m : Nat, toProp E t (upd st x (Int.ofNat m)) :=
  toProp_all_embed E Int.ofNat x ty t st h

-- ══ FACT 4 — soundness_concrete. The carried Val-level `ref_wp_sound` (parametric
--    over oracles) INSTANTIATED at the concrete triple. "The emitted goals of
--    `ref_wp c s`, read CONCRETELY through `edenote` (so `holdsAll` is literally
--    the conjunction of the user's rendered obligations), hold" ⟺ "operational
--    safety `execSafeF` of the seed-framed program". The Val-level drift-detector,
--    now reading concrete user obligations. This is the W5f payoff: soundness
--    lifted from the opaque Val level to the pinned user-facing denotation. ══
theorem soundness_concrete (E : SymEnv) (c : lib.FnCtxData) (s : lib.StmData) (st : St) :
    holdsAll (hpOf E) (heOf E) (lvOf E) (lib.ref_wp c s) st
      ↔ execSafeF (hpOf E) (heOf E) (lvOf E) (lib.seed_frame c) s st :=
  ref_wp_sound (hpOf E) (heOf E) (lvOf E) c s st

-- box-deref rfl helper for ExprList (mirror u_box_ed; used by the AppN fold).
@[simp] theorem u_box_el (x : lib.ExprList) : (Tactus.Box.mk x).deref = x := rfl

-- ══════════════════════════════════════════════════════════════════════
-- W5f v2 — the body-fragment adequacy facts, each over the REAL `lib.render_exp`
-- (App/AppN/Forall/Ite arms), pinning the meaning of the widened `eval`/`edenote`.
-- The faithful `Match` facts (board bootstrap-56) follow after FACT 8 below.
-- ══════════════════════════════════════════════════════════════════════

-- ══ FACT 5 — adequacy_leaf_app_grounded. THE grounding: a spec-fn CALL inside an
--    obligation, `g(x) < 10`, DENOTES `g (E.av x st) < 10` where `g := E.fn fId`
--    is pinned to the real emitted spec fn (P5 shape). Over the REAL render_exp:
--    the `Call` arm's nat-coerce + ref-deref are no-ops on an Int arg/ret. When
--    `g` is instantiated to `lib.<userfn>`, this reads EXACTLY as the user Prop —
--    the whole point of v2. (A match-bodied `g` reduces on its own inside its Lean
--    def; `eval` never sees the match node.) ══
theorem adequacy_leaf_app_grounded (E : SymEnv) (nId fId ltId : Int) (g : Int → Int) (st : St)
    (hop : E.opk ltId = OpKind.lt) (hfn : E.fn fId = g) :
    edenote E (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Call fId lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt)) lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))) st
      ↔ (g (E.av nId st) < 10) := by
  have hr : lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.Call fId lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt)) lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 10 lib.TypData.TyInt)))
      = lib.ExprData.BinOp ltId
          (Tactus.Box.mk (lib.ExprData.App fId (Tactus.Box.mk (lib.ExprData.Atom nId))))
          (Tactus.Box.mk (lib.ExprData.Lit 10)) := rfl
  rw [hr]
  simp only [u_edenote_binop, hop, u_eval_app, u_eval_atom, u_eval_lit, hfn]

-- ══ FACT 6 — adequacy_leaf_forall. A quantified obligation `forall|i| body` (the
--    `RawExp.ForallR` node — a genuine quantifier INSIDE an expression, e.g.
--    `assert(forall|i| …)`) DENOTES a genuine `∀ n:Int, …`, with the binder
--    threaded into the (rendered) BODY denotation through `upd st i n` — for ANY
--    body (so it COMPOSES through nesting). This is the expr-level analog of the
--    goal-level All arm; the Int→user-type narrowing is `toProp_all_embed`. Stated
--    for arbitrary `body` (not a hardcoded leaf) because `E.av` is an OPAQUE oracle
--    — the honest content is the binder threading, not a specific numeric fact. ══
theorem adequacy_leaf_forall (E : SymEnv) (iId : Int) (ty : lib.TypData)
    (body : lib.RawExp) (st : St) :
    edenote E (lib.render_exp (lib.RawExp.ForallR iId ty (Tactus.Box.mk body))) st
      ↔ (∀ n : Int, edenote E (lib.render_exp body) (upd st iId n)) := by
  have hr : lib.render_exp (lib.RawExp.ForallR iId ty (Tactus.Box.mk body))
      = lib.ExprData.Forall iId ty (Tactus.Box.mk (lib.render_exp body)) := rfl
  rw [hr, u_edenote_forall, u_box_ed]

-- ══ FACT 6b — adequacy_leaf_exists. The `∃` mirror — a genuine `∃ n:Int, …` with
--    the same binder threading. Completes the quantifier fragment of the vocab. ══
theorem adequacy_leaf_exists (E : SymEnv) (iId : Int) (ty : lib.TypData)
    (body : lib.RawExp) (st : St) :
    edenote E (lib.render_exp (lib.RawExp.ExistsR iId ty (Tactus.Box.mk body))) st
      ↔ (∃ n : Int, edenote E (lib.render_exp body) (upd st iId n)) := by
  have hr : lib.render_exp (lib.RawExp.ExistsR iId ty (Tactus.Box.mk body))
      = lib.ExprData.Exists iId ty (Tactus.Box.mk (lib.render_exp body)) := rfl
  rw [hr, u_edenote_exists, u_box_ed]

-- ══ FACT 7 — adequacy_leaf_ite (VALUE sort). A spec `if b then x else 0` DENOTES
--    the decidable `if E.av b st ≠ 0 then E.av x st else 0` — the O9 value/prop
--    split resolved by a decidable Bool-as-Int condition (no `Classical`). Over
--    the REAL render_exp Ite arm (branch nat-coerce = no-op on Int branches). ══
theorem adequacy_leaf_ite (E : SymEnv) (bId xId : Int) (st : St) :
    eval E (lib.render_exp
      (lib.RawExp.Ite lib.TypData.TyInt
        (Tactus.Box.mk (lib.RawExp.Var bId lib.TypData.TyBool))
        (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt)))) st
      = (if E.av bId st ≠ 0 then E.av xId st else 0) := by
  have hr : lib.render_exp
      (lib.RawExp.Ite lib.TypData.TyInt
        (Tactus.Box.mk (lib.RawExp.Var bId lib.TypData.TyBool))
        (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
        (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt)))
      = lib.ExprData.Ite (Tactus.Box.mk (lib.ExprData.Atom bId))
          (Tactus.Box.mk (lib.ExprData.Atom xId)) (Tactus.Box.mk (lib.ExprData.Lit 0)) := rfl
  rw [hr]
  simp only [u_eval_ite, u_eval_atom, u_eval_lit]

-- ══ FACT 8 — adequacy_leaf_appn_grounded. The N-ARY grounding: a MULTI-arg spec-fn
--    call `h(m, n) < 100` DENOTES `h [E.av m st, E.av n st] < 100`, where `h :=
--    E.fnN fId` is pinned to the real emitted (n-ary) spec fn. Exercises the
--    `evalList` arg-fold over the REAL render_exp `CallN`→`AppN`/`render_list`
--    lowering. ══
theorem adequacy_leaf_appn_grounded (E : SymEnv) (mId nId fId ltId : Int)
    (h : List Int → Int) (st : St)
    (hop : E.opk ltId = OpKind.lt) (hfnN : E.fnN fId = h) :
    edenote E (lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.CallN fId lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawList.Cons
            (Tactus.Box.mk (lib.RawExp.Var mId lib.TypData.TyInt))
            (Tactus.Box.mk (lib.RawList.Cons
              (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt))
              (Tactus.Box.mk lib.RawList.Nil)))))))
        (Tactus.Box.mk (lib.RawExp.Lit 100 lib.TypData.TyInt)))) st
      ↔ (h [E.av mId st, E.av nId st] < 100) := by
  have hr : lib.render_exp
      (lib.RawExp.BinOp ltId lib.TypData.TyBool
        (Tactus.Box.mk (lib.RawExp.CallN fId lib.TypData.TyInt
          (Tactus.Box.mk (lib.RawList.Cons
            (Tactus.Box.mk (lib.RawExp.Var mId lib.TypData.TyInt))
            (Tactus.Box.mk (lib.RawList.Cons
              (Tactus.Box.mk (lib.RawExp.Var nId lib.TypData.TyInt))
              (Tactus.Box.mk lib.RawList.Nil)))))))
        (Tactus.Box.mk (lib.RawExp.Lit 100 lib.TypData.TyInt)))
      = lib.ExprData.BinOp ltId
          (Tactus.Box.mk (lib.ExprData.AppN fId
            (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom mId))
              (Tactus.Box.mk (lib.ExprList.Cons (Tactus.Box.mk (lib.ExprData.Atom nId))
                (Tactus.Box.mk lib.ExprList.Nil)))))))
          (Tactus.Box.mk (lib.ExprData.Lit 100)) := rfl
  rw [hr]
  simp only [u_edenote_binop, hop, u_eval_appn, u_evalList_cons, u_evalList_nil,
    u_eval_atom, u_eval_lit, hfnN]

-- ══════════════════════════════════════════════════════════════════════
-- W5f v2 MATCH decode (board bootstrap-56) — the faithful `Match` facts. Each
-- over the REAL `lib.render_exp`/`lib.render_arms`. The scrutinee is a var of a
-- named datatype (`TyNamed 100`); the two arms are
--   arm0: ctor c0, binds [xId], body `xId`     (READS the arm-0 binder)
--   arm1: ctor c1, binds [yId,zId], body `0`
-- with result type `TyInt` (⇒ `needs_nat_coercion _ TyInt = 0`: `render_arms`
-- inserts NO cast on any arm body). The honest new content vs probe28 is (a) arm
-- SELECTION by the decoded `ctorTag`, and (b) binder THREADING by `bindArm`/
-- `ctorField` — the arm body then reads the threaded slot via `E.av`/`E.avP`
-- exactly as `toProp_all_embed` resolves the `Forall` binder. The `ctorTag` value
-- is a hypothesis (as `hop`/`hfn` are in FACT 5/8); the concrete crate `SymEnv`
-- literal discharges it by `rfl`/`decide`.
-- ══════════════════════════════════════════════════════════════════════

-- ══ FACT 9 — adequacy_leaf_match_hd (VALUE). The decoded scrutinee tag selects
--    the FIRST arm, whose body reads its own bound binder `xId`: the whole match
--    DENOTES `E.av xId (upd st xId (ctorField v 0))` — the binder is bound to the
--    decoded field-0 value and the leaf reads it back through the threaded state. ══
theorem adequacy_leaf_match_hd (E : SymEnv) (scrutId c0 c1 xId yId zId : Int) (st : St)
    (htag : E.ctorTag (E.av scrutId st) = c0) :
    eval E (lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)) st
      = E.av xId (upd st xId (E.ctorField (E.av scrutId st) 0)) := by
  have hr : lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)
      = lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom scrutId))
          (Tactus.Box.mk (lib.ArmList.Cons c0
            (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
            (Tactus.Box.mk (lib.ExprData.Atom xId))
            (Tactus.Box.mk (lib.ArmList.Cons c1
              (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
              (Tactus.Box.mk (lib.ExprData.Lit 0))
              (Tactus.Box.mk lib.ArmList.Nil))))) := rfl
  rw [hr]
  simp only [u_eval_match, u_eval_atom, u_evalArms_cons]
  rw [if_pos htag]
  simp only [u_bindArm_cons, u_bindArm_nil]

-- ══ FACT 10 — adequacy_leaf_match_tl (VALUE). A tag that MISSES arm0 but hits
--    arm1: `evalArms` walks past the first arm (via `ctorTag v ≠ c0`) to the
--    second, whose body is `0`. Exercises the recursive arm WALK. ══
theorem adequacy_leaf_match_tl (E : SymEnv) (scrutId c0 c1 xId yId zId : Int) (st : St)
    (hmiss : E.ctorTag (E.av scrutId st) ≠ c0) (htag1 : E.ctorTag (E.av scrutId st) = c1) :
    eval E (lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)) st
      = 0 := by
  have hr : lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)
      = lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom scrutId))
          (Tactus.Box.mk (lib.ArmList.Cons c0
            (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
            (Tactus.Box.mk (lib.ExprData.Atom xId))
            (Tactus.Box.mk (lib.ArmList.Cons c1
              (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
              (Tactus.Box.mk (lib.ExprData.Lit 0))
              (Tactus.Box.mk lib.ArmList.Nil))))) := rfl
  rw [hr]
  simp only [u_eval_match, u_eval_atom, u_evalArms_cons]
  rw [if_neg hmiss, if_pos htag1]
  simp only [u_eval_lit]

-- ══ FACT 11 — adequacy_leaf_match_prop_hd (PROP). The prop-position mirror: in an
--    obligation whose top node is a `match`, the decoded tag selects arm0 and the
--    match DENOTES the arm-0 body's PROP reading with binder threaded —
--    `E.avP xId (upd st xId (ctorField v 0))`. Exercises `edenote`/`edenoteArms`. ══
theorem adequacy_leaf_match_prop_hd (E : SymEnv) (scrutId c0 c1 xId yId zId : Int) (st : St)
    (htag : E.ctorTag (E.av scrutId st) = c0) :
    edenote E (lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)) st
      ↔ E.avP xId (upd st xId (E.ctorField (E.av scrutId st) 0)) := by
  have hr : lib.render_exp
      (lib.RawExp.MatchR
        (Tactus.Box.mk (lib.RawExp.Var scrutId (lib.TypData.TyNamed 100)))
        (Tactus.Box.mk (lib.RawArmList.Cons c0
          (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
          (Tactus.Box.mk (lib.RawExp.Var xId lib.TypData.TyInt))
          (Tactus.Box.mk (lib.RawArmList.Cons c1
            (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
            (Tactus.Box.mk (lib.RawExp.Lit 0 lib.TypData.TyInt))
            (Tactus.Box.mk lib.RawArmList.Nil)))))
        lib.TypData.TyInt)
      = lib.ExprData.Match (Tactus.Box.mk (lib.ExprData.Atom scrutId))
          (Tactus.Box.mk (lib.ArmList.Cons c0
            (lib.BinderIdList.Cons xId (Tactus.Box.mk lib.BinderIdList.Nil))
            (Tactus.Box.mk (lib.ExprData.Atom xId))
            (Tactus.Box.mk (lib.ArmList.Cons c1
              (lib.BinderIdList.Cons yId (Tactus.Box.mk (lib.BinderIdList.Cons zId (Tactus.Box.mk lib.BinderIdList.Nil))))
              (Tactus.Box.mk (lib.ExprData.Lit 0))
              (Tactus.Box.mk lib.ArmList.Nil))))) := rfl
  rw [hr]
  simp only [u_edenote_match, u_eval_atom, u_edenoteArms_cons]
  rw [if_pos htag]
  simp only [u_bindArm_cons, u_bindArm_nil, u_edenote_atom]

end W5f

-- axiom closure (regression guard): the adequacy spine closes over ONLY the
-- standard logical axioms — no `Classical.choice`, no `sorryAx`, no smuggled
-- axioms. `render_exp`/`render_arms` reduce (structural), `eval`/`evalList`/
-- `evalArms` and `edenote`/`edenoteArms` reduce (mutual structural), `bindArm`
-- reduces (structural). The v2 body-fragment facts (App/AppN/Forall/Ite) add NO
-- new axioms — the Ite decidability is `Int.decEq` (constructive), the quantifier
-- is a genuine `∀`, the fn grounding is a plain oracle application. The v2 Match
-- facts add NO new axioms either — arm selection is a decidable `ctorTag v = c`
-- (`Int.decEq`), binder threading is a structural `upd`/`ctorField` fold.
#print axioms W5f.adequacy_leaf_cmp            -- v1
#print axioms W5f.adequacy_leaf_overflow       -- v1
#print axioms W5f.toProp_all_embed             -- v1
#print axioms W5f.soundness_concrete           -- v1
#print axioms W5f.wp_stm_sound                 -- v1
#print axioms W5f.adequacy_leaf_app_grounded   -- v2: App grounding (expect [propext])
#print axioms W5f.adequacy_leaf_forall         -- v2: Forall binder threading
#print axioms W5f.adequacy_leaf_exists         -- v2: Exists binder threading
#print axioms W5f.adequacy_leaf_ite            -- v2: Ite (decidable, no Classical)
#print axioms W5f.adequacy_leaf_appn_grounded  -- v2: AppN grounding + evalList fold
#print axioms W5f.adequacy_leaf_match_hd       -- v2 Match: tag→arm0 select + binder thread
#print axioms W5f.adequacy_leaf_match_tl       -- v2 Match: miss arm0 → walk to arm1
#print axioms W5f.adequacy_leaf_match_prop_hd  -- v2 Match: prop-position edenoteArms
