//! tactus-core: reference-semantics mirror types (bootstrap N2 / N2.1 / W1).
//!
//! These datatypes ARE the certificate vocabulary: their crate-defs
//! emission produces the Lean inductives that (a) the SST serializer
//! (N3) targets when printing per-fn SST literals and (b) the reference
//! WP (W2) consumes and produces. Single source of truth — no
//! hand-written Lean mirror, no O2 sync problem.
//!
//! Design constraints (probe-validated, DESIGN-bootstrap.md §11-12):
//! * OWN datatypes only — never Seq/Map (opaque axiom types: no match,
//!   no kernel reduction).
//! * No MUTUAL recursion between datatypes: `structural_decreases`
//!   covers only single-fn recursion, so statement sequencing is
//!   binary `Seq`/`Skip` (matching WP composition) instead of a
//!   statement list — the one cycle a Block list would create.
//!   One-way nesting (StmData → BinderList/LeafList/RawExpList, GoalList →
//!   GoalData) is fine.
//! * Every recursive spec fn carries `#[verifier::structural_decreases]`
//!   so the emitted defs kernel-compute (decide/rfl) with an empty
//!   axiom closure.
//! * Stage A (W2): expressions, types, locals, and binder names
//!   embedded in statements are OPAQUE LEAF IDS (u64) resolved through
//!   the serializer's side table of production-rendered Lean terms.
//! * Stage B (W6): obligation leaves optionally deepen into a structural
//!   `ExprData` tree (`GoalData::LeafE`), rendered by `render_exp` from the
//!   raw SST's type tags — ADDITIVE over stage A (refWp still emits
//!   `Leaf(u64)`; W6c wires the serializer to emit `LeafE`). Shape frozen by
//!   the W6a probe (probe-w0/probe12_w6a_castleaf); the reference renderer
//!   RE-DERIVES the `as nat` coercion from type tags, so a production emitter
//!   that applies it inconsistently diverges and the `decide` bridge catches
//!   it (DESIGN-W6-stageB.md §2/§3.1).
//!
//! N2.1 amendments (DESIGN-W2-refwp.md §0 / §2.1 — the fields refWp's
//! equations need, added BEFORE the serializer freezes the literal shape):
//! * `If` carries a rendered `¬cond` leaf (the else-branch hypothesis;
//!   refWp cannot synthesize leaf ids).
//! * `Loop` carries the modified-local havoc set (`binders` +
//!   `binder_bounds`), the invariant HYP leaves as NAMED `_h_ctx` ∀-hyps
//!   (`inv_hyps`, opaque), the parallel DEEP invariant OBLIGATIONS
//!   (`inv_obligs`, a `RawExpList` — W6d.1b-iii split the old dual-role
//!   prop slot: opaque frame-hyp vs deep goal), the loop condition
//!   (`cond_name`/`cond_ann`/`neg_cond_ann`), the `_tactus_d_old`
//!   decreases snapshot (`d_old_name`/`d_old_val`) and its DEEP obligation
//!   (`decrease_oblig`, a `RawExp`). refWp havocs the pre-loop lets,
//!   re-quantifies the modified locals, and re-closes each invariant
//!   (`close_each_e` over `inv_obligs`) + the decrease (`close_e`) at body
//!   end — mirroring production's `walk_loop` (finding-3).
//!   bootstrap-79 (break-form loops, `loop_normalize`'s
//!   `loop { setup; if !cond { break; } body }` rewriting of call-in-cond
//!   whiles): `setup` transcribes the `original_cond` setup stms (Skip
//!   for classical empty-setup loops — the classical derivation is
//!   byte-identical), `inv_obligs_break` carries the exit-reclose
//!   obligations (the break leaf; Nil for classical), and
//!   `neg_neg_cond_ann` the `¬(¬cond)` maintain else-guard leaf
//!   (999999 sentinel for classical). Non-Skip setup switches
//!   `wp_stm`/`frame_after`/`exec_safe_f` to the three-family break-form
//!   derivation (exit-reclose under the setup+¬cond ctx, maintain under
//!   setup+¬(¬cond), the post-loop continuation prefixed by the setup
//!   replay + ¬cond — ONE setup transcription, TWO derivations, the
//!   `decide` bridge validates both).
//! * `Call` carries the requires obligations (`reqs`) and the WHOLE
//!   post-call frame (`post: FrameList`) production's
//!   `push_post_call_frames` computes — "lowering the mirror"
//!   (DESIGN-W2-refwp.md §2.6): the post-call frame becomes explicit
//!   EVIDENCE the serializer transcribes (the naive ∀-path OR the #128
//!   ret-eq path in one uniform slot), not intent refWp re-derives, so
//!   refWp's Call arm is a pass-through and the `decide` bridge validates
//!   the serializer's replication against production.
//! * `Ret` carries a `RawExpList` — one annotated-ensures DEEP obligation
//!   per postcondition, rendered at the return site — plus a `RetBind`
//!   (finding-4): the `let <ret> := <e>` binding production prepends to
//!   the postcondition frame (`RetNone` for a unit return).
//! * `FnCtxData` (context seed for refWp): typ-param telescope, value
//!   params, per-param optional bound-hyp leaves, requires, ensures.
//! * `FrameList` / `CtxFrame`: the ONE ordered goal-spine frame the
//!   worker folds (interleaved binders/hyps/lets — three parallel lists
//!   cannot reproduce `∀x, h → let y := e; h2 → …` ordering; DESIGN
//!   §2.1 review fix).
//!
//! Covered vir::sst::StmX subset (tripwire test:
//! lean_verify/src/tests/bootstrap_coverage.rs): Assert, Assume,
//! Assign, Call (contract view), DeadEnd, Return, If, Loop, Block (as
//! Seq/Skip). Uncovered (stage B+): AssertBitVector, AssertQuery,
//! AssertCompute, Fuel, RevealString, BreakOrContinue, OpenInvariant,
//! ClosureInner, Air.
//!
//! Canonical check (live Lean, package gate — the M6.5 default; proof
//! fns always route to Lean under --lean-backend since e5f7aea, the
//! old --lean-all-proofs flag is gone):
//!   TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus \
//!     --crate-type=lib --lean-backend lib.rs

use vstd::prelude::*;

verus! {

// ── Leaf lists (self-recursive only) ────────────────────────────────

pub enum LeafList {
    Nil,
    Cons(u64, Box<LeafList>),
}

// W7: a list of interned binder ids — the bound-var ids of a `match` arm
// (`Leaf v` binds `[v]`, `Node l r` binds `[l, r]`, wildcards get a canonical
// positional id). A DEDICATED u64-list (not `LeafList`) so arm-binder lists
// stay their own certifiable surface (the crate's one-type-per-role idiom).
// Self-recursive only — no `structural_decreases` needed on its `_len`.
pub enum BinderIdList {
    Nil,
    Cons(u64, Box<BinderIdList>),
}

// ── Binder lists: (binder id, typ/kind leaf) pairs, self-recursive ──
// Reused for value-param telescopes, typ-param telescopes (kind leaf in
// the second slot), and Loop loop-state binders.

pub enum BinderList {
    Nil,
    Cons(u64, u64, Box<BinderList>),
}

// ── Per-param optional bound-hypothesis leaves ──────────────────────
// Parallel to `FnCtxData.params`. `NoBound` = this param has no range
// hypothesis (e.g. a datatype-typed param); `Bound(name, prop)` = an
// int-typed param's range hypothesis, rendered by production as a NAMED
// ∀-binder `∀ (h_x_bound : 0≤x∧x<2^64)` — `name` is the `h_<param>_bound`
// name leaf, `prop` the range-predicate leaf (finding-2). Distinct
// constructors rather than a sentinel leaf id, since 0 is a valid
// interned leaf.

pub enum ParamBoundList {
    Nil,
    NoBound(Box<ParamBoundList>),
    Bound(u64, u64, Box<ParamBoundList>),
}

// ── F4 (bootstrap-80 stage 2): the poison-derivation side table ─────
// (prop leaf id, deep `RawExp` transcription, tail) — one entry per
// poison-CHECKED prop (FHyp props, FLetH/RetLetH eq props, cond props,
// IfCtor eq/neg props; the serializer registers an entry at every
// `hyp_poison` call site and asserts totality at emission). Hyp props
// stay opaque leaf ids in GOALS (byte-neutrality); this table exists so
// refWp can DERIVE the wrap-gate poison mark (`poisoned_props`) instead
// of trusting a serializer-computed bit (endgame P1 — the mark was the
// one trusted semantic predicate on the cert path; the N2 IsVariant
// detector is the remaining one, scoped out of F4). The transcription is
// the dumb faithful copy (the same `raw_exp` SST path as obligation
// slots) — the mention projection happens reference-side, never
// serializer-side.
pub enum PropDeepList {
    Nil,
    Cons(u64, Box<RawExp>, Box<PropDeepList>),
}

// ── `&mut`-param fn-entry preamble entries (bootstrap-78 S2) ────────
// One entry per `&mut` param (and per `BorrowMut` local, production's
// #107 synthetic mut_ref class), in production's declaration order:
// `Cons(param name leaf, at_pre name leaf, deref value leaf, tail)`.
// `at_pre` is the `<p>_at_pre_tactus` old()-snapshot name; the deref
// value leaf is the interned `<p>.deref` text (production's exact pp,
// the FLetH typ/eq-leaf precedent — the entry's inner typ has no S2
// consumer and is NOT carried; the call-site mut frames get their typs
// per-call in `Call.post`, D1). refWp DERIVES the two fn-entry frames
// structurally per entry (`mut_preamble_frame`):
//
//   FLet(at_pre, deref)   -- old() snapshot:  let <p>_at_pre_tactus := <p>.deref
//   FLet(p,      deref)   -- body shadow:     let <p> := <p>.deref
//
// Both PLAIN FLets: production builds them as TYP-LESS `CtxFrame::Let`s
// (`add_pre_capture`/`add_body_shadow`, sst_to_lean ~1517), so
// `hoist_all` bails and every goal of a mut-param fn renders in WRAP
// mode — which the mirror gets for free from `has_plain_flet` over the
// seeded frame (vec_push7 evidence: params + reqs stay theorem binders
// via FBind→All; the preamble lets and everything after render
// goal-position).

pub enum MutParamList {
    Nil,
    Cons(u64, u64, u64, Box<MutParamList>),
}

// ── Return-value binding (finding-4) ────────────────────────────────
// Production binds the returned value as a frame `let` before the
// postcondition obligation: a `return e` / tail-expression whose fn
// declares `-> (r: T)` renders `let r := <e>; <ensures>` (the walker's
// `Wp::Done(let_bind_synthetic(sanitize(ret), e_ast, ensures_goal))`,
// peeled into a `CtxFrame::Let` by `emit_done_or_split`). refWp's Ret
// arm prepends this `let` to the frame before closing each ensures.
// `RetNone` = a unit return (`return;`) or no declared return var — no
// binding. `RetLet(name, val)` = the `sanitize(ret)` name leaf and the
// rendered return-expression value leaf. Distinct constructors (not a
// sentinel leaf) since 0 is a valid interned leaf, and to keep the
// trusted SST literal's valid states exhaustive at a glance.

pub enum RetBind {
    RetNone,
    RetLet(u64, u64),
    /// (ret binder id, typ leaf, value leaf, eq-name leaf, eq-prop leaf) —
    /// the HOISTABLE return-value binding (bootstrap-74 slice 2). Production
    /// hoists a typed non-Bool `let r := e` into the binder pair
    /// `(r : T) (_h_r_hoist1 : r = e)`; `ret_frame` appends an `FLetH`.
    /// In wrap mode (the gate tripped) it renders `Let(r, e)` exactly like
    /// `RetLet`, so the two are interchangeable whenever the goal wraps.
    RetLetH(u64, u64, u64, u64, u64),
}

// ── Statements: the Wp-input mirror (stage-A subset) ────────────────

pub enum StmData {
    /// StmX::Assert — (annotated obligation `RawExp`, hyp NAME leaf, bare
    /// hyp leaf). The GOAL this assert emits closes the
    /// ANNOTATED obligation
    /// (`/- @rust:LOC -/ prop`, production's `span_mark` render) via
    /// `close_e` → `LeafE(render_exp(ob))` (W6d.1b: the obligation slot is
    /// now the DEEP raw-SST mirror, not an opaque `u64`); the forward HYP it
    /// adds for the rest of the body still uses the BARE prop leaf (an
    /// opaque `u64` — hypotheses are not deepened, only obligations).
    /// Production renders `cond_ast` once and uses it span_mark'd for the
    /// goal, bare for the hyp (sst_to_lean::walk_obligations) — the fixture
    /// certs show goal `LeafE …` (annotated) alongside forward `Imp 8`
    /// (bare) for the SAME assert (finding-1). Fixtures with an opaque
    /// obligation use `atom_ob(id)` (= `Var(id, TyBool)`, renders to
    /// `Atom(id)`) so the deep spine matches the stage-A ids by construction.
    /// The hyp NAME (`_h_hoist_i`, bootstrap-74 slice 2) is the serializer's
    /// mirror of production's hyp ordinal. F4 (bootstrap-80 stage 2): the
    /// poison bit is GONE — the wrap-gate poison mark is DERIVED
    /// reference-side (`poisoned_props` over `FnCtxData.prop_deeps`).
    Assert(RawExp, u64, u64),
    /// StmX::Assume — (hyp NAME leaf, prop leaf). Same
    /// naming discipline as `Assert`.
    Assume(u64, u64),
    /// StmX::Assign — (dest local leaf, rhs leaf). Plain form: a let that
    /// is NOT hoistable — typ-less, or (slice-2 collapse) a hoistable let
    /// whose equation prop mentions a residue name. F4: the
    /// poison-collapse is DERIVED reference-side (`frame_after`'s
    /// AssignH arm), LOSSLESS either way: poison forces the whole goal
    /// into wrap mode, where the hoist payload (typ/eq leaves) is
    /// discarded anyway.
    Assign(u64, u64),
    /// StmX::Assign, HOISTABLE (bootstrap-74 slice 2) — (dest leaf, typ
    /// leaf, rhs leaf, eq-name leaf, eq-prop leaf): a typed non-Bool
    /// `x = e` that production's `hoist_all` lifts to the binder pair
    /// `(x : T) (_h_x_hoist1 : x = e)`. Becomes an `FLetH` frame; wrap
    /// mode renders it `Let(x, e)` exactly like `Assign`.
    AssignH(u64, u64, u64, u64, u64),
    /// StmX::Assign, RESIDUE (bootstrap-74 slice 2) — (dest leaf, rhs
    /// leaf): a BOOL-typed `x = e` (an if-condition temp like
    /// `tmp__1 := s < 2000`). Production keeps Bool lets in GOAL POSITION
    /// (the "residue") while the other frames hoist — hoisting them as
    /// propositional equations loops simp (the nested_if maxRecDepth
    /// regression). Becomes an `FLetR` frame.
    AssignR(u64, u64),
    /// StmX::Call — the requires OBLIGATIONS (`reqs`, a `RawExpList` of DEEP
    /// obligations closed via `close_each_e`; W6d.1b-ii) instantiated at the
    /// call's actual args, and the entire POST-CALL FRAME (`post`) the
    /// walker appends for whatever FOLLOWS the call. "Lowering the mirror"
    /// (DESIGN-W2-refwp.md §2.6): `post` is the frame delta production's
    /// `push_post_call_frames` computes, carried as explicit evidence in one
    /// uniform slot — EITHER the naive ∀-path
    /// (`FBind(dest, ret_typ, [FHyp(ret_bound)] FHyp(ens))`) OR the #128
    /// ret-eq path (`[FHyp(E_bound)] [FHyp(rest)] FLet(dest, E)`, chosen when
    /// a callee ensures conjunct is `r == E` with `E ∌ r`). refWp is then a
    /// pass-through — `frame_after` appends `post` verbatim, `wp_stm` closes
    /// each req — so the `decide` bridge validates the serializer's
    /// `push_post_call_frames` replication against production (non-circular:
    /// the serializer recomputes the frame, it does not copy production's),
    /// and this generalizes to the coming `&mut` post-state / prophecy
    /// frames instead of perpetually growing refWp's Call arm.
    Call { reqs: Box<RawExpList>, post: Box<FrameList> },
    /// StmX::DeadEnd — verify inside, discard facts after.
    DeadEnd(Box<StmData>),
    /// StmX::Return — annotated ensures obligations (a `RawExpList` of DEEP
    /// obligations, one span_mark'd obligation per postcondition, closed via
    /// `close_each_e` at the return site like production's `WpCtx`
    /// postcondition — finding-1's Ret-annotation; W6d.1b-ii), plus the
    /// return-value binding `let <ret> := <e>` production prepends before the
    /// postcondition (`RetBind`, finding-4). refWp closes each ensures under
    /// the frame extended by the return binding.
    Ret(Box<RawExpList>, RetBind),
    /// StmX::If — (cond leaf, cond-hyp NAME leaf, ¬cond leaf, ¬cond-hyp
    /// NAME leaf, then, else); absent else = Skip.
    /// Both prop leaves are ANNOTATED (span_mark'd), byte-matching production's
    /// `Wp::Branch`: it pushes `cond_marked =
    /// span_mark(loc, Hypothesis(BranchCondition), cond)` as the then-branch
    /// hyp and `not(cond_marked)` as the else-branch hyp
    /// (`sst_to_lean::walk_obligations`). The serializer mints them via
    /// `oblig_leaf`/`neg_oblig_leaf` (the
    /// `AssertKind` never reaches the pp, so an `Obligation(Plain)` mark
    /// interns to the SAME text as production's `BranchCondition` mark —
    /// bootstrap-17). The `cond` leaf is the then-branch hyp; `¬cond` is
    /// BOTH the else-branch hyp AND the fall-through continuation hyp when
    /// the then-branch DIVERGES (`frame_after`, DESIGN §2.4.1). The name
    /// leaves are the serializer's `_h_hoist_i` mirror (bootstrap-74 slice
    /// 2); the poison of both hyps is DERIVED (`c` and `¬c` share the
    /// mention set) — a cond mentioning a residue let (e.g. `if tmp__1`)
    /// forces whole-goal wrap.
    If(u64, u64, u64, u64, Box<StmData>, Box<StmData>),
    /// StmX::Loop — the maintain/use telescopes production builds around a
    /// loop (finding-3, UNIFORM post-N1-hoist shape — bootstrap-74 slice
    /// 2, evidence DESIGN-b74-slice2-serializer §2b). Production havocs
    /// the modified locals, re-quantifies them as ∀-binders, re-asserts
    /// each mod-var's type bound / each invariant / the loop condition as
    /// NAMED `_h_hoist_i` hyps (the `_h_ctx_N` naming is GONE from goal
    /// shapes — it survives only in this node's `inv_hyps` side-table,
    /// consumed by the WP semantics, not the goals), and snapshots the
    /// decreases measure in a `_tactus_d_old` let that HOISTS as an
    /// `FLetH` binder pair (typed, non-Bool). The old
    /// leading/non-leading (`has_let`) distinction is DEAD: nested loops
    /// are flat concatenation under one per-goal hyp counter — a
    /// surviving pre-loop plain `FLet` still wrap-forces the goal, but
    /// via the GLOBAL gate, not a loop-local switch. Fields:
    /// * `inv_hyps` — one `(_h_hoist name leaf, invariant HYP leaf)` per
    ///   standard invariant (the serializer computes the per-goal
    ///   ordinals), consumed by the maintain/use ∀-telescope as the
    ///   re-asserted HYPOTHESIS (an opaque `u64`, byte-matched —
    ///   hypotheses are not deepened). W6d.1b-iii split the old dual-role
    ///   prop slot: the frame keeps the opaque hyp here; the deep
    ///   obligation moves to `inv_obligs`.
    /// * `inv_obligs` — the DEEP invariant OBLIGATION `RawExp` per invariant
    ///   (W6d.1b-iii), index-aligned with `inv_hyps`, closed at init AND
    ///   maintain-reclose via `close_each_e` → `LeafE(render_exp(ob))`.
    ///   Production reuses the one span_mark'd leaf for both roles, so in
    ///   the fixture `inv_hyps`'s prop id == the `Atom` id inside the
    ///   aligned `inv_obligs` entry (`atom_ob(prop)`); deepening splits
    ///   them by TYPE (opaque frame-hyp `u64` vs structural goal `RawExp`),
    ///   not by content.
    /// * `inv_obligs_exit` — the RENAMED re-close obligations
    ///   (bootstrap-74 slice 2 Round D evidence): at body end,
    ///   production's shadow mirror rewrites the invariant texts'
    ///   references to shadowed locals (`i_hoist1 ≤ n`,
    ///   `Int.toNat acc_hoist1 = lib.tri (Int.toNat i_hoist1)` — fresh
    ///   leaf ids, distinct from the init obligations' plain-`i`
    ///   texts). Index-aligned with `inv_obligs`; closed ONLY at
    ///   maintain-reclose (init keeps `inv_obligs`).
    /// * `inv_obligs_break` — the EXIT-RECLOSE obligations
    ///   (bootstrap-79, break-form loops only): the invariant texts at
    ///   the post-SETUP rename state, closed at the normalized body's
    ///   `if ¬cond { break }` break leaf. Byte-equal to `inv_obligs`
    ///   when the setup rebinds no mod var (the common case — cond
    ///   setup assigns only compiler temps). `RawExpList::Nil` for
    ///   classical empty-setup loops (no break leaf ever fires).
    /// * `setup` — the transcribed cond-setup stms (bootstrap-79):
    ///   `StmData::Skip` for a classical empty-setup while; otherwise
    ///   the `original_cond` setup (ordinary Assign/Call content).
    ///   refWp splices the setup's frames at the THREE positions
    ///   production's two physical walks produce them (maintain/body
    ///   walk under the maintain telescope; exit-reclose telescope;
    ///   post-loop continuation prefix) — ONE transcription, TWO
    ///   derivations, the `decide` bridge validates both against
    ///   production's body copy and `original_cond` exit copy.
    /// * `neg_neg_cond_ann` — the ANNOTATED `¬(¬cond)` leaf (the
    ///   normalized If's ELSE-guard, maintain path; break-form only,
    ///   999999 sentinel for classical). The guard hyps share
    ///   `cond_name` (the per-goal-path walk ordinals coincide — the
    ///   d_old eq-hyp is name-based, not ordinal-consuming).
    /// * `break_guard_ann` — the SPAN-MARK'D `¬cond` leaf (break-form
    ///   only, 999999 for classical): the exit-reclose telescope's
    ///   If-then-guard hyp, `/- @rust:…-/ ¬(…)` — production's walk_if
    ///   marks the synthesized `¬exp` itself (comment OUTSIDE the
    ///   negation), unlike the classical use hyp's `¬(/- …-/ …)`.
    /// * `break_use_ann` — the BARE `¬cond` leaf (break-form only,
    ///   999999 for classical): the post-loop continuation's exit-fact
    ///   hyp — production's `exit_wrap` pushes `LExpr::not(cond)` with
    ///   NO span_mark (`build_wp_loop`'s `neg_cond_lexpr`), so the
    ///   comment is absent here too.
    /// * `binders` — the modified-local havoc set `(id, typ leaf)`.
    /// * `binder_bounds` — parallel `(NoBound | Bound(_h_hoist name, range
    ///   prop))` per modified local (production re-asserts each mod-var's
    ///   type bound as a NAMED `_h_hoist_i` hyp right after its ∀-binder —
    ///   sum_to evidence: `All[i] (All[_h_hoist_1 : 0 ≤ i ∧ …]`).
    /// * `cond_name` / `cond_ann` / `neg_cond_ann` — the
    ///   cond hyp's `_h_hoist_i` name, the ANNOTATED `cond` leaf
    ///   (maintain) and `¬cond` leaf (use). The cond poison is DERIVED
    ///   (F4): a cond mentioning a residue let forces whole-goal wrap.
    /// * `d_old_name` / `d_old_ty` / `d_old_val` / `d_old_eq_name` /
    ///   `d_old_eq_prop` — the `_tactus_d_old_<id>_0` snapshot let as an
    ///   FLetH pair (maintain only): binder typ leaf, rendered measure
    ///   value, eq-name `_h__tactus_d_old_<id>_0_hoist1`, eq-prop
    ///   `_tactus_d_old_<id>_0 = <measure>`.
    /// * `decrease_oblig` — the ANNOTATED `0 ≤ D ∧ D < d_old` obligation, a
    ///   DEEP `RawExp` (W6d.1b-iii, like `Assert`'s obligation slot), closed at
    ///   body end via `close_e` alongside the maintain invariants.
    Loop {
        inv_hyps: Box<BinderList>,
        inv_obligs: Box<RawExpList>,
        inv_obligs_exit: Box<RawExpList>,
        inv_obligs_break: Box<RawExpList>,
        binders: Box<BinderList>,
        binder_bounds: Box<ParamBoundList>,
        cond_name: u64,
        cond_ann: u64,
        neg_cond_ann: u64,
        neg_neg_cond_ann: u64,
        break_guard_ann: u64,
        break_use_ann: u64,
        d_old_name: u64,
        d_old_ty: u64,
        d_old_val: u64,
        d_old_eq_name: u64,
        d_old_eq_prop: u64,
        decrease_oblig: RawExp,
        setup: Box<StmData>,
        body: Box<StmData>,
    },
    /// StmX::AssertQuery (mode NonLinear) — an ISOLATED verification
    /// query (`assert … by(nonlinear_arith)`): production emits the
    /// body's obligations under a scope that keeps Let/Binder frames
    /// and DROPS Hyp frames (`OblCtx::new_scope`, sst_to_lean.rs), then
    /// control falls through with NO frame delta — the proven facts
    /// re-enter the main flow via the `Assume` statements Verus itself
    /// emits after the query (same as assert-by/DeadEnd). The mirror:
    /// `wp_stm` recurses on the body under `strip_hyps(f)`;
    /// `frame_after` is `f`.
    /// The second field is the query's DEGENERATE ensures obligation
    /// (bootstrap-74 slice 2): the query's own ensures is empty, so
    /// production emits one final in-scope goal `True`
    /// (`emit_done_or_split`'s `and_all([])` fallback, the
    /// `_tactus_ensures_` theorem — mul_bound evidence). refWp closes
    /// it under `frame_after(strip_hyps(f), body)` — the body's own
    /// assert hyps DO accumulate inside the query (only the OUTER hyps
    /// are stripped). The serializer fills the slot with
    /// `atom_ob("True")`.
    AssertQueryNl(Box<StmData>, RawExp),
    /// StmX::AssertQuery (mode Tactus, kind AssertBy) — `assert(P) by
    /// { <lean tactic> }` (bootstrap-77 / b69 residue; endgame Q1:
    /// first-class variant). Production (`walk_assert_by_tactus` with
    /// `Some(P)`) emits ONE theorem for the span-marked P with the
    /// user's verbatim tactic as closer — `emit_with_closer` NEVER
    /// hoists, so the mirror closes the obligation under
    /// `f + FUserCloser` — then pushes bare P as an `AssertFact` hyp
    /// for the continuation. Assert-SHAPED, not Assume-shaped (the
    /// endgame §A3 sketch predates the b77 E3 evidence): P is proven
    /// inline (kernel-checked at elaboration under the user's tactic),
    /// never assumed — census counts it proven-inline and it must not
    /// trip assume-warnings. Fields mirror `Assert`: annotated P
    /// obligation, hyp NAME leaf, bare P leaf. The
    /// PROOF-BLOCK kind (`proof { tac }`) has NO mirror node: it emits
    /// no theorem and pushes no hyp — the tactic rides the emitter's
    /// closer prefix AFTER the hoist decision (closers are not
    /// stage-A-certified), and the fn-level `closer_is_default` DFS
    /// already routes such fns to wrap mode.
    AssertQueryTactus(RawExp, u64, u64),
    /// StmX-less (bootstrap-77 / A5): production's `walk_let` FORK of a
    /// spine-position value-if whose POSITIVE condition is an IsVariant
    /// discriminator that N2 (`branch_ctor_frames`) upgrades to
    /// constructor form — field binders + the equation
    /// `scrut(.deref…) = Dt.Variant f0 f1 …` (CtorEq) replace the plain
    /// cond hyp on the then-side; the else-side keeps the plain
    /// `¬cond`. Plain-cond forks need NO new vocabulary (they are
    /// `StmData::If` with per-branch `Seq(assigns…, Ret(…))` bodies —
    /// production duplicates the continuation per branch and so does
    /// the serializer). NOT a `Match` node: production has no Match
    /// either — the construct is "If with a ctor-upgraded branch
    /// hypothesis", and N2 applies to hand-written `if t.is_leaf()`
    /// tests too. The upgrade only exists in DEFAULT-closer scopes
    /// (the N2 gate), so `IfCtor` never carries wrap-mode goals.
    IfCtor {
        /// N2 field binders `(interned id, typ leaf)` in declaration
        /// order — `tmp___val0 : Int` etc.
        pos_binders: Box<BinderList>,
        /// The ctor-equation hyp: `_h_hoist_i` name leaf, annotated
        /// `scrut = Dt.Variant fs` prop leaf, poison bit.
        eq_name: u64,
        eq_prop: u64,
        /// The else-branch hyp: `_h_hoist_i` name leaf, annotated
        /// `¬cond` prop leaf (plain discriminator — negative tests
        /// never upgrade), poison bit.
        neg_name: u64,
        neg_prop: u64,
        thn: Box<StmData>,
        els: Box<StmData>,
    },
    /// Empty StmX::Block.
    Skip,
    /// StmX::Block, right-nested pairwise — avoids the StmData/StmList
    /// mutual-recursion cycle and matches WP composition:
    /// wp(s1; s2, post) = wp(s1, wp(s2, post)).
    Seq(Box<StmData>, Box<StmData>),
}

// ── W6b: expression mirror (stage B — cast-class deep leaves) ────────
// The hybrid-leaf expression vocabulary the W6a probe froze
// (probe-w0/probe12_w6a_castleaf). Stage-A leaves are opaque interned u64s;
// stage B additively deepens obligation leaves into a structural expression
// tree whose cast/coercion decisions the reference renderer RE-DERIVES from
// the raw SST's type tags (implementation diversity D2). Datatype discipline
// unchanged: OWN types only, no Seq/Map, one-way nesting (GoalData →
// ExprData; RawExp → RawExp; ExprData → ExprData — none mutual), every
// recursive worker `structural_decreases`.

/// Minimal type mirror. The cast decision needs only `Int` (a uN, renders
/// Lean `Int`) vs `Nat`; `Bool` types comparisons/`Eq` (NOT arith-coercion
/// sites); `Named`/`Ref` cover user datatypes and `&`-params (the `.deref`
/// class). Non-recursive (`TyRef` carries the pointee's interned id, not a
/// TypData) — so `typ_size` needs no `structural_decreases`.
///
/// Variant names are `Ty`-prefixed: the tactus Lean backend renders a
/// nullary constructor as `(Name : TypData)`, so bare `Int`/`Nat`/`Bool`
/// would resolve to Lean's builtin types instead of these constructors
/// ("type expected, got (Nat : TypData)"). The prefix avoids the collision.
pub enum TypData {
    TyInt,
    TyNat,
    TyBool,
    TyNamed(u64),
    TyRef(u64),
    // W7: a `Box<T>` datatype field type (`Node (val0 : Tactus.Box lib.Tree)`),
    // kept DISTINCT from `TyRef` (`&T` borrow). Box (owned heap) and Ref deref
    // identically but are semantically distinct — conflating them would let a
    // Box/Ref field swap pass the bridge (W7a §7 Q4 verdict). Carries the
    // pointee's interned id, non-recursive (like TyRef).
    TyBox(u64),
}

/// Which materialized cast a `Cast` node denotes.
pub enum CastKind {
    IntToNat,   // `Int.toNat` (the materialized `as nat`)
    NatToInt,   // `Int.ofNat` (the reverse; present for completeness)
}

/// The HYBRID leaf. Structural cast/binop/app/fieldproj/span decisions are
/// mirrored; terminal atoms (var reads, spec-fn/type names) stay interned
/// `u64`. Atoms CARRY their id so a forgotten cast (`Atom 1` vs
/// `Cast IntToNat (Atom 1)`) is a shape difference the bridge catches (the
/// §2.1 safety condition).
pub enum ExprData {
    Atom(u64),                              // var read / spec-fn or type name
    Lit(int),                               // integer literal
    // G1: bool literal (`True`/`False`) in a leaf. Payload is the nat
    // encoding (0 = false, 1 = true), NOT a `bool`: the tactus Lean backend
    // renders a spec `bool` as `Prop`, whose equality needs
    // `Classical.propDecidable` and sticks `decide` — the whole crate encodes
    // such tags as `nat` for exactly this reason.
    LitBool(nat),
    Cast(CastKind, Box<ExprData>),          // Int.toNat / Int.ofNat node
    BinOp(u64, Box<ExprData>, Box<ExprData>),
    App(u64, Box<ExprData>),                // lib.tri (…), lib.tree_head (…)
    FieldProj(Box<ExprData>, u64),          // `.deref`, `.x`, `.1`, …
    SpanMark(u64, Box<ExprData>),           // `/- @rust:loc -/ <e>` wrapper
    // G4: goal-side let-binding `let <name> := <value>; <body>` — the If-fold
    // in max_u64's ensures leaf (`let r := let m := y; m; r ≥ x ∧ r ≥ y`).
    // Structural; `name` is the interned binder id (matches the reference
    // side's `RawExp::Let` name so the two agree by construction).
    Let(u64, Box<ExprData>, Box<ExprData>),
    // G4: unary logical negation `¬ e` — max_u64's `¬(x < y)` branch guard.
    Not(Box<ExprData>),
    // ── W7 body constructors (frozen by probe15_w7a_defs; the mutual cycle +
    //    eq/size idioms validated in-crate by probe_mutual2) ──
    // First-class `if c then t else e`. W6 G4 folded goal-side If→Let, but a
    // spec-fn BODY needs the raw if (e.g. `tri(n) = if n=0 then 0 else …`).
    Ite(Box<ExprData>, Box<ExprData>, Box<ExprData>),
    // `match scrut with <arms>` — inductive spec fns are match-bodied. Arms are
    // INLINED into `ArmList::Cons` (the `BinderList::Cons` idiom), NOT a
    // single-variant `MatchArm` enum: such an enum lowers to a Lean `structure`
    // whose auto-generated `.height` mis-names the ctor (`Arm.Arm` vs `Arm.mk`)
    // → `Invalid pattern`. `ExprData ↔ ArmList` is the one W7 datatype cycle.
    Match(Box<ExprData>, Box<ArmList>),
    // Multi-arg application `f a b c` (W6 `App` was single-arg). Args in a
    // dedicated `ExprList` (the second mutual cycle `ExprData ↔ ExprList`).
    AppN(u64, Box<ExprList>),
    // A7 (bootstrap-80 F3): the `Tactus.Ref.mk e` / `Tactus.Box.mk e`
    // WRAPPER constructions production's `coerce_lexpr` inserts when a
    // bare-typed value flows into a wrapper-typed slot (vec_push7's
    // `view (Tactus.Ref.mk v)`). First-class nodes, NOT `App` with an
    // interned fn-name leaf: the reference DERIVES these (reconcile_arg)
    // and cannot mint the per-cert interned id. Production's transcriber
    // (`lexpr_to_exprdata`) maps the same apps here, so the two sides
    // agree id-free.
    RefMk(Box<ExprData>),
    BoxMk(Box<ExprData>),
    // Quantifier nodes `∀/∃ (bid : bty), body`. `GoalData::All` is goal-level
    // only; a spec-fn body quantifier needs its own expression node.
    Forall(u64, TypData, Box<ExprData>),
    Exists(u64, TypData, Box<ExprData>),
}

// W7: match arms, INLINED (ctor id, bound-var ids, arm body, tail). Mutually
// recursive with `ExprData` via the boxed body. No separate `MatchArm` type
// (see the `Match` variant comment). Cf. `BinderList::Cons(u64,u64,Box<..>)`.
pub enum ArmList {
    Nil,
    Cons(u64, BinderIdList, Box<ExprData>, Box<ArmList>),
}

// W7: the multi-arg `AppN` argument list. Mutually recursive with `ExprData`.
pub enum ExprList {
    Nil,
    Cons(Box<ExprData>, Box<ExprList>),
}

/// The NEW independent input: the raw SST expression tree, mirrored to data
/// and type-annotated. NOT rendered through production's `to_lean_sst_expr`
/// — that independence is what gives the bridge its diversity. (W6c will
/// transcribe `vir::sst::ExpX` into this; the type tags read off the SST's
/// per-node `typ`.)
pub enum RawExp {
    Var(u64, TypData),                              // typed variable read
    Lit(int, TypData),
    LitBool(nat),                                   // G1: source bool literal (0/1 nat encoding)
    Clip(TypData, Box<RawExp>),                     // explicit `as` cast (Verus Clip)
    BinOp(u64, TypData, Box<RawExp>, Box<RawExp>),  // 2nd slot = op RESULT type
    Call(u64, TypData, Box<RawExp>, TypData),       // fn, ret ty, arg, arg ty
    // G3: struct/tuple field projection — (field id, field RESULT type, base).
    // The field id is interned by the serializer to match production's accessor
    // text (`deref_field()=0` reserved; `.x` interns "x"; tuple `.1` interns
    // the SHIFTED name production renders).
    Field(u64, TypData, Box<RawExp>),
    // G6: an unsigned-overflow `HasType(U(n))` refinement. `render_exp`
    // reproduces production's `type_bound_predicate` expansion
    // `0 ≤ e ∧ e < 2^n` (option (i), Danielle 2026-07-14); the width `n` stays
    // observable and `2^n` is re-derived via `pow2` (independent of
    // production's `two_pow_lit`). Signed/USize/Char/vacuous ranges are NOT
    // carried — the serializer fails loud on them (none appear in the fixture).
    HasType(u64, Box<RawExp>),
    Deref(Box<RawExp>),                             // `*t` on a `&`-param (dead for the serializer; see G2)
    // G4: let-binding + negation mirrors (the max_u64 If-fold). `Let` carries
    // the interned binder id; `render_exp` maps both STRAIGHT THROUGH —
    // structural, with no coercion at this node (any Int→Nat coercion lives in
    // the sub-expressions, materialized at their own BinOp/Call/Clip nodes).
    Let(u64, Box<RawExp>, Box<RawExp>),
    Not(Box<RawExp>),
    Span(u64, Box<RawExp>),
    // ── W7 body constructors (raw side). `ite`/`matchR`/`callN` carry the
    //    branch / arm-body / value RESULT type so `render_exp` can materialize
    //    the `as nat` coercion there (parallel to `BinOp`'s result-type slot).
    //    No `HasType` addition — the unsigned-overflow refinement is an
    //    obligation-goal construct, already present, not a body construct. ──
    Ite(TypData, Box<RawExp>, Box<RawExp>, Box<RawExp>),       // ty = branch result type
    MatchR(Box<RawExp>, Box<RawArmList>, TypData),            // scrut, arms, arm-body result ty
    CallN(u64, TypData, Box<RawList>),                        // fn, ret ty, args
    ForallR(u64, TypData, Box<RawExp>),
    ExistsR(u64, TypData, Box<RawExp>),
}

// W7: the raw (VIR-transcribed) match-arm list, mirroring `ArmList` with a
// `RawExp` body. Inlined arm fields (ctor, binds, body, tail).
pub enum RawArmList {
    Nil,
    Cons(u64, BinderIdList, Box<RawExp>, Box<RawArmList>),
}

// W7: the raw multi-arg argument list, mirroring `ExprList`.
// A7 (bootstrap-80 F3): each element pairs the arg with the callee's
// EXPECTED param typ (instantiated at the call site's typ args,
// transcribed from the same fn_map production's `fn_param_typs`
// consults; the serializer's fallback for an unknown signature is the
// arg's own typ, mirroring production's `into_slot(&a.typ)`). This is
// what lets `render_exp` DERIVE the per-arg slot coercions
// (`reconcile_arg`) reference-side instead of trusting a mark.
pub enum RawList {
    Nil,
    Cons(Box<RawExp>, TypData, Box<RawList>),
}

// ── W7 def-header layer: the DEFINITIONS the obligations are stated in
//    terms of — `@[reducible] def` spec-fn bodies + `inductive` datatype
//    decls (trust-inventory row 4). `render_def` is an INDEPENDENT second
//    lowering (VIR-body → Lean-def), NOT production's renderer — that
//    diversity is what gives the bridge teeth (DESIGN-W7-defslayer §2). ──

// (param id, param TYPE, tail) — like BinderList but the 2nd slot is a TypData
// (a wrong param type is a real, certifiable bug; W7a §7 Q4). Self-recursive.
pub enum ParamList {
    Nil,
    Cons(u64, TypData, Box<ParamList>),
}

// positional field types of one datatype constructor (no accessor names — the
// accessor surface is separately certifiable; W7a §7 Q4).
pub enum TypList {
    Nil,
    Cons(TypData, Box<TypList>),
}

// one `inductive` ctor INLINED (name, positional field types, tail) — no
// separate `CtorData` type (same single-variant-struct avoidance as ArmList).
pub enum CtorList {
    Nil,
    Cons(u64, TypList, Box<CtorList>),
}

// `@[reducible] def <name> <params> : <ret> := <body>` — production-style and
// raw (VIR-transcribed) headers around a body ExprData / RawExp. Structs (one
// ctor): spec field access is a projection, no tag+idiom needed (cf. FnCtxData).
pub struct DefData {
    pub name: u64,
    pub params: ParamList,
    pub ret: TypData,
    pub body: ExprData,
}
pub struct RawDef {
    pub name: u64,
    pub params: ParamList,
    pub ret: TypData,
    pub body: RawExp,
}

// `inductive <name> where <ctors>`. Datatype render is TRANSCRIPTION not
// decision (no body to lower); the bridge teeth are the VIR-vs-LExpr
// transcription diversity, abstracted as two inputs (a wrong-transcribed field
// type / ctor is the kill). RawDt/DtData share the ctor shape.
pub struct DtData {
    pub name: u64,
    pub ctors: CtorList,
}
pub struct RawDt {
    pub name: u64,
    pub ctors: CtorList,
}

// ── W6d.1b-ii: lists of DEEP obligations (Call.reqs / Ret.es) ────────
// A DEDICATED list, NOT a polymorphic `LeafList`: `LeafList` is still
// shared by `enss` and `hyps_of_leaves`, where the element MUST stay an
// opaque `u64` (hypotheses are not deepened). Keeping the deep list a
// distinct type also keeps the two element worlds unmergeable — a
// `LeafE(render_exp …)` can never silently match a stage-A `Leaf(u64)`
// (the `goal_eq` safety condition; Danielle 2026-07-14). The element is
// `Box<RawExp>`, mirroring `GoalList::Cons(Box<GoalData>, …)` (compound
// elements are boxed; only primitive-element lists like `LeafList` /
// `BinderList` inline the head). `close_each_e` maps `close_e` over it.
pub enum RawExpList {
    Nil,
    Cons(Box<RawExp>, Box<RawExpList>),
}

// ── Goals: the refWp output shape ───────────────────────────────────

pub enum GoalData {
    /// A rendered obligation leaf (stage-A opaque interned id).
    Leaf(u64),
    /// hypothesis leaf → goal.
    Imp(u64, Box<GoalData>),
    /// (binder id, typ leaf, body) — ∀-introduction.
    All(u64, u64, Box<GoalData>),
    /// (binder id, value leaf, body) — let-binding.
    Let(u64, u64, Box<GoalData>),
    /// W6b (stage B): a DEEP obligation leaf carrying the rendered `ExprData`
    /// tree instead of an opaque u64. Additive — refWp does NOT yet emit this
    /// (`close` still produces `Leaf(u64)`); W6c wires the serializer to
    /// transcribe raw SST exprs and emit `LeafE`. The `goal_eq` bridge already
    /// compares two `LeafE`s structurally via `expr_eq`.
    LeafE(ExprData),
}

/// One-way nesting (GoalList → GoalData, never back): plain recursion.
pub enum GoalList {
    Nil,
    Cons(Box<GoalData>, Box<GoalList>),
}

// ── The refWp context frame (the ONE ordered goal spine) ────────────
// `CtxFrame` is a SINGLE ordered entry list, NOT three parallel lists:
// the production telescope interleaves binders, hypotheses, and lets
// (`∀ x, h → let y := e; h2 → …`) and three separate lists cannot
// reproduce the interleave order (DESIGN-W2-refwp.md §2.1 review fix).
// wpStm folds this frame entry-by-entry around each obligation leaf.

pub enum FrameList {
    FNil,
    /// (binder id, typ leaf, tail) — ∀-binder in the spine.
    FBind(u64, u64, Box<FrameList>),
    /// (name leaf, hyp leaf, tail) — an implication
    /// hypothesis in the spine. The NAME is rendering payload for
    /// N1-hoist mode (production emits hyps as named theorem binders
    /// `(_h_hoist_i : P)`, bootstrap-74); wrap-mode rendering (`Imp`)
    /// and the semantic layer ignore it. Sites without a
    /// serializer-supplied name carry 0 (never rendered in wrap mode).
    /// POISON (bootstrap-74 slice 2 → F4, bootstrap-80 stage 2): a prop
    /// whose text mentions a residue-let (`FLetR`) name forces the WHOLE
    /// goal to wrap (production's `hoist_all` bail). The mark is DERIVED
    /// reference-side — `has_poisoned_hyp` membership-checks the prop id
    /// against `poisoned_props(c)`; there is NO carried bit (era-2
    /// deletion: the serializer's bit slot is gone, the
    /// `FnCtxData.prop_deeps` side table is the only channel).
    FHyp(u64, u64, Box<FrameList>),
    /// (binder id, value leaf, tail) — a let-binding in the spine.
    /// Post-N1 (bootstrap-74): a PLAIN FLet marks a NON-hoistable let
    /// (typ-less — production's hoist_all None case — or a hoistable
    /// let poisoned by a residue mention, collapsed losslessly); its
    /// presence in a frame list is one half of the wrap-mode gate.
    FLet(u64, u64, Box<FrameList>),
    /// (binder id, typ leaf, value leaf, eq-name leaf, eq-prop leaf,
    /// tail) — a HOISTABLE let (bootstrap-74 N1 mirror). In hoist mode
    /// it renders as the production binder pair `(x : T)
    /// (_h_x_hoist1 : x = v)` = `All(x, typ) ∘ All(eq_name, eq_prop)`;
    /// in wrap mode (a plain FLet somewhere in the list) it renders
    /// `Let(x, v)` exactly like FLet. The typ/eq leaves are serializer
    /// renderings (production's exact texts, interned).
    FLetH(u64, u64, u64, u64, u64, Box<FrameList>),
    /// (binder id, value leaf, tail) — a RESIDUE let (bootstrap-74
    /// slice 2): a BOOL-typed let (an if-condition temp). Production
    /// keeps Bool lets in GOAL POSITION while the other frames hoist —
    /// hoisting them as propositional equations loops simp. In hoist
    /// mode an FLetR is SKIPPED by the binder telescope and folded as a
    /// goal-position `Let(x, v)` around the leaf (frame order: earliest
    /// residue outermost); in wrap mode it renders `Let(x, v)` exactly
    /// like FLet. It NEVER forces wrap mode by itself — but an `FHyp`
    /// whose prop mentions its name is poisoned, which does.
    FLetR(u64, u64, Box<FrameList>),
    /// NON-DEFAULT-CLOSER marker (R1, bootstrap-77): production's
    /// per-obligation closer class lives in `OblCtx` next to the frames;
    /// the mirror carries it as a frame entry. Renders NOTHING and has
    /// no semantic content — its only effect is tripping `gate_wrap`
    /// (production's `emit_split` hoists only default-closer obligations;
    /// `emit_with_closer` never hoists). Seeded per-fn when
    /// `FnCtxData.closer_default == 0` (a fn-level `tactus_tactic` attr
    /// or a proof-block prefix — `closer_is_default`'s DFS), appended
    /// per-goal for the always-wrapped assert-by theorem
    /// (`AssertQueryTactus`), and STRIPPED by `strip_hyps` — production's
    /// `OblCtx::new_scope` drops hyps AND resets the closer at the same
    /// point, so an NL query scope inside a user-closer fn hoists again.
    FUserCloser(Box<FrameList>),
}

pub type CtxFrame = FrameList;

// ── The refWp seed context (per-fn signature data) ──────────────────
// Not recursive: holds other datatypes by value. `typ_params` reuses
// BinderList with the kind leaf in the second slot; instance binders
// (`[Nonempty A]`) ride as ordinary entries with distinguished kind
// leaves. `param_bounds` is parallel to `params`.

pub struct FnCtxData {
    pub typ_params: BinderList,
    pub params: BinderList,
    pub param_bounds: ParamBoundList,
    // `reqs`: (h_req<i> name leaf, req-prop leaf) pairs. Production renders
    // each requires as a NAMED ∀-binder `∀ (h_req0 : x < 1000)` (finding-2),
    // so `reqs` is a `BinderList` (name, prop) — folded via binders_to_frame
    // into `FBind` spine entries, not anonymous `FHyp`s.
    pub reqs: BinderList,
    // `&mut`-param preamble entries (bootstrap-78 S2, see `MutParamList`):
    // `seed_frame` derives the two fn-entry FLets per entry AFTER the req
    // binders (production's frame order — the reqs are theorem-level base
    // binders; the preamble lets are the first OblCtx frames).
    pub mut_params: MutParamList,
    pub enss: LeafList,
    // F4 (bootstrap-80 stage 2): the poison-derivation inputs.
    // `residue_names` = interned NAME ids of the residue (FLetR / Bool)
    // lets, in walk order. GLOBAL and monotonic, mirroring production's
    // `residue_names` vec — production's branch state save excludes it,
    // so a frame-prefix derivation would NOT be faithful (b80 card,
    // design-review addendum). `prop_deeps` = the side table above.
    // `ref_wp` derives the poison set ONCE (`poisoned_props`) and the
    // wrap gate / FLetH collapse read it as a membership check.
    pub residue_names: LeafList,
    pub prop_deeps: PropDeepList,
    // R1 (bootstrap-77): the fn-level closer class — 1 = default
    // (`tactus_auto`), 0 = user. AMENDED post-landing (proof_block_fn
    // evidence, b77 card): this is the ATTR bit ONLY — a fn-level
    // `tactus_tactic` sets `obl.closer` for every goal (they all wrap).
    // A proof-block PREFIX does NOT touch `obl.closer` (it composes
    // into the tactic AFTER the hoist decision), so a prefix-only fn
    // seeds 1 here and its goals hoist normally; the prefix flips only
    // the RETURN ROUTE (a serializer-side decision, not frame state).
    // `seed_frame` plants a `FUserCloser` marker when 0, so every goal
    // of the fn renders in wrap mode (the A2 wrap_mode collapse,
    // now modeled as frame state instead of lying about let classes).
    pub closer_default: u64,
}

// ── Skeleton spec fns (all structural, all kernel-computable) ───────

#[verifier::structural_decreases]
pub open spec fn leaf_len(l: LeafList) -> nat
    decreases l
{
    match l {
        LeafList::Nil => 0,
        LeafList::Cons(_h, t) => 1 + leaf_len(*t),
    }
}

// W6d.1b-ii: the deep analogue of `leaf_len` for `RawExpList` (the
// Call.reqs / Ret.es obligation slots).
#[verifier::structural_decreases]
pub open spec fn raw_exp_list_len(l: RawExpList) -> nat
    decreases l
{
    match l {
        RawExpList::Nil => 0,
        RawExpList::Cons(_h, t) => 1 + raw_exp_list_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn binder_len(b: BinderList) -> nat
    decreases b
{
    match b {
        BinderList::Nil => 0,
        BinderList::Cons(_id, _typ, t) => 1 + binder_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn param_bound_len(p: ParamBoundList) -> nat
    decreases p
{
    match p {
        ParamBoundList::Nil => 0,
        ParamBoundList::NoBound(t) => 1 + param_bound_len(*t),
        ParamBoundList::Bound(_name, _prop, t) => 1 + param_bound_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn frame_len(f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_id, _typ, t) => 1 + frame_len(*t),
        FrameList::FHyp(_hn, _h, t) => 1 + frame_len(*t),
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => 1 + frame_len(*t),
        FrameList::FLet(_id, _v, t) => 1 + frame_len(*t),
        FrameList::FLetR(_id, _v, t) => 1 + frame_len(*t),
        FrameList::FUserCloser(t) => 1 + frame_len(*t),
    }
}

#[verifier::structural_decreases]
pub open spec fn stm_size(s: StmData) -> nat
    decreases s
{
    match s {
        StmData::Assert(_o, _hn, _h) => 1,
        StmData::Assume(_hn, _e) => 1,
        StmData::Assign(_d, _r) => 1,
        StmData::AssignH(_x, _ty, _v, _en, _ep) => 1,
        StmData::AssignR(_x, _v) => 1,
        // 1 + |reqs| (a RawExpList) + frame_len(post) (the FrameList delta) —
        // mirrors the serializer's `stm_size_of` token count: stmt heads +
        // RawExpList `Cons` (reqs) + FrameList `FBind`/`FHyp`/`FLet` (post).
        StmData::Call { reqs, post } => 1 + raw_exp_list_len(*reqs) + frame_len(*post),
        StmData::DeadEnd(b) => 1 + stm_size(*b),
        StmData::AssertQueryNl(b, _tq) => 1 + stm_size(*b),
        StmData::AssertQueryTactus(_o, _hn, _h) => 1,
        StmData::Ret(es, _rb) => 1 + raw_exp_list_len(*es),
        StmData::If(_c, _cn, _nc, _ncn, t, e) => 1 + stm_size(*t) + stm_size(*e),
        // Mirrors the serializer token count: head + pos-binder Cons + bodies.
        StmData::IfCtor { pos_binders, eq_name: _, eq_prop: _, neg_name: _, neg_prop: _, thn, els } =>
            1 + binder_len(*pos_binders) + stm_size(*thn) + stm_size(*els),
        StmData::Loop { inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds: _, cond_name: _, cond_ann: _, neg_cond_ann: _, neg_neg_cond_ann: _, break_guard_ann: _, break_use_ann: _, d_old_name: _, d_old_ty: _, d_old_val: _, d_old_eq_name: _, d_old_eq_prop: _, decrease_oblig: _, setup, body } =>
            // Mirrors the serializer's `stm_size_of` token count, which sums
            // stmt heads + LeafList/BinderList/RawExpList `Cons` — `inv_hyps`
            // and `binders` are BinderLists (counted); `inv_obligs`,
            // `inv_obligs_exit` and `inv_obligs_break` are the parallel
            // DEEP-obligation RawExpLists (counted, W6d.1b-iii);
            // `binder_bounds` is a ParamBoundList (NOT counted, same as
            // FnCtxData's); the scalar leaves add 0; `setup` is an ordinary
            // StmData (counted, bootstrap-79).
            1 + binder_len(*inv_hyps) + raw_exp_list_len(*inv_obligs) + raw_exp_list_len(*inv_obligs_exit) + raw_exp_list_len(*inv_obligs_break) + binder_len(*binders) + stm_size(*setup) + stm_size(*body),
        StmData::Skip => 1,
        StmData::Seq(a, b) => 1 + stm_size(*a) + stm_size(*b),
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_size(g: GoalData) -> nat
    decreases g
{
    match g {
        GoalData::Leaf(_e) => 1,
        GoalData::Imp(_h, b) => 1 + goal_size(*b),
        GoalData::All(_x, _t, b) => 1 + goal_size(*b),
        GoalData::Let(_x, _v, b) => 1 + goal_size(*b),
        // A deep leaf is still ONE spine node (like `Leaf`); its expression
        // depth is measured by `expr_size`, not folded into the goal spine.
        GoalData::LeafE(_e) => 1,
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_count(gs: GoalList) -> nat
    decreases gs
{
    match gs {
        GoalList::Nil => 0,
        GoalList::Cons(_g, t) => 1 + goal_count(*t),
    }
}

/// Value-param arity of a context (non-recursive projection).
pub open spec fn fnctx_arity(c: FnCtxData) -> nat {
    binder_len(c.params)
}

// ── W6b: expression measures, reference renderer, structural eq ─────
// The stage-B counterparts of the skeleton size fns + the goal_eq family,
// on the expression vocabulary. All structural / kernel-computable.

// Structural size of an expression (spine node count).
#[verifier::structural_decreases]
pub open spec fn expr_size(e: ExprData) -> nat
    decreases e
{
    match e {
        ExprData::Atom(_) => 1,
        ExprData::Lit(_) => 1,
        ExprData::LitBool(_) => 1,
        ExprData::Cast(_k, t) => 1 + expr_size(*t),
        ExprData::BinOp(_op, l, r) => 1 + expr_size(*l) + expr_size(*r),
        ExprData::App(_fn, a) => 1 + expr_size(*a),
        ExprData::FieldProj(t, _f) => 1 + expr_size(*t),
        ExprData::SpanMark(_loc, t) => 1 + expr_size(*t),
        ExprData::Let(_n, v, bd) => 1 + expr_size(*v) + expr_size(*bd),
        ExprData::Not(t) => 1 + expr_size(*t),
        // W7 body constructors. `Match`/`AppN` recurse through the arm/expr
        // list measures (the mutual group); binder ids are leaves (not sized).
        ExprData::Ite(c, t, e) => 1 + expr_size(*c) + expr_size(*t) + expr_size(*e),
        ExprData::Match(s, arms) => 1 + expr_size(*s) + arms_size(*arms),
        ExprData::AppN(_fn, args) => 1 + exprlist_size(*args),
        ExprData::Forall(_bid, _bty, body) => 1 + expr_size(*body),
        ExprData::Exists(_bid, _bty, body) => 1 + expr_size(*body),
        ExprData::RefMk(t) => 1 + expr_size(*t),
        ExprData::BoxMk(t) => 1 + expr_size(*t),
    }
}

// W7: the arm-list / expr-list spine measures, MUTUALLY recursive with
// `expr_size` (validated in-crate by probe_mutual2 — Verus accepts mutual
// `structural_decreases` across the `ExprData ↔ ArmList`/`ExprList` cycles;
// the emitted `termination_by structural` kernel-reduces under `decide`).
#[verifier::structural_decreases]
pub open spec fn arms_size(a: ArmList) -> nat
    decreases a
{
    match a {
        ArmList::Nil => 0,
        ArmList::Cons(_c, _bs, body, tl) => 1 + expr_size(*body) + arms_size(*tl),
    }
}

#[verifier::structural_decreases]
pub open spec fn exprlist_size(l: ExprList) -> nat
    decreases l
{
    match l {
        ExprList::Nil => 0,
        ExprList::Cons(h, t) => 1 + expr_size(*h) + exprlist_size(*t),
    }
}

// W7: length of a binder-id list (leaf list; self-recursive, no mutual group).
#[verifier::structural_decreases]
pub open spec fn binder_id_list_len(b: BinderIdList) -> nat
    decreases b
{
    match b {
        BinderIdList::Nil => 0,
        BinderIdList::Cons(_id, t) => 1 + binder_id_list_len(*t),
    }
}

// Structural size of a type mirror. Non-recursive (every TypData is flat) —
// no `structural_decreases`; the match documents the variant set.
pub open spec fn typ_size(t: TypData) -> nat {
    match t {
        TypData::TyInt => 1,
        TypData::TyNat => 1,
        TypData::TyBool => 1,
        TypData::TyNamed(_) => 1,
        TypData::TyRef(_) => 1,
        TypData::TyBox(_) => 1,
    }
}

// TypData tag (kernel-computable discriminant; the cast decision reads it).
pub open spec fn td_tag(t: TypData) -> nat {
    match t {
        TypData::TyInt => 0,
        TypData::TyNat => 1,
        TypData::TyBool => 2,
        TypData::TyNamed(_) => 3,
        TypData::TyRef(_) => 4,
        TypData::TyBox(_) => 5,
    }
}

// The type a `Deref` presents to its parent: `&T` (Ref inner) becomes the
// pointee `Named inner`; every other type derefs to itself. Factored into a
// top-level fn (NOT a match nested inside `type_of`'s Deref arm) per the
// decide-checker flattening caveat (see `ret_frame`). Explicit arms, no
// wildcard.
pub open spec fn deref_type(t: TypData) -> TypData {
    match t {
        TypData::TyRef(inner) => TypData::TyNamed(inner),
        // W7: `Box<T>` derefs to its pointee `T`, same as `&T` (semantically
        // distinct owner vs borrow, but identical deref presentation).
        TypData::TyBox(inner) => TypData::TyNamed(inner),
        TypData::TyInt => TypData::TyInt,
        TypData::TyNat => TypData::TyNat,
        TypData::TyBool => TypData::TyBool,
        TypData::TyNamed(n) => TypData::TyNamed(n),
    }
}

// W7: the interned id a type carries (0 for the nullary types). Paired with
// `td_tag` for structural type equality — `TyBox(5)` vs `TyRef(5)` differ by
// tag (5 vs 4), `TyNamed(5)` vs `TyNamed(7)` differ by id.
pub open spec fn td_id(t: TypData) -> u64 {
    match t {
        TypData::TyNamed(n) => n,
        TypData::TyRef(n) => n,
        TypData::TyBox(n) => n,
        _ => 0,
    }
}

// W7: nat-returning type equality (the `Forall`/`Exists` binder-type compare
// + the def-header layer). Tag + carried-id, no recursion (TypData is flat).
pub open spec fn typ_eq(a: TypData, b: TypData) -> nat {
    if td_tag(a) == td_tag(b) {
        if td_id(a) == td_id(b) { 1 } else { 0 }
    } else { 0 }
}

// The rendered type a raw node presents to its parent. Crucially a
// `Clip target` presents `target` (not its operand's type) — that is how an
// elided-clip operand still reads `Int` to the enclosing op and a
// materialized one reads `Nat`.
#[verifier::structural_decreases]
pub open spec fn type_of(re: RawExp) -> TypData
    decreases re
{
    match re {
        RawExp::Var(_id, ty) => ty,
        RawExp::Lit(_v, ty) => ty,
        RawExp::LitBool(_b) => TypData::TyBool,
        RawExp::Clip(target, _e) => target,
        RawExp::BinOp(_op, ty, _l, _r) => ty,
        RawExp::Call(_fn, ret, _arg, _argty) => ret,
        RawExp::Field(_fid, fty, _base) => fty,
        // The refinement is a proposition (`0 ≤ e ∧ e < 2^n`) → Bool.
        RawExp::HasType(_n, _inner) => TypData::TyBool,
        RawExp::Deref(e) => deref_type(type_of(*e)),
        // G4: a `let`'s type is its body's; `¬ e` is a proposition (Bool).
        RawExp::Let(_name, _val, body) => type_of(*body),
        RawExp::Not(_e) => TypData::TyBool,
        RawExp::Span(_loc, e) => type_of(*e),
        // W7: `ite`/`matchR`/`callN` present their carried result type in one
        // step (no recursion into arms/branches); quantifiers are propositions.
        RawExp::Ite(ty, _c, _t, _e) => ty,
        RawExp::MatchR(_scrut, _arms, ty) => ty,
        RawExp::CallN(_fn, ret, _args) => ret,
        RawExp::ForallR(_bid, _bty, _body) => TypData::TyBool,
        RawExp::ExistsR(_bid, _bty, _body) => TypData::TyBool,
    }
}

// The coercion PREDICATE: an operand that renders `Int` under an op/target
// that renders `Nat` needs the `Int.toNat` the `as nat` denotes. Returns nat
// (1/0) — a bool-returning spec fn lowers to a noncomputable Prop on which
// `decide` sticks (finding-5).
pub open spec fn needs_nat_coercion(operand: TypData, op_result: TypData) -> nat {
    if td_tag(operand) == 0 && td_tag(op_result) == 1 { 1 } else { 0 }
}

// Wrap `e` in an `Int.toNat` cast iff the predicate fired.
pub open spec fn coerce_if(b: nat, e: ExprData) -> ExprData {
    if b == 1 { ExprData::Cast(CastKind::IntToNat, Box::new(e)) } else { e }
}

// The interned field id for a `.deref` (the `&`-param dereference field).
pub open spec fn deref_field() -> u64 { 0 }

// G2: a spec-fn Call arg whose mirror type is `TyRef(T)` gets a `.deref`
// coercion. Spec fns never take `&T`, so the `TyRef` tag on the arg is the
// entire signal — no callee param type needed (W6d.0 dump confirmed the arg
// stays `&T`, the `*t` in spec being transparent). Parallel to
// needs_nat_coercion; nat-returning for the same `decide`-friendliness reason.
pub open spec fn needs_ref_deref(operand: TypData) -> nat {
    if td_tag(operand) == 4 { 1 } else { 0 }
}

// Wrap `e` in a `.deref` FieldProj iff the predicate fired (mirrors coerce_if).
pub open spec fn deref_if(b: nat, e: ExprData) -> ExprData {
    if b == 1 { ExprData::FieldProj(Box::new(e), deref_field()) } else { e }
}

// A7 (bootstrap-80 F3/A1): the per-arg slot reconciliation — the TypData
// fragment of production's `coerce_lexpr` two-phase decision
// (`expr_shared.rs:1101`), DERIVED reference-side from the (actual,
// expected) typ pair the call node carries. Phase 1 (numeric sort
// bridge, both types bare): Int↔Nat → the `Int.toNat`/`Int.ofNat` cast.
// Phase 2 (wrapper reconciliation, depth ≤ 1): wrapper → bare peels
// (`.deref`), bare → wrapper wraps (`RefMk`/`BoxMk`), Ref↔Box at equal
// depth peels+rewraps, equal tags pass through (the vec_read view case:
// `View.view`'s param IS the ref type, so NO deref — the G2 bug).
// Non-recursive; kernel reduces under `decide`. Written as a TAG
// if-chain, NOT a nested match — the one-line Lean emission flattens a
// nested match's arms into the outer arm scope (the inner `_` swallows
// the remaining outer constructors → "redundant alternative"); the
// tag-comparison idiom is the house style for exactly this reason (cf.
// `deref_type`'s factoring note).
//
// Named blind spots (bridge-diverge LOUD, never silent-pass; card A1):
// a sort bridge UNDER a wrapper (TypData pointees are opaque leaf ids,
// so the reference cannot see the pointee's sort — production peels,
// bridges, rewraps) and MutRef-vs-Ref at equal depth (both erase to
// `TyRef`). Multi-layer wraps cannot arise (TypData is depth-bounded).
pub open spec fn reconcile_arg(actual: TypData, expected: TypData, e: ExprData) -> ExprData {
    let ta = td_tag(actual);
    let te = td_tag(expected);
    // Phase 1 — bare numeric sort bridge (both directions).
    if ta == 0 && te == 1 { ExprData::Cast(CastKind::IntToNat, Box::new(e)) }
    else if ta == 1 && te == 0 { ExprData::Cast(CastKind::NatToInt, Box::new(e)) }
    // Phase 2 — wrapper reconciliation.
    else if ta == 4 && te == 4 { e }                          // Ref → Ref: passthrough (vec_read)
    else if ta == 5 && te == 5 { e }                          // Box → Box: passthrough
    else if ta == 4 && te == 5 {
        ExprData::BoxMk(Box::new(ExprData::FieldProj(Box::new(e), deref_field())))
    }                                                          // Ref → Box: peel + rewrap
    else if ta == 5 && te == 4 {
        ExprData::RefMk(Box::new(ExprData::FieldProj(Box::new(e), deref_field())))
    }                                                          // Box → Ref: peel + rewrap
    else if ta == 4 || ta == 5 { ExprData::FieldProj(Box::new(e), deref_field()) }
    // wrapper → bare: peel (the G2 auto-deref, now driven by the pair)
    else if te == 4 { ExprData::RefMk(Box::new(e)) }           // bare → Ref: wrap (vec_push7)
    else if te == 5 { ExprData::BoxMk(Box::new(e)) }           // bare → Box: wrap
    else { e }
}

// G6: 2^n as an int — the upper bound of the unsigned-overflow refinement
// `0 ≤ e ∧ e < 2^n`. An INDEPENDENT re-derivation of production's
// `two_pow_str` (a divergence in either surfaces as a bridge mismatch rather
// than silently agreeing). A finite width→bound TABLE, not recursive
// doubling: a `decreases n` power lowers to `WellFounded.fix` (recursion on
// `n - 1` is not a structural `Nat` subterm), which the kernel does NOT reduce
// under `decide` — so the recursive form freezes `render_exp`. The if-chain
// over concrete widths reduces via `Nat.decEq`. Covers the fixed-width Verus
// integer widths (u8/u16/u32/u64/u128); other widths (incl. arch `usize`) hit
// the `0` sentinel, which never matches production's real bound → a loud
// bridge mismatch rather than a silent pass. The serializer fails loud on
// unsupported ranges before this is reached.
pub open spec fn pow2(n: nat) -> int {
    if n == 8 { 256 }
    else if n == 16 { 65536 }
    else if n == 32 { 4294967296 }
    else if n == 64 { 18446744073709551616 }
    // 2^128 exceeds the Rust literal parser (u128::MAX + 1); write it as an
    // exact spec-`int` product of two in-range 2^64 literals.
    else if n == 128 { (18446744073709551616 * 18446744073709551616) as int }
    else { 0 }
}

// `render_exp` reimplements the cast/coercion decision UNIFORMLY from the
// type tags, independently of production's renderer. Plainly structural (each
// call is on a subterm) so the kernel reduces it under `decide`/`rfl`.
#[verifier::structural_decreases]
pub open spec fn render_exp(re: RawExp) -> ExprData
    decreases re
{
    match re {
        RawExp::Var(id, _ty) => ExprData::Atom(id),
        RawExp::Lit(v, _ty) => ExprData::Lit(v),
        RawExp::LitBool(b) => ExprData::LitBool(b),   // G1: straight through
        // explicit `as` cast: materialize Int.toNat iff there is a real
        // Int→Nat gap between the operand and the clip target.
        RawExp::Clip(target, e) =>
            coerce_if(needs_nat_coercion(type_of(*e), target), render_exp(*e)),
        // nat-typed arith op: each Int-rendering operand is materialized (the
        // Friction-2 site). A bool-typed op (cmp/Eq) has
        // `needs_nat_coercion _ Bool = 0`, so operands are left as-is.
        RawExp::BinOp(op, ty, l, r) => {
            // B1 (bootstrap-48): reproduce production's structural-binop
            // min-balance (`to_lean_sst_expr.rs:1157-1161`) IN THE TCB. A
            // structural compare between a `&T` operand and a bare-`T` operand
            // (e.g. `result == self` in a `&self` clone's `_return = self`
            // postcondition, where the SST carries a bare `Var(self):&Self`)
            // peels the DEEPER operand DOWN to the shallower's ref-depth via
            // `.deref` field-projections. With TypData ref-depth bounded 0/1
            // (`TyRef inner`, inner never nested ref), `needs_ref_deref` IS that
            // depth (0/1) and the per-operand peel `dl - min(dl,dr)` is 1 iff
            // that operand is strictly deeper — i.e. `dl > dr` / `dr > dl` (the
            // 0/1 specialization of the monus; avoids nat subtraction so the
            // kernel reduces it under `decide`).
            //
            // Independence (the whole point of B1 vs B2): the reference derives
            // the peel from the TypData it reads, NOT from production's shared
            // `count_ref_decorations`. So the bridge now checks production's
            // deref-count against the reference's; any divergence — including a
            // >1 depth that production could peel but TypData cannot express —
            // fails the bridge LOUD (the TCB underpeels) rather than silently
            // agreeing. Fail-loud, never silent-pass.
            //
            // Non-interaction with nat-coercion: a ref operand is tag 4, and its
            // peel is `TyNamed` (tag 3); `needs_nat_coercion` fires only on tag 0
            // (`TyInt`), so it is 0 on a ref operand whether peeled or not. And
            // every op that can carry a ref operand is a structural comparison
            // (Bool result, tag 2) ⟹ `needs_nat_coercion(_, Bool) = 0` across the
            // entire ref-reachable region. The two coercions provably never
            // co-fire, so feeding the unpeeled `type_of` to `needs_nat_coercion`
            // is immaterial (simplest; matches the arm's prior shape).
            let dl = needs_ref_deref(type_of(*l));
            let dr = needs_ref_deref(type_of(*r));
            let l1 = deref_if(if dl > dr { 1 } else { 0 }, render_exp(*l));
            let r1 = deref_if(if dr > dl { 1 } else { 0 }, render_exp(*r));
            let l2 = coerce_if(needs_nat_coercion(type_of(*l), ty), l1);
            let r2 = coerce_if(needs_nat_coercion(type_of(*r), ty), r1);
            ExprData::BinOp(op, Box::new(l2), Box::new(r2))
        },
        // A7 (bootstrap-80 F3): per-arg slot reconciliation via
        // `reconcile_arg` — the carried `argty` is now the callee's
        // EXPECTED param typ (re-sourced from the arg's own typ; the
        // serializer mirrors production's `fn_param_typs`). This subsumes
        // the G2 special case (deref iff the pair is (TyRef, pointee))
        // and adds the mk-wrap grow + both sort-bridge directions. The
        // old two-step (nat-coerce then needs_ref_deref on the ACTUAL
        // typ alone) mis-derived `v.deref` where production writes bare
        // `v` whenever the callee's param is itself ref-typed (vec_read).
        RawExp::Call(fnid, _ret, arg, argty) =>
            ExprData::App(fnid, Box::new(reconcile_arg(type_of(*arg), argty, render_exp(*arg)))),
        // G3: field projection. `fid` already matches production's accessor id.
        RawExp::Field(fid, _fty, base) =>
            ExprData::FieldProj(Box::new(render_exp(*base)), fid),
        // G6: reproduce production's unsigned-overflow expansion
        // `0 ≤ e ∧ e < 2^n` (`type_bound_predicate`'s `unsigned` shape). The
        // opcodes are the canonical table (And = 11, Le = 3, Lt = 2); `e`
        // renders once and appears in both conjuncts, exactly as production
        // reuses the one rendered `e_ast`.
        RawExp::HasType(n, inner) => {
            let e2 = render_exp(*inner);
            ExprData::BinOp(11,
                Box::new(ExprData::BinOp(3, Box::new(ExprData::Lit(0)), Box::new(e2))),
                Box::new(ExprData::BinOp(2, Box::new(e2),
                    Box::new(ExprData::Lit(pow2(n as nat))))))
        },
        RawExp::Deref(e) => ExprData::FieldProj(Box::new(render_exp(*e)), deref_field()),
        // G4: structural pass-through — the binder id rides across, value and
        // body render recursively (their own coercions already materialized at
        // BinOp/Call/Clip). No coercion decision at the Let/Not node itself.
        RawExp::Let(name, val, body) =>
            ExprData::Let(name, Box::new(render_exp(*val)), Box::new(render_exp(*body))),
        RawExp::Not(e) => ExprData::Not(Box::new(render_exp(*e))),
        RawExp::Span(loc, e) => ExprData::SpanMark(loc, Box::new(render_exp(*e))),
        // W7: first-class if. Cond is bool (never coerced); each branch is
        // materialized iff it renders Int under a Nat result type (Friction-2,
        // like BinOp operands). `tri`'s branches are already Nat → no cast.
        RawExp::Ite(ty, c, t, e) => {
            let t2 = coerce_if(needs_nat_coercion(type_of(*t), ty), render_exp(*t));
            let e2 = coerce_if(needs_nat_coercion(type_of(*e), ty), render_exp(*e));
            ExprData::Ite(Box::new(render_exp(*c)), Box::new(t2), Box::new(e2))
        },
        // W7: match. Scrutinee is never coerced; each arm body is materialized
        // like an Ite branch (the carried result type `ty` flows into render_arms).
        RawExp::MatchR(scrut, arms, ty) =>
            ExprData::Match(Box::new(render_exp(*scrut)), Box::new(render_arms(*arms, ty))),
        // W7: multi-arg app. A7 (bootstrap-80 F3): each arg renders
        // through `reconcile_arg` at its carried EXPECTED param typ
        // (the RawList pair slot) — this was the "deferred to W7c"
        // per-arg coercion gap (the `Int.ofNat` on `Seq.index` args).
        RawExp::CallN(fnid, _ret, args) =>
            ExprData::AppN(fnid, Box::new(render_list(*args))),
        // W7: quantifiers pass the binder id + type through; body renders recursively.
        RawExp::ForallR(bid, bty, body) =>
            ExprData::Forall(bid, bty, Box::new(render_exp(*body))),
        RawExp::ExistsR(bid, bty, body) =>
            ExprData::Exists(bid, bty, Box::new(render_exp(*body))),
    }
}

// W7: render the arm list, MUTUALLY recursive with `render_exp`. Binder ids
// ride STRAIGHT THROUGH (the §7 Q1 discipline — reference and production must
// intern arm-binder ids identically; a mismatch is a shape diff the bridge
// catches). Each arm body is coerced at the carried result type `ty`, exactly
// like an Ite branch.
#[verifier::structural_decreases]
pub open spec fn render_arms(a: RawArmList, ty: TypData) -> ArmList
    decreases a
{
    match a {
        RawArmList::Nil => ArmList::Nil,
        RawArmList::Cons(c, bs, body, tl) =>
            ArmList::Cons(c, bs,
                Box::new(coerce_if(needs_nat_coercion(type_of(*body), ty), render_exp(*body))),
                Box::new(render_arms(*tl, ty))),
    }
}

// W7: render the multi-arg argument list, mutually recursive with `render_exp`.
// A7: each element pairs the arg with its EXPECTED param typ — the arg
// renders recursively, then `reconcile_arg` derives the slot coercion
// from the (actual, expected) pair (production's per-arg `into_slot`).
#[verifier::structural_decreases]
pub open spec fn render_list(l: RawList) -> ExprList
    decreases l
{
    match l {
        RawList::Nil => ExprList::Nil,
        RawList::Cons(h, expected, t) =>
            ExprList::Cons(
                Box::new(reconcile_arg(type_of(*h), expected, render_exp(*h))),
                Box::new(render_list(*t)),
            ),
    }
}

// W7: reference def lowering — copy the header (name/params/ret transcribed
// straight from VIR) and render the body INDEPENDENTLY via `render_exp`.
pub open spec fn render_def(d: RawDef) -> DefData {
    DefData { name: d.name, params: d.params, ret: d.ret, body: render_exp(d.body) }
}

// W7: reference datatype lowering — ctor names + positional field types
// straight through (no body; the diversity is the VIR-vs-LExpr transcription).
pub open spec fn render_dt(d: RawDt) -> DtData {
    DtData { name: d.name, ctors: d.ctors }
}

// ── W6b: structural equality on expressions (the LeafE bridge) ──────
// Same discipline as `goal_eq`: match the FIRST arg alone (structural +
// unambiguous), read the second through NON-recursive tag+projection
// accessors, every arm body a chain of `if`s (never a nested match). Returns
// nat (1/0) for the `decide` idiom.

pub open spec fn ck_tag(k: CastKind) -> nat {
    match k {
        CastKind::IntToNat => 0,
        CastKind::NatToInt => 1,
    }
}
pub open spec fn castkind_eq(a: CastKind, b: CastKind) -> nat {
    if ck_tag(a) == ck_tag(b) { 1 } else { 0 }
}

pub open spec fn ed_tag(e: ExprData) -> nat {
    match e {
        ExprData::Atom(_) => 0,
        ExprData::Lit(_) => 1,
        ExprData::Cast(_, _) => 2,
        ExprData::BinOp(_, _, _) => 3,
        ExprData::App(_, _) => 4,
        ExprData::FieldProj(_, _) => 5,
        ExprData::SpanMark(_, _) => 6,
        ExprData::LitBool(_) => 7,
        ExprData::Let(_, _, _) => 8,
        ExprData::Not(_) => 9,
        // W7 body constructors.
        ExprData::Ite(_, _, _) => 10,
        ExprData::Match(_, _) => 11,
        ExprData::AppN(_, _) => 12,
        ExprData::Forall(_, _, _) => 13,
        ExprData::Exists(_, _, _) => 14,
        // A7 wrapper constructions.
        ExprData::RefMk(_) => 15,
        ExprData::BoxMk(_) => 16,
    }
}
pub open spec fn ed_atom_id(e: ExprData) -> u64 { match e { ExprData::Atom(x) => x, _ => 0 } }
pub open spec fn ed_lit_val(e: ExprData) -> int { match e { ExprData::Lit(v) => v, _ => 0 } }
pub open spec fn ed_litbool_val(e: ExprData) -> nat { match e { ExprData::LitBool(x) => x, _ => 0 } }
pub open spec fn ed_cast_k(e: ExprData) -> CastKind { match e { ExprData::Cast(k, _) => k, _ => CastKind::IntToNat } }
pub open spec fn ed_cast_e(e: ExprData) -> ExprData { match e { ExprData::Cast(_, t) => *t, _ => ExprData::Atom(0) } }
pub open spec fn ed_binop_op(e: ExprData) -> u64 { match e { ExprData::BinOp(op, _, _) => op, _ => 0 } }
pub open spec fn ed_binop_l(e: ExprData) -> ExprData { match e { ExprData::BinOp(_, l, _) => *l, _ => ExprData::Atom(0) } }
pub open spec fn ed_binop_r(e: ExprData) -> ExprData { match e { ExprData::BinOp(_, _, r) => *r, _ => ExprData::Atom(0) } }
pub open spec fn ed_app_fn(e: ExprData) -> u64 { match e { ExprData::App(f, _) => f, _ => 0 } }
pub open spec fn ed_app_arg(e: ExprData) -> ExprData { match e { ExprData::App(_, a) => *a, _ => ExprData::Atom(0) } }
pub open spec fn ed_fp_e(e: ExprData) -> ExprData { match e { ExprData::FieldProj(t, _) => *t, _ => ExprData::Atom(0) } }
pub open spec fn ed_fp_field(e: ExprData) -> u64 { match e { ExprData::FieldProj(_, f) => f, _ => 0 } }
pub open spec fn ed_span_loc(e: ExprData) -> u64 { match e { ExprData::SpanMark(loc, _) => loc, _ => 0 } }
pub open spec fn ed_span_e(e: ExprData) -> ExprData { match e { ExprData::SpanMark(_, t) => *t, _ => ExprData::Atom(0) } }
// G4: Let/Not projections.
pub open spec fn ed_let_name(e: ExprData) -> u64 { match e { ExprData::Let(n, _, _) => n, _ => 0 } }
pub open spec fn ed_let_val(e: ExprData) -> ExprData { match e { ExprData::Let(_, v, _) => *v, _ => ExprData::Atom(0) } }
pub open spec fn ed_let_body(e: ExprData) -> ExprData { match e { ExprData::Let(_, _, b) => *b, _ => ExprData::Atom(0) } }
pub open spec fn ed_not_e(e: ExprData) -> ExprData { match e { ExprData::Not(t) => *t, _ => ExprData::Atom(0) } }
// W7: projections for the body constructors (read the 2nd `expr_eq` arg via
// tag + NON-recursive accessors — the `goal_eq` idiom, no nested match).
pub open spec fn ed_ite_c(e: ExprData) -> ExprData { match e { ExprData::Ite(c, _, _) => *c, _ => ExprData::Atom(0) } }
pub open spec fn ed_ite_t(e: ExprData) -> ExprData { match e { ExprData::Ite(_, t, _) => *t, _ => ExprData::Atom(0) } }
pub open spec fn ed_ite_e(e: ExprData) -> ExprData { match e { ExprData::Ite(_, _, el) => *el, _ => ExprData::Atom(0) } }
pub open spec fn ed_match_scrut(e: ExprData) -> ExprData { match e { ExprData::Match(s, _) => *s, _ => ExprData::Atom(0) } }
pub open spec fn ed_match_arms(e: ExprData) -> ArmList { match e { ExprData::Match(_, a) => *a, _ => ArmList::Nil } }
pub open spec fn ed_appn_fn(e: ExprData) -> u64 { match e { ExprData::AppN(f, _) => f, _ => 0 } }
pub open spec fn ed_appn_args(e: ExprData) -> ExprList { match e { ExprData::AppN(_, a) => *a, _ => ExprList::Nil } }
pub open spec fn ed_forall_bid(e: ExprData) -> u64 { match e { ExprData::Forall(x, _, _) => x, _ => 0 } }
pub open spec fn ed_forall_bty(e: ExprData) -> TypData { match e { ExprData::Forall(_, t, _) => t, _ => TypData::TyInt } }
pub open spec fn ed_forall_body(e: ExprData) -> ExprData { match e { ExprData::Forall(_, _, b) => *b, _ => ExprData::Atom(0) } }
pub open spec fn ed_exists_bid(e: ExprData) -> u64 { match e { ExprData::Exists(x, _, _) => x, _ => 0 } }
pub open spec fn ed_exists_bty(e: ExprData) -> TypData { match e { ExprData::Exists(_, t, _) => t, _ => TypData::TyInt } }
pub open spec fn ed_exists_body(e: ExprData) -> ExprData { match e { ExprData::Exists(_, _, b) => *b, _ => ExprData::Atom(0) } }
// A7: RefMk/BoxMk projections.
pub open spec fn ed_refmk_e(e: ExprData) -> ExprData { match e { ExprData::RefMk(t) => *t, _ => ExprData::Atom(0) } }
pub open spec fn ed_boxmk_e(e: ExprData) -> ExprData { match e { ExprData::BoxMk(t) => *t, _ => ExprData::Atom(0) } }
// ArmList projections (read `arms_eq`'s 2nd arg): head ctor/binds/body + tail.
pub open spec fn al_is_nil(a: ArmList) -> nat { match a { ArmList::Nil => 1, _ => 0 } }
pub open spec fn al_hd_ctor(a: ArmList) -> u64 { match a { ArmList::Cons(c, _, _, _) => c, _ => 0 } }
pub open spec fn al_hd_binds(a: ArmList) -> BinderIdList { match a { ArmList::Cons(_, bs, _, _) => bs, _ => BinderIdList::Nil } }
pub open spec fn al_hd_body(a: ArmList) -> ExprData { match a { ArmList::Cons(_, _, b, _) => *b, _ => ExprData::Atom(0) } }
pub open spec fn al_tl(a: ArmList) -> ArmList { match a { ArmList::Cons(_, _, _, t) => *t, _ => ArmList::Nil } }
// ExprList projections (read `exprlist_eq`'s 2nd arg): head + tail.
pub open spec fn el_is_nil(l: ExprList) -> nat { match l { ExprList::Nil => 1, _ => 0 } }
pub open spec fn el_hd(l: ExprList) -> ExprData { match l { ExprList::Cons(h, _) => *h, _ => ExprData::Atom(0) } }
pub open spec fn el_tl(l: ExprList) -> ExprList { match l { ExprList::Cons(_, t) => *t, _ => ExprList::Nil } }
// BinderIdList projections + nat-returning equality (arm binder ids — the §7 Q1
// discipline). Projection idiom (match first arg, read 2nd via accessors) —
// a nested match on the 2nd arg breaks Lean structural-recursion inference.
pub open spec fn bil_is_nil(b: BinderIdList) -> nat { match b { BinderIdList::Nil => 1, _ => 0 } }
pub open spec fn bil_hd(b: BinderIdList) -> u64 { match b { BinderIdList::Cons(x, _) => x, _ => 0 } }
pub open spec fn bil_tl(b: BinderIdList) -> BinderIdList { match b { BinderIdList::Cons(_, t) => *t, _ => BinderIdList::Nil } }
#[verifier::structural_decreases]
pub open spec fn bidl_eq(a: BinderIdList, b: BinderIdList) -> nat
    decreases a
{
    match a {
        BinderIdList::Nil => bil_is_nil(b),
        BinderIdList::Cons(x, t) =>
            if bil_is_nil(b) == 1 { 0 }
            else if x == bil_hd(b) { bidl_eq(*t, bil_tl(b)) }
            else { 0 },
    }
}

#[verifier::structural_decreases]
pub open spec fn expr_eq(a: ExprData, b: ExprData) -> nat
    decreases a
{
    match a {
        ExprData::Atom(x) =>
            if ed_tag(b) == 0 { if x == ed_atom_id(b) { 1 } else { 0 } } else { 0 },
        ExprData::Lit(v) =>
            if ed_tag(b) == 1 { if v == ed_lit_val(b) { 1 } else { 0 } } else { 0 },
        ExprData::LitBool(x) =>
            if ed_tag(b) == 7 { if x == ed_litbool_val(b) { 1 } else { 0 } } else { 0 },
        ExprData::Cast(k, t) =>
            if ed_tag(b) == 2 {
                if castkind_eq(k, ed_cast_k(b)) == 1 { expr_eq(*t, ed_cast_e(b)) } else { 0 }
            } else { 0 },
        ExprData::BinOp(op, l, r) =>
            if ed_tag(b) == 3 {
                if op == ed_binop_op(b) {
                    if expr_eq(*l, ed_binop_l(b)) == 1 { expr_eq(*r, ed_binop_r(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        ExprData::App(f, a2) =>
            if ed_tag(b) == 4 {
                if f == ed_app_fn(b) { expr_eq(*a2, ed_app_arg(b)) } else { 0 }
            } else { 0 },
        ExprData::FieldProj(t, fld) =>
            if ed_tag(b) == 5 {
                if fld == ed_fp_field(b) { expr_eq(*t, ed_fp_e(b)) } else { 0 }
            } else { 0 },
        ExprData::SpanMark(loc, t) =>
            if ed_tag(b) == 6 {
                if loc == ed_span_loc(b) { expr_eq(*t, ed_span_e(b)) } else { 0 }
            } else { 0 },
        // G4: let equality — name id, then value, then body (body binder is
        // `bd` so it does not shadow the second-arg parameter `b`).
        ExprData::Let(n, v, bd) =>
            if ed_tag(b) == 8 {
                if n == ed_let_name(b) {
                    if expr_eq(*v, ed_let_val(b)) == 1 { expr_eq(*bd, ed_let_body(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        ExprData::Not(t) =>
            if ed_tag(b) == 9 { expr_eq(*t, ed_not_e(b)) } else { 0 },
        // ── W7 body constructors. Same tag+projection idiom; `Match`/`AppN`
        //    recurse through the mutual `arms_eq`/`exprlist_eq`. ──
        ExprData::Ite(c, t, e) =>
            if ed_tag(b) == 10 {
                if expr_eq(*c, ed_ite_c(b)) == 1 {
                    if expr_eq(*t, ed_ite_t(b)) == 1 { expr_eq(*e, ed_ite_e(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        ExprData::Match(s, arms) =>
            if ed_tag(b) == 11 {
                if expr_eq(*s, ed_match_scrut(b)) == 1 { arms_eq(*arms, ed_match_arms(b)) } else { 0 }
            } else { 0 },
        ExprData::AppN(f, args) =>
            if ed_tag(b) == 12 {
                if f == ed_appn_fn(b) { exprlist_eq(*args, ed_appn_args(b)) } else { 0 }
            } else { 0 },
        ExprData::Forall(bid, bty, body) =>
            if ed_tag(b) == 13 {
                if bid == ed_forall_bid(b) {
                    if typ_eq(bty, ed_forall_bty(b)) == 1 { expr_eq(*body, ed_forall_body(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        ExprData::Exists(bid, bty, body) =>
            if ed_tag(b) == 14 {
                if bid == ed_exists_bid(b) {
                    if typ_eq(bty, ed_exists_bty(b)) == 1 { expr_eq(*body, ed_exists_body(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        // A7: wrapper constructions — structural on the inner.
        ExprData::RefMk(t) =>
            if ed_tag(b) == 15 { expr_eq(*t, ed_refmk_e(b)) } else { 0 },
        ExprData::BoxMk(t) =>
            if ed_tag(b) == 16 { expr_eq(*t, ed_boxmk_e(b)) } else { 0 },
    }
}

// W7: the arm-list / expr-list structural equalities, MUTUALLY recursive with
// `expr_eq` (arms_eq recurses INTO expr_eq on arm bodies — the genuine mutual
// eq W7a's derived-`=` shortcut left unvalidated; validated in-crate by
// probe_mutual2). Match the first arg, read the second via projections.
#[verifier::structural_decreases]
pub open spec fn arms_eq(a: ArmList, b: ArmList) -> nat
    decreases a
{
    match a {
        ArmList::Nil => al_is_nil(b),
        ArmList::Cons(c, bs, body, tl) =>
            if al_is_nil(b) == 1 { 0 }
            else if c == al_hd_ctor(b) {
                if bidl_eq(bs, al_hd_binds(b)) == 1 {
                    if expr_eq(*body, al_hd_body(b)) == 1 { arms_eq(*tl, al_tl(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
    }
}

#[verifier::structural_decreases]
pub open spec fn exprlist_eq(a: ExprList, b: ExprList) -> nat
    decreases a
{
    match a {
        ExprList::Nil => el_is_nil(b),
        ExprList::Cons(h, t) =>
            if el_is_nil(b) == 1 { 0 }
            else if expr_eq(*h, el_hd(b)) == 1 { exprlist_eq(*t, el_tl(b)) } else { 0 },
    }
}

// ── W7 def-header layer: nat-returning equalities for the def/dt structs ──
// The list eqs follow the same match-first-arg + projection idiom; `def_eq`/
// `dt_eq` are non-recursive struct projections (spec field access, cf.
// `fnctx_arity`).

// ParamList projections + equality (param id + type).
pub open spec fn pl_is_nil(p: ParamList) -> nat { match p { ParamList::Nil => 1, _ => 0 } }
pub open spec fn pl_hd_id(p: ParamList) -> u64 { match p { ParamList::Cons(id, _, _) => id, _ => 0 } }
pub open spec fn pl_hd_ty(p: ParamList) -> TypData { match p { ParamList::Cons(_, ty, _) => ty, _ => TypData::TyInt } }
pub open spec fn pl_tl(p: ParamList) -> ParamList { match p { ParamList::Cons(_, _, t) => *t, _ => ParamList::Nil } }
#[verifier::structural_decreases]
pub open spec fn param_list_eq(a: ParamList, b: ParamList) -> nat
    decreases a
{
    match a {
        ParamList::Nil => pl_is_nil(b),
        ParamList::Cons(id, ty, t) =>
            if pl_is_nil(b) == 1 { 0 }
            else if id == pl_hd_id(b) {
                if typ_eq(ty, pl_hd_ty(b)) == 1 { param_list_eq(*t, pl_tl(b)) } else { 0 }
            } else { 0 },
    }
}

// TypList projections + equality (positional field types).
pub open spec fn tyl_is_nil(l: TypList) -> nat { match l { TypList::Nil => 1, _ => 0 } }
pub open spec fn tyl_hd(l: TypList) -> TypData { match l { TypList::Cons(ty, _) => ty, _ => TypData::TyInt } }
pub open spec fn tyl_tl(l: TypList) -> TypList { match l { TypList::Cons(_, t) => *t, _ => TypList::Nil } }
#[verifier::structural_decreases]
pub open spec fn typ_list_eq(a: TypList, b: TypList) -> nat
    decreases a
{
    match a {
        TypList::Nil => tyl_is_nil(b),
        TypList::Cons(ty, t) =>
            if tyl_is_nil(b) == 1 { 0 }
            else if typ_eq(ty, tyl_hd(b)) == 1 { typ_list_eq(*t, tyl_tl(b)) } else { 0 },
    }
}

// CtorList projections + equality (ctor name + positional field types).
pub open spec fn cl_is_nil(c: CtorList) -> nat { match c { CtorList::Nil => 1, _ => 0 } }
pub open spec fn cl_hd_name(c: CtorList) -> u64 { match c { CtorList::Cons(nm, _, _) => nm, _ => 0 } }
pub open spec fn cl_hd_fields(c: CtorList) -> TypList { match c { CtorList::Cons(_, f, _) => f, _ => TypList::Nil } }
pub open spec fn cl_tl(c: CtorList) -> CtorList { match c { CtorList::Cons(_, _, t) => *t, _ => CtorList::Nil } }
#[verifier::structural_decreases]
pub open spec fn ctor_list_eq(a: CtorList, b: CtorList) -> nat
    decreases a
{
    match a {
        CtorList::Nil => cl_is_nil(b),
        CtorList::Cons(nm, flds, t) =>
            if cl_is_nil(b) == 1 { 0 }
            else if nm == cl_hd_name(b) {
                if typ_list_eq(flds, cl_hd_fields(b)) == 1 { ctor_list_eq(*t, cl_tl(b)) } else { 0 }
            } else { 0 },
    }
}

// def / dt equality: name + params + ret + body (body via the deep `expr_eq`);
// name + ctors. Non-recursive (struct-field projections + the list/expr eqs).
pub open spec fn def_eq(a: DefData, b: DefData) -> nat {
    if a.name == b.name {
        if param_list_eq(a.params, b.params) == 1 {
            if typ_eq(a.ret, b.ret) == 1 { expr_eq(a.body, b.body) } else { 0 }
        } else { 0 }
    } else { 0 }
}
pub open spec fn dt_eq(a: DtData, b: DtData) -> nat {
    if a.name == b.name { ctor_list_eq(a.ctors, b.ctors) } else { 0 }
}

// In-crate kernel-computation guard for the expression mirror: the W6a
// probe's Cases A/B/C + the D negative control, now against the LANDED
// render_exp/expr_eq — pinning that the frozen shape kernel-computes IN
// tactus-core (analogous to `skeleton_kernel_computes`). Case B is
// load-bearing: render_exp DERIVES both `Int.toNat`s from `Mul:Nat` +
// `operand:Int` (no source cast to copy), so an inconsistent production shape
// diverges — the documented core win (DESIGN-W6-stageB.md §3.1/§6).
proof fn expr_mirror_kernel_computes()
    ensures
        // Case A — sum_to leaf `Int.toNat r = lib.tri (Int.toNat n)` from raw
        // `(r as nat) == tri((n as nat))`; kill = LHS Int.toNat dropped.
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::Var(1, TypData::TyInt)))),
                Box::new(RawExp::Call(10, TypData::TyNat,
                    Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::Var(2, TypData::TyInt)))),
                    TypData::TyNat)))),
            ExprData::BinOp(0,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(1)))),
                Box::new(ExprData::App(10,
                    Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(2)))))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::Var(1, TypData::TyInt)))),
                Box::new(RawExp::Call(10, TypData::TyNat,
                    Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::Var(2, TypData::TyInt)))),
                    TypData::TyNat)))),
            ExprData::BinOp(0,
                Box::new(ExprData::Atom(1)),  // BUG: forgotten Int.toNat
                Box::new(ExprData::App(10,
                    Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(2)))))))
        ) == 0,
        // Case B — `(x as nat) * x`, BOTH inner clips elided: render_exp
        // DERIVES both casts from the nat-typed Mul. Kill = inconsistent.
        expr_eq(
            render_exp(RawExp::BinOp(1, TypData::TyNat,
                Box::new(RawExp::Var(3, TypData::TyInt)),
                Box::new(RawExp::Var(3, TypData::TyInt)))),
            ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::BinOp(1, TypData::TyNat,
                Box::new(RawExp::Var(3, TypData::TyInt)),
                Box::new(RawExp::Var(3, TypData::TyInt)))),
            ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Atom(3)))  // BUG: cast at one operand only
        ) == 0,
        // Case C — `lib.tree_head (*t)` on t:&Tree → FieldProj; kill = deref
        // dropped.
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(100),
                Box::new(RawExp::Deref(Box::new(RawExp::Var(4, TypData::TyRef(100))))),
                TypData::TyNamed(100))),
            ExprData::App(11, Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(4)), 0)))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(100),
                Box::new(RawExp::Deref(Box::new(RawExp::Var(4, TypData::TyRef(100))))),
                TypData::TyNamed(100))),
            ExprData::App(11, Box::new(ExprData::Atom(4)))  // BUG: dropped .deref
        ) == 0,
        // Negative control (D): a bool-typed cmp does NOT coerce its bare LHS
        // (needs_nat_coercion fires only on Nat targets).
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Var(3, TypData::TyInt)),
                Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::Var(3, TypData::TyInt)))))),
            ExprData::BinOp(0,
                Box::new(ExprData::Atom(3)),
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))))
        ) == 1,
        // Lit + measures kernel-compute.
        expr_eq(ExprData::Lit(5), ExprData::Lit(5)) == 1,
        expr_eq(ExprData::Lit(5), ExprData::Lit(6)) == 0,
        // G1 — bool literal straight through (nat encoding: 1 = true);
        // value mismatch caught.
        expr_eq(render_exp(RawExp::LitBool(1)), ExprData::LitBool(1)) == 1,
        expr_eq(render_exp(RawExp::LitBool(1)), ExprData::LitBool(0)) == 0,
        // G6 — the u64 overflow refinement `0 ≤ x+y ∧ x+y < 2^64`, DERIVED by
        // render_exp from a `HasType(64)` node (production `type_bound_predicate`
        // expands identically). `pow2(64)` re-derives the bound independently.
        // Kill = wrong bound width (2^32).
        expr_eq(
            render_exp(RawExp::HasType(64,
                Box::new(RawExp::BinOp(6, TypData::TyInt,
                    Box::new(RawExp::Var(1, TypData::TyInt)),
                    Box::new(RawExp::Var(2, TypData::TyInt)))))),
            ExprData::BinOp(11,
                Box::new(ExprData::BinOp(3, Box::new(ExprData::Lit(0)),
                    Box::new(ExprData::BinOp(6, Box::new(ExprData::Atom(1)), Box::new(ExprData::Atom(2)))))),
                Box::new(ExprData::BinOp(2,
                    Box::new(ExprData::BinOp(6, Box::new(ExprData::Atom(1)), Box::new(ExprData::Atom(2)))),
                    Box::new(ExprData::Lit(18446744073709551616)))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::HasType(64,
                Box::new(RawExp::BinOp(6, TypData::TyInt,
                    Box::new(RawExp::Var(1, TypData::TyInt)),
                    Box::new(RawExp::Var(2, TypData::TyInt)))))),
            ExprData::BinOp(11,
                Box::new(ExprData::BinOp(3, Box::new(ExprData::Lit(0)),
                    Box::new(ExprData::BinOp(6, Box::new(ExprData::Atom(1)), Box::new(ExprData::Atom(2)))))),
                Box::new(ExprData::BinOp(2,
                    Box::new(ExprData::BinOp(6, Box::new(ExprData::Atom(1)), Box::new(ExprData::Atom(2)))),
                    Box::new(ExprData::Lit(4294967296)))))  // BUG: 2^32, not 2^64
        ) == 0,
        // G3 — struct field projection `p.x` (field id 5). Kill = dropped proj.
        expr_eq(
            render_exp(RawExp::Field(5, TypData::TyInt,
                Box::new(RawExp::Var(9, TypData::TyNamed(50))))),
            ExprData::FieldProj(Box::new(ExprData::Atom(9)), 5)
        ) == 1,
        expr_eq(
            render_exp(RawExp::Field(5, TypData::TyInt,
                Box::new(RawExp::Var(9, TypData::TyNamed(50))))),
            ExprData::Atom(9)  // BUG: dropped `.x`
        ) == 0,
        // G2 — the REAL head_exec path: a bare `&Tree` typed Var arg (NO
        // explicit Deref node); render_exp DERIVES the `.deref` from the arg's
        // `TyRef` tag. Distinct from Case C (explicit source Deref). Kill =
        // deref dropped.
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(100),
                Box::new(RawExp::Var(4, TypData::TyRef(100))),
                TypData::TyNamed(100))),
            ExprData::App(11, Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(4)), 0)))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(100),
                Box::new(RawExp::Var(4, TypData::TyRef(100))),
                TypData::TyNamed(100))),
            ExprData::App(11, Box::new(ExprData::Atom(4)))  // BUG: no auto-deref
        ) == 0,
        // ── B1 (bootstrap-48) — structural-binop min-balance in the TCB ──
        // The real `runtime__impl__4__clone` shape: `result:T == self:&Self`
        // (`Eq`=0, Bool result). LHS `result` is bare `TyNamed(5)` (depth 0),
        // RHS `self` is `TyRef(5)` (depth 1); min-balance peels the DEEPER RHS
        // by one `.deref`, leaving the LHS alone. render_exp DERIVES this from
        // the operand TypData independently of production. Kill = the RHS peel
        // dropped (reproduces the pre-B1 `0 passed, 1 failed` bridge divergence).
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Var(6, TypData::TyNamed(5))),
                Box::new(RawExp::Var(0, TypData::TyRef(5))))),
            ExprData::BinOp(0,
                Box::new(ExprData::Atom(6)),
                Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(0)), 0)))
        ) == 1,
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Var(6, TypData::TyNamed(5))),
                Box::new(RawExp::Var(0, TypData::TyRef(5))))),
            ExprData::BinOp(0,
                Box::new(ExprData::Atom(6)),
                Box::new(ExprData::Atom(0)))  // BUG: min-balance deref dropped
        ) == 0,
        // B1 negative control: `&Self == &Self` (BOTH operands depth 1) →
        // min-balance m=1 → NEITHER operand peeled (production leaves matched
        // depths alone). This is exactly what an unsound blanket per-operand
        // `Var(TyRef _) => .deref` rule would get WRONG (it would peel both);
        // the min-balance form must leave both bare.
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Var(6, TypData::TyRef(5))),
                Box::new(RawExp::Var(0, TypData::TyRef(5))))),
            ExprData::BinOp(0,
                Box::new(ExprData::Atom(6)),
                Box::new(ExprData::Atom(0)))
        ) == 1,
        expr_eq(
            render_exp(RawExp::BinOp(0, TypData::TyBool,
                Box::new(RawExp::Var(6, TypData::TyRef(5))),
                Box::new(RawExp::Var(0, TypData::TyRef(5))))),
            ExprData::BinOp(0,
                Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(6)), 0)),  // BUG: peeled a matched-depth operand
                Box::new(ExprData::Atom(0)))
        ) == 0,
        expr_size(ExprData::BinOp(1,
            Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
            Box::new(ExprData::Atom(3)))) == 4,
        typ_size(TypData::TyRef(7)) == 1,
        // ── G4 — the max_u64 If-fold leaf (the deepest gap) ──
        // leaf 15: `x < y → (let r := let m := y; m; r ≥ x ∧ r ≥ y)`, i.e.
        //   Implies(Lt(x,y), Let(r, Let(m, y, m), And(Span(r≥x), Span(r≥y)))).
        // ids x=0 y=4 r=10 m=14, spans 9/12; opcodes Implies=13 Lt=2 And=11 Ge=5.
        // render_exp reproduces production's leaf via the new Let arm (structural)
        // + the frozen BinOp/Span arms (bool targets → no coercion). This is the
        // reference-side shape the W6e serializer recompute must emit.
        expr_eq(
            render_exp(RawExp::BinOp(13, TypData::TyBool,
                Box::new(RawExp::BinOp(2, TypData::TyBool,
                    Box::new(RawExp::Var(0, TypData::TyInt)), Box::new(RawExp::Var(4, TypData::TyInt)))),
                Box::new(RawExp::Let(10,
                    Box::new(RawExp::Let(14, Box::new(RawExp::Var(4, TypData::TyInt)),
                        Box::new(RawExp::Var(14, TypData::TyInt)))),
                    Box::new(RawExp::BinOp(11, TypData::TyBool,
                        Box::new(RawExp::Span(9, Box::new(RawExp::BinOp(5, TypData::TyBool,
                            Box::new(RawExp::Var(10, TypData::TyInt)), Box::new(RawExp::Var(0, TypData::TyInt)))))),
                        Box::new(RawExp::Span(12, Box::new(RawExp::BinOp(5, TypData::TyBool,
                            Box::new(RawExp::Var(10, TypData::TyInt)), Box::new(RawExp::Var(4, TypData::TyInt)))))))))))),
            ExprData::BinOp(13,
                Box::new(ExprData::BinOp(2, Box::new(ExprData::Atom(0)), Box::new(ExprData::Atom(4)))),
                Box::new(ExprData::Let(10,
                    Box::new(ExprData::Let(14, Box::new(ExprData::Atom(4)), Box::new(ExprData::Atom(14)))),
                    Box::new(ExprData::BinOp(11,
                        Box::new(ExprData::SpanMark(9, Box::new(ExprData::BinOp(5,
                            Box::new(ExprData::Atom(10)), Box::new(ExprData::Atom(0)))))),
                        Box::new(ExprData::SpanMark(12, Box::new(ExprData::BinOp(5,
                            Box::new(ExprData::Atom(10)), Box::new(ExprData::Atom(4)))))))))))
        ) == 1,
        // Kill: the inner `let m := y; m` is dropped (Let value → bare `y`). The
        // reference still binds it, so the shapes diverge (Let-tag vs Atom-tag).
        expr_eq(
            render_exp(RawExp::Let(10,
                Box::new(RawExp::Let(14, Box::new(RawExp::Var(4, TypData::TyInt)),
                    Box::new(RawExp::Var(14, TypData::TyInt)))),
                Box::new(RawExp::Var(10, TypData::TyInt)))),
            ExprData::Let(10, Box::new(ExprData::Atom(4)), Box::new(ExprData::Atom(10)))  // BUG: inner let dropped
        ) == 0,
        // Not — `¬(x < y)` (leaf 16's branch guard). render_exp maps the new
        // Not arm straight through; kill = the `¬` dropped.
        expr_eq(
            render_exp(RawExp::Not(Box::new(RawExp::BinOp(2, TypData::TyBool,
                Box::new(RawExp::Var(0, TypData::TyInt)), Box::new(RawExp::Var(4, TypData::TyInt)))))),
            ExprData::Not(Box::new(ExprData::BinOp(2, Box::new(ExprData::Atom(0)), Box::new(ExprData::Atom(4)))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Not(Box::new(RawExp::BinOp(2, TypData::TyBool,
                Box::new(RawExp::Var(0, TypData::TyInt)), Box::new(RawExp::Var(4, TypData::TyInt)))))),
            ExprData::BinOp(2, Box::new(ExprData::Atom(0)), Box::new(ExprData::Atom(4)))  // BUG: dropped ¬
        ) == 0,
        // Let/Not measures kernel-compute (Let=1 + Atom=1 + [Not=1 + Atom=1] = 4).
        expr_size(ExprData::Let(10, Box::new(ExprData::Atom(4)),
            Box::new(ExprData::Not(Box::new(ExprData::Atom(0)))))) == 4
by { decide }

// W7: in-crate kernel-computation guard for the DEFS-layer expression
// vocabulary — the analog of `expr_mirror_kernel_computes` for the new body
// constructors, against the LANDED `render_exp`/`expr_eq`/`render_arms`. The
// real emitted-fixture shapes (probe15_w7a_defs; ground truth
// TactusDefs_lib_exec__{root,base}.lean): `tri`(Ite), `tree_head`(Match),
// `Tree.height`(self-recursive Match + Box-`Deref`), + `AppN`/`Forall`. Each
// correct-closes to 1 and a single mutation flips to 0 (non-vacuous) — pinning
// that the frozen Match/AppN/Ite/Forall vocabulary kernel-computes IN
// tactus-core (the mutual `render_arms`/`arms_eq` structural recursion reduces
// under `decide`, no `WellFounded.fix`). ids/opcodes per probe15 (nId=1 vId=2
// tId=3 sId=4 lId=5 rId=6 val0=7 val1=8 aId=9 bId=10 kId=15 triId=20
// treeHeadId=21 heightId=23 gId=24 leafCtor=30 nodeCtor=31 treeTy=100;
// eqOp=0 addOp=6 subOp=7).
proof fn defs_expr_vocab_kernel_computes()
    ensures
        // ── Ite — `tri`'s body `if n=0 then 0 else n + tri(Int.toNat (n-1))` ──
        expr_eq(
            render_exp(RawExp::Ite(TypData::TyNat,
                Box::new(RawExp::BinOp(0, TypData::TyBool,
                    Box::new(RawExp::Var(1, TypData::TyNat)), Box::new(RawExp::Lit(0, TypData::TyNat)))),
                Box::new(RawExp::Lit(0, TypData::TyNat)),
                Box::new(RawExp::BinOp(6, TypData::TyNat,
                    Box::new(RawExp::Var(1, TypData::TyNat)),
                    Box::new(RawExp::Call(20, TypData::TyNat,
                        Box::new(RawExp::Clip(TypData::TyNat, Box::new(RawExp::BinOp(7, TypData::TyInt,
                            Box::new(RawExp::Var(1, TypData::TyInt)), Box::new(RawExp::Lit(1, TypData::TyInt)))))),
                        TypData::TyNat)))))),
            ExprData::Ite(
                Box::new(ExprData::BinOp(0, Box::new(ExprData::Atom(1)), Box::new(ExprData::Lit(0)))),
                Box::new(ExprData::Lit(0)),
                Box::new(ExprData::BinOp(6, Box::new(ExprData::Atom(1)),
                    Box::new(ExprData::App(20, Box::new(ExprData::Cast(CastKind::IntToNat,
                        Box::new(ExprData::BinOp(7, Box::new(ExprData::Atom(1)), Box::new(ExprData::Lit(1)))))))))))
        ) == 1,
        // kill: then/else branches swapped.
        expr_eq(
            render_exp(RawExp::Ite(TypData::TyNat,
                Box::new(RawExp::BinOp(0, TypData::TyBool,
                    Box::new(RawExp::Var(1, TypData::TyNat)), Box::new(RawExp::Lit(0, TypData::TyNat)))),
                Box::new(RawExp::Lit(0, TypData::TyNat)),
                Box::new(RawExp::Var(1, TypData::TyNat)))),
            ExprData::Ite(
                Box::new(ExprData::BinOp(0, Box::new(ExprData::Atom(1)), Box::new(ExprData::Lit(0)))),
                Box::new(ExprData::Atom(1)),        // BUG: then/else swapped
                Box::new(ExprData::Lit(0)))
        ) == 0,
        // ── Match — `tree_head(t) = match t {Leaf v => v, Node _ _ => 0}` ──
        expr_eq(
            render_exp(RawExp::MatchR(
                Box::new(RawExp::Var(3, TypData::TyNamed(100))),
                Box::new(RawArmList::Cons(30, BinderIdList::Cons(2, Box::new(BinderIdList::Nil)),
                    Box::new(RawExp::Var(2, TypData::TyInt)),
                    Box::new(RawArmList::Cons(31,
                        BinderIdList::Cons(5, Box::new(BinderIdList::Cons(6, Box::new(BinderIdList::Nil)))),
                        Box::new(RawExp::Lit(0, TypData::TyInt)),
                        Box::new(RawArmList::Nil))))),
                TypData::TyInt)),
            ExprData::Match(Box::new(ExprData::Atom(3)),
                Box::new(ArmList::Cons(30, BinderIdList::Cons(2, Box::new(BinderIdList::Nil)),
                    Box::new(ExprData::Atom(2)),
                    Box::new(ArmList::Cons(31,
                        BinderIdList::Cons(5, Box::new(BinderIdList::Cons(6, Box::new(BinderIdList::Nil)))),
                        Box::new(ExprData::Lit(0)),
                        Box::new(ArmList::Nil))))))
        ) == 1,
        // kill: Leaf-arm binder id 2 → 99 (body still reads Atom(2)); §7 Q1 —
        // arm binder ids are part of structural equality.
        expr_eq(
            render_exp(RawExp::MatchR(
                Box::new(RawExp::Var(3, TypData::TyNamed(100))),
                Box::new(RawArmList::Cons(30, BinderIdList::Cons(2, Box::new(BinderIdList::Nil)),
                    Box::new(RawExp::Var(2, TypData::TyInt)),
                    Box::new(RawArmList::Nil))),
                TypData::TyInt)),
            ExprData::Match(Box::new(ExprData::Atom(3)),
                Box::new(ArmList::Cons(30, BinderIdList::Cons(99, Box::new(BinderIdList::Nil)),  // BUG: binder 2→99
                    Box::new(ExprData::Atom(2)),
                    Box::new(ArmList::Nil))))
        ) == 0,
        // ── Match (self-recursive) + Box-Deref — `Tree.height` Node arm
        //    `1 + Tree.height val0.deref + Tree.height val1.deref`. §7 Q2: the
        //    App(height) callee is never reduced (def_eq is syntactic). ──
        expr_eq(
            render_exp(RawExp::MatchR(
                Box::new(RawExp::Var(4, TypData::TyNamed(100))),
                Box::new(RawArmList::Cons(30, BinderIdList::Cons(99, Box::new(BinderIdList::Nil)),
                    Box::new(RawExp::Lit(1, TypData::TyNat)),
                    Box::new(RawArmList::Cons(31,
                        BinderIdList::Cons(7, Box::new(BinderIdList::Cons(8, Box::new(BinderIdList::Nil)))),
                        Box::new(RawExp::BinOp(6, TypData::TyNat,
                            Box::new(RawExp::BinOp(6, TypData::TyNat,
                                Box::new(RawExp::Lit(1, TypData::TyNat)),
                                Box::new(RawExp::Call(23, TypData::TyNat,
                                    Box::new(RawExp::Deref(Box::new(RawExp::Var(7, TypData::TyBox(100))))),
                                    TypData::TyNamed(100))))),
                            Box::new(RawExp::Call(23, TypData::TyNat,
                                Box::new(RawExp::Deref(Box::new(RawExp::Var(8, TypData::TyBox(100))))),
                                TypData::TyNamed(100))))),
                        Box::new(RawArmList::Nil))))),
                TypData::TyNat)),
            ExprData::Match(Box::new(ExprData::Atom(4)),
                Box::new(ArmList::Cons(30, BinderIdList::Cons(99, Box::new(BinderIdList::Nil)),
                    Box::new(ExprData::Lit(1)),
                    Box::new(ArmList::Cons(31,
                        BinderIdList::Cons(7, Box::new(BinderIdList::Cons(8, Box::new(BinderIdList::Nil)))),
                        Box::new(ExprData::BinOp(6,
                            Box::new(ExprData::BinOp(6, Box::new(ExprData::Lit(1)),
                                Box::new(ExprData::App(23, Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(7)), 0)))))),
                            Box::new(ExprData::App(23, Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(8)), 0)))))),
                        Box::new(ArmList::Nil))))))
        ) == 1,
        // kill: Leaf measure 1 → 0.
        expr_eq(
            render_exp(RawExp::MatchR(
                Box::new(RawExp::Var(4, TypData::TyNamed(100))),
                Box::new(RawArmList::Cons(30, BinderIdList::Cons(99, Box::new(BinderIdList::Nil)),
                    Box::new(RawExp::Lit(1, TypData::TyNat)),
                    Box::new(RawArmList::Nil))),
                TypData::TyNat)),
            ExprData::Match(Box::new(ExprData::Atom(4)),
                Box::new(ArmList::Cons(30, BinderIdList::Cons(99, Box::new(BinderIdList::Nil)),
                    Box::new(ExprData::Lit(0)),          // BUG: Leaf => 0, not 1
                    Box::new(ArmList::Nil))))
        ) == 0,
        // ── AppN — `g a b` (synthetic; §7 Q3 flat arg list; A7: per-arg
        //    expected typs carried — Nat/Nat here, so passthrough) ──
        expr_eq(
            render_exp(RawExp::CallN(24, TypData::TyNat,
                Box::new(RawList::Cons(Box::new(RawExp::Var(9, TypData::TyNat)), TypData::TyNat,
                    Box::new(RawList::Cons(Box::new(RawExp::Var(10, TypData::TyNat)), TypData::TyNat,
                        Box::new(RawList::Nil))))))),
            ExprData::AppN(24, Box::new(ExprList::Cons(Box::new(ExprData::Atom(9)),
                Box::new(ExprList::Cons(Box::new(ExprData::Atom(10)), Box::new(ExprList::Nil))))))
        ) == 1,
        // kill: args swapped.
        expr_eq(
            render_exp(RawExp::CallN(24, TypData::TyNat,
                Box::new(RawList::Cons(Box::new(RawExp::Var(9, TypData::TyNat)), TypData::TyNat,
                    Box::new(RawList::Cons(Box::new(RawExp::Var(10, TypData::TyNat)), TypData::TyNat,
                        Box::new(RawList::Nil))))))),
            ExprData::AppN(24, Box::new(ExprList::Cons(Box::new(ExprData::Atom(10)),  // BUG: swapped
                Box::new(ExprList::Cons(Box::new(ExprData::Atom(9)), Box::new(ExprList::Nil))))))
        ) == 0,
        // ── Forall — `∀ k : Nat, k = k` (synthetic) ──
        expr_eq(
            render_exp(RawExp::ForallR(15, TypData::TyNat,
                Box::new(RawExp::BinOp(0, TypData::TyBool,
                    Box::new(RawExp::Var(15, TypData::TyNat)), Box::new(RawExp::Var(15, TypData::TyNat)))))),
            ExprData::Forall(15, TypData::TyNat,
                Box::new(ExprData::BinOp(0, Box::new(ExprData::Atom(15)), Box::new(ExprData::Atom(15)))))
        ) == 1,
        // kill: binder type Nat → Int.
        expr_eq(
            render_exp(RawExp::ForallR(15, TypData::TyNat,
                Box::new(RawExp::BinOp(0, TypData::TyBool,
                    Box::new(RawExp::Var(15, TypData::TyNat)), Box::new(RawExp::Var(15, TypData::TyNat)))))),
            ExprData::Forall(15, TypData::TyInt,          // BUG: binder Nat→Int
                Box::new(ExprData::BinOp(0, Box::new(ExprData::Atom(15)), Box::new(ExprData::Atom(15)))))
        ) == 0
by { decide }

// A7 (bootstrap-80 F3): in-crate kernel-computation guard for
// `reconcile_arg` — the per-arg slot reconciliation derived from the
// (actual, expected) pair. The three live divergence shapes from the
// frozen step-0 evidence, each correct-closes to 1 + a kill flips to 0.
proof fn a7_reconcile_kernel_computes()
    ensures
        // vec_read View case: arg `v : TyRef(14)`, `View.view`'s param IS
        // ref-typed (expected TyRef(14)) → PASSTHROUGH (the G2 bug was
        // deriving `v.deref` here). Kill = the old mis-derivation.
        expr_eq(
            render_exp(RawExp::Call(12, TypData::TyNamed(13),
                Box::new(RawExp::Var(0, TypData::TyRef(14))),
                TypData::TyRef(14))),
            ExprData::App(12, Box::new(ExprData::Atom(0)))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Call(12, TypData::TyNamed(13),
                Box::new(RawExp::Var(0, TypData::TyRef(14))),
                TypData::TyRef(14))),
            ExprData::App(12, Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(0)), 0)))  // BUG: spurious .deref
        ) == 0,
        // vec_push7 View case: arg `v : TyNamed(12)` (the &mut final value
        // at the POINTEE), `View.view`'s param is ref-typed → the
        // `Tactus.Ref.mk v` WRAP (first-class node, no interned id).
        // Kill = wrap dropped.
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(10),
                Box::new(RawExp::Var(0, TypData::TyNamed(12))),
                TypData::TyRef(12))),
            ExprData::App(11, Box::new(ExprData::RefMk(Box::new(ExprData::Atom(0)))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Call(11, TypData::TyNamed(10),
                Box::new(RawExp::Var(0, TypData::TyNamed(12))),
                TypData::TyRef(12))),
            ExprData::App(11, Box::new(ExprData::Atom(0)))  // BUG: RefMk dropped
        ) == 0,
        // Seq.index case: CallN whose 2nd arg is Nat under an Int param →
        // the `Int.ofNat` cast, DERIVED per-arg (the "deferred to W7c"
        // gap); 1st arg (Nat under Nat) passes through. Kill = cast
        // dropped.
        expr_eq(
            render_exp(RawExp::CallN(15, TypData::TyInt,
                Box::new(RawList::Cons(Box::new(RawExp::Var(9, TypData::TyNat)), TypData::TyNat,
                    Box::new(RawList::Cons(Box::new(RawExp::Var(10, TypData::TyNat)), TypData::TyInt,
                        Box::new(RawList::Nil))))))),
            ExprData::AppN(15, Box::new(ExprList::Cons(Box::new(ExprData::Atom(9)),
                Box::new(ExprList::Cons(
                    Box::new(ExprData::Cast(CastKind::NatToInt, Box::new(ExprData::Atom(10)))),
                    Box::new(ExprList::Nil))))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::CallN(15, TypData::TyInt,
                Box::new(RawList::Cons(Box::new(RawExp::Var(9, TypData::TyNat)), TypData::TyNat,
                    Box::new(RawList::Cons(Box::new(RawExp::Var(10, TypData::TyNat)), TypData::TyInt,
                        Box::new(RawList::Nil))))))),
            ExprData::AppN(15, Box::new(ExprList::Cons(Box::new(ExprData::Atom(9)),
                Box::new(ExprList::Cons(Box::new(ExprData::Atom(10)),  // BUG: ofNat dropped
                    Box::new(ExprList::Nil))))))
        ) == 0,
        // Ref↔Box at equal depth: peel + rewrap (production's kind-mismatch
        // arm); reverse Int→Nat direction (toNat).
        expr_eq(
            render_exp(RawExp::Call(23, TypData::TyNat,
                Box::new(RawExp::Var(7, TypData::TyBox(100))),
                TypData::TyRef(100))),
            ExprData::App(23, Box::new(ExprData::RefMk(
                Box::new(ExprData::FieldProj(Box::new(ExprData::Atom(7)), 0)))))
        ) == 1,
        expr_eq(
            render_exp(RawExp::Call(20, TypData::TyNat,
                Box::new(RawExp::Var(1, TypData::TyInt)),
                TypData::TyNat)),
            ExprData::App(20, Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(1)))))
        ) == 1,
        // RefMk/BoxMk tag separation (Ref ≠ Box).
        expr_eq(ExprData::RefMk(Box::new(ExprData::Atom(0))),
                ExprData::BoxMk(Box::new(ExprData::Atom(0)))) == 0
by { decide }

// W7: in-crate kernel-computation guard for the DEF-HEADER layer — pins
// `render_def`/`render_dt` + `def_eq`/`dt_eq` (and the `param_list_eq`/
// `typ_list_eq`/`ctor_list_eq` list eqs) against the landed code. A def with a
// self-recursive App body (§7 Q2: `def_eq` is syntactic — the App(20) callee is
// compared as a node, never unfolded) + the REAL `Tree` datatype (§7 Q4: the
// Box-vs-Int positional-field kill). Each correct=1 + mutation=0, decide-reducible.
proof fn defs_mirror_kernel_computes()
    ensures
        // def_eq: header + self-recursive body `f(n) = n + f(n)` (name 20,
        // param (1:Nat), ret Nat). render_def copies the header, renders the
        // body via render_exp; the App(20) callee is NOT reduced.
        def_eq(
            render_def(RawDef {
                name: 20,
                params: ParamList::Cons(1, TypData::TyNat, Box::new(ParamList::Nil)),
                ret: TypData::TyNat,
                body: RawExp::BinOp(6, TypData::TyNat,
                    Box::new(RawExp::Var(1, TypData::TyNat)),
                    Box::new(RawExp::Call(20, TypData::TyNat,
                        Box::new(RawExp::Var(1, TypData::TyNat)), TypData::TyNat))),
            }),
            DefData {
                name: 20,
                params: ParamList::Cons(1, TypData::TyNat, Box::new(ParamList::Nil)),
                ret: TypData::TyNat,
                body: ExprData::BinOp(6, Box::new(ExprData::Atom(1)),
                    Box::new(ExprData::App(20, Box::new(ExprData::Atom(1))))),
            }
        ) == 1,
        // kill: wrong PARAM TYPE (Nat → Int) — the typed-param bug (§7 Q4).
        def_eq(
            render_def(RawDef {
                name: 20,
                params: ParamList::Cons(1, TypData::TyNat, Box::new(ParamList::Nil)),
                ret: TypData::TyNat,
                body: RawExp::Var(1, TypData::TyNat),
            }),
            DefData {
                name: 20,
                params: ParamList::Cons(1, TypData::TyInt, Box::new(ParamList::Nil)),  // BUG: Nat→Int
                ret: TypData::TyNat,
                body: ExprData::Atom(1),
            }
        ) == 0,
        // kill: wrong BODY (recursive call dropped) — the App(20) present in the
        // reference, an Atom in the mutation.
        def_eq(
            render_def(RawDef {
                name: 20,
                params: ParamList::Cons(1, TypData::TyNat, Box::new(ParamList::Nil)),
                ret: TypData::TyNat,
                body: RawExp::BinOp(6, TypData::TyNat,
                    Box::new(RawExp::Var(1, TypData::TyNat)),
                    Box::new(RawExp::Call(20, TypData::TyNat,
                        Box::new(RawExp::Var(1, TypData::TyNat)), TypData::TyNat))),
            }),
            DefData {
                name: 20,
                params: ParamList::Cons(1, TypData::TyNat, Box::new(ParamList::Nil)),
                ret: TypData::TyNat,
                body: ExprData::BinOp(6, Box::new(ExprData::Atom(1)),
                    Box::new(ExprData::Atom(1))),   // BUG: recursive App dropped
            }
        ) == 0,
        // dt_eq: the REAL `Tree = Leaf(Int) | Node(Box Tree, Box Tree)`.
        dt_eq(
            render_dt(RawDt {
                name: 100,
                ctors: CtorList::Cons(30, TypList::Cons(TypData::TyInt, Box::new(TypList::Nil)),
                    Box::new(CtorList::Cons(31,
                        TypList::Cons(TypData::TyBox(100), Box::new(TypList::Cons(TypData::TyBox(100), Box::new(TypList::Nil)))),
                        Box::new(CtorList::Nil)))),
            }),
            DtData {
                name: 100,
                ctors: CtorList::Cons(30, TypList::Cons(TypData::TyInt, Box::new(TypList::Nil)),
                    Box::new(CtorList::Cons(31,
                        TypList::Cons(TypData::TyBox(100), Box::new(TypList::Cons(TypData::TyBox(100), Box::new(TypList::Nil)))),
                        Box::new(CtorList::Nil)))),
            }
        ) == 1,
        // kill: Leaf field Int → Box<Tree> (the Box-vs-Int / positional-field kill).
        dt_eq(
            render_dt(RawDt {
                name: 100,
                ctors: CtorList::Cons(30, TypList::Cons(TypData::TyInt, Box::new(TypList::Nil)),
                    Box::new(CtorList::Nil)),
            }),
            DtData {
                name: 100,
                ctors: CtorList::Cons(30, TypList::Cons(TypData::TyBox(100), Box::new(TypList::Nil)),  // BUG: Int→Box
                    Box::new(CtorList::Nil)),
            }
        ) == 0
by { decide }

// ── In-crate kernel-computation sanity (decide через structural) ────

proof fn skeleton_kernel_computes()
    ensures
        stm_size(StmData::Seq(
            Box::new(StmData::Assert(atom_ob(0), 0, 0)),
            Box::new(StmData::If(1, 0, 2, 0, Box::new(StmData::Skip), Box::new(StmData::Ret(Box::new(RawExpList::Nil), RetBind::RetNone)))),
        )) == 5,
        goal_size(GoalData::Imp(7, Box::new(GoalData::All(8, 9, Box::new(GoalData::Leaf(10)))))) == 3,
        leaf_len(LeafList::Cons(1, Box::new(LeafList::Cons(2, Box::new(LeafList::Nil))))) == 2
by {
    decide
}

proof fn seq_size_unfolds()
    ensures
        stm_size(StmData::Seq(Box::new(StmData::Skip), Box::new(StmData::Skip))) ==
            1 + stm_size(StmData::Skip) + stm_size(StmData::Skip),
        goal_count(GoalList::Cons(
            Box::new(GoalData::Leaf(0)),
            Box::new(GoalList::Cons(Box::new(GoalData::Leaf(1)), Box::new(GoalList::Nil))),
        )) == 2
by {
    decide
}

// N2.1: the amended shapes kernel-compute (If/Loop/Call/Ret + the new
// BinderList/ParamBoundList/FrameList/FnCtxData vocabulary).
// ── W2a: the reference WP (refWp) and its first-order workers ───────
// DESIGN-W2-refwp.md §2. These emitted defs ARE the checker the
// certificate runs. Authored snake_case (file convention); the DESIGN
// names map as: close, frame_after=`frameAfter`, wp_stm=`wpStm`,
// ref_wp=`refWp`, goal_eq/goals_eq. Every recursive worker is single-
// datatype structural recursion (no spec_fn continuations — closures are
// trigger/kernel-hostile, memory: closure-identity arc) with
// `#[verifier::structural_decreases]` so the defs kernel-compute.
//
// Shape decisions (grounded in the on-disk fixture certs — see the W2a
// board writeup for the full empirical read):
//  * The frame IS the goal spine (DESIGN §2.1): `close` folds it entry-
//    by-entry around one obligation leaf. First (outermost) frame entry =
//    outermost GoalData constructor.
//  * `StmData::Assert(oblig, hyp)` emits `close(frame, oblig)` (the
//    ANNOTATED obligation leaf, finding-1) AND `frame_after` adds forward
//    hyp `hyp` (the BARE prop leaf): the fixture certs show TWO `Imp <bare>`
//    after an Assert/Assume pair — the Assert's bare forward hyp plus the
//    following Assume's hyp — while the goal uses the span_mark'd obligation.
//  * Signature bound-hyps and requires render as NAMED ∀-binders
//    (`All 19 2` = ∀ (h_x_bound : …), `All 17 5` = ∀ (h_req0 : …)), NOT
//    arrows (finding-2, LANDED). `ParamBoundList::Bound` now carries the
//    `h_<param>_bound` name leaf and `FnCtxData.reqs` is a `BinderList` of
//    (h_req<i>, prop); seed_params/seed_frame fold both via `FBind` → `All`.

// Concatenate two frames (structural on the first).
#[verifier::structural_decreases]
pub open spec fn frame_append(f: FrameList, g: FrameList) -> FrameList
    decreases f
{
    match f {
        FrameList::FNil => g,
        FrameList::FBind(id, typ, t) => FrameList::FBind(id, typ, Box::new(frame_append(*t, g))),
        FrameList::FHyp(hn, h, t) => FrameList::FHyp(hn, h, Box::new(frame_append(*t, g))),
        FrameList::FLetH(x, ty, v, en, ep, t) => FrameList::FLetH(x, ty, v, en, ep, Box::new(frame_append(*t, g))),
        FrameList::FLet(id, v, t) => FrameList::FLet(id, v, Box::new(frame_append(*t, g))),
        FrameList::FLetR(id, v, t) => FrameList::FLetR(id, v, Box::new(frame_append(*t, g))),
        FrameList::FUserCloser(t) => FrameList::FUserCloser(Box::new(frame_append(*t, g))),
    }
}

// A LeafList rendered as a chain of anonymous FHyp entries.
#[verifier::structural_decreases]
pub open spec fn hyps_of_leaves(l: LeafList) -> FrameList
    decreases l
{
    match l {
        LeafList::Nil => FrameList::FNil,
        LeafList::Cons(h, t) => FrameList::FHyp(0, h, Box::new(hyps_of_leaves(*t))),
    }
}

// A BinderList rendered as a chain of FBind entries.
#[verifier::structural_decreases]
pub open spec fn binders_to_frame(b: BinderList) -> FrameList
    decreases b
{
    match b {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => FrameList::FBind(id, typ, Box::new(binders_to_frame(*t))),
    }
}

// Fold a frame around an obligation leaf → one GoalData spine.
#[verifier::structural_decreases]
pub open spec fn close(f: FrameList, obligation: u64) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => GoalData::Leaf(obligation),
        FrameList::FBind(id, typ, t) => GoalData::All(id, typ, Box::new(close(*t, obligation))),
        FrameList::FHyp(_hn, h, t) => GoalData::Imp(h, Box::new(close(*t, obligation))),
        FrameList::FLetH(id, _ty, v, _en, _ep, t) => GoalData::Let(id, v, Box::new(close(*t, obligation))),
        FrameList::FLet(id, v, t) => GoalData::Let(id, v, Box::new(close(*t, obligation))),
        FrameList::FLetR(id, v, t) => GoalData::Let(id, v, Box::new(close(*t, obligation))),
        FrameList::FUserCloser(t) => close(*t, obligation),
    }
}

// W6d.1b: fold a frame around a DEEP obligation `RawExp` → one GoalData
// spine terminating in the RENDERED leaf `LeafE(render_exp(ob))`. Mirrors
// `close` entry-for-entry (same All/Imp/Let spine); only the terminal
// differs — the opaque `Leaf(u64)` becomes the structural `LeafE(ExprData)`.
// The obligation-emitting `wp_stm` arms switch to this so the production
// side's `LeafE(ExprData)` matches the reference constructor-for-constructor
// (the architecture decision: a symmetric deepen is FORCED — `goals_eq`
// compares `LeafE` against `LeafE`, never `LeafE` against `Leaf`).
#[verifier::structural_decreases]
// The N1 wrap gate, first half (bootstrap-74): production's `hoist_all`
// returns None — whole goal renders old-style — iff ANY let frame is
// typ-less (or a hoistable-but-poisoned let, which the serializer
// collapses to plain FLet losslessly). The mirror: any plain `FLet` in
// the list. nat-valued (1 = a plain FLet is present), NOT bool: the
// dispatchers branch on `== 1`, which emits with Nat.decEq and stays
// kernel-computable for `decide` (the file's has_let/binder_has_id
// idiom — a bool gate emits Classical.propDecidable and sticks).
// A RESIDUE let (`FLetR`) is NOT plain — it never forces wrap.
#[verifier::structural_decreases]
pub open spec fn has_plain_flet(f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_x, _ty, t) => has_plain_flet(*t),
        FrameList::FHyp(_n, _h, t) => has_plain_flet(*t),
        FrameList::FLet(_x, _v, _t) => 1,
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => has_plain_flet(*t),
        FrameList::FLetR(_x, _v, t) => has_plain_flet(*t),
        FrameList::FUserCloser(t) => has_plain_flet(*t),
    }
}

// F4 (bootstrap-80 stage 2): the poison derivation. `leaf_mem` is the
// `binder_has_id` idiom for the LeafList world (nat-valued, never bool —
// the finding-5 decide idiom).
#[verifier::structural_decreases]
pub open spec fn leaf_mem(l: LeafList, x: u64) -> nat
    decreases l
{
    match l {
        LeafList::Nil => 0,
        LeafList::Cons(h, t) => if h == x { 1 } else { leaf_mem(*t, x) },
    }
}

// Does the deep transcription mention any residue name? Dumb textual
// scan over `Var` atoms — binders (Let/ForallR/ExistsR) do NOT shadow,
// exactly mirroring production's `lexpr_mentions_var` (residue names are
// gensym-unique fn-level lets, so no well-formed prop re-binds one).
// Structural (each call on a subterm) so the kernel reduces it under
// `decide`; mutually recursive with the arm/arg-list twins exactly like
// `render_exp`/`render_arms`/`render_list`.
#[verifier::structural_decreases]
pub open spec fn raw_exp_mentions(rs: LeafList, e: RawExp) -> nat
    decreases e
{
    match e {
        RawExp::Var(id, _ty) => leaf_mem(rs, id),
        RawExp::Lit(_v, _ty) => 0,
        RawExp::LitBool(_b) => 0,
        RawExp::Clip(_t, a) => raw_exp_mentions(rs, *a),
        RawExp::BinOp(_op, _ty, l, r) =>
            if raw_exp_mentions(rs, *l) == 1 { 1 } else { raw_exp_mentions(rs, *r) },
        RawExp::Call(_f, _ret, a, _aty) => raw_exp_mentions(rs, *a),
        RawExp::Field(_fid, _fty, a) => raw_exp_mentions(rs, *a),
        RawExp::HasType(_n, a) => raw_exp_mentions(rs, *a),
        RawExp::Deref(a) => raw_exp_mentions(rs, *a),
        RawExp::Let(_x, v, b) =>
            if raw_exp_mentions(rs, *v) == 1 { 1 } else { raw_exp_mentions(rs, *b) },
        RawExp::Not(a) => raw_exp_mentions(rs, *a),
        RawExp::Span(_l, a) => raw_exp_mentions(rs, *a),
        RawExp::Ite(_ty, c, t, e2) =>
            if raw_exp_mentions(rs, *c) == 1 { 1 }
            else if raw_exp_mentions(rs, *t) == 1 { 1 }
            else { raw_exp_mentions(rs, *e2) },
        RawExp::MatchR(s, arms, _ty) =>
            if raw_exp_mentions(rs, *s) == 1 { 1 } else { raw_arms_mentions(rs, *arms) },
        RawExp::CallN(_f, _ret, args) => raw_list_mentions(rs, *args),
        RawExp::ForallR(_b, _bty, body) => raw_exp_mentions(rs, *body),
        RawExp::ExistsR(_b, _bty, body) => raw_exp_mentions(rs, *body),
    }
}

#[verifier::structural_decreases]
pub open spec fn raw_arms_mentions(rs: LeafList, a: RawArmList) -> nat
    decreases a
{
    match a {
        RawArmList::Nil => 0,
        RawArmList::Cons(_c, _bs, body, tl) =>
            if raw_exp_mentions(rs, *body) == 1 { 1 } else { raw_arms_mentions(rs, *tl) },
    }
}

#[verifier::structural_decreases]
pub open spec fn raw_list_mentions(rs: LeafList, l: RawList) -> nat
    decreases l
{
    match l {
        RawList::Nil => 0,
        RawList::Cons(h, _expected, t) =>
            if raw_exp_mentions(rs, *h) == 1 { 1 } else { raw_list_mentions(rs, *t) },
    }
}

// The derived poison set: the prop ids whose deep transcription mentions
// a residue name. Computed ONCE at `ref_wp` and threaded as the single
// poison source — the wrap gate (`has_poisoned_hyp`) and the FLetH/RetLetH
// collapse are membership checks against it. A prop id with NO table
// entry derives 0 (not a member): loud-by-bridge in the divergence
// direction (production wrapped on a real mention, we hoist → the goal
// shapes diverge), correct-by-luck in the other; totality loudness rests
// on the serializer's emission-time assertion (b80 card, review addendum).
// The ctx-level entry `poisoned_props` takes the WHOLE FnCtxData (not the
// two field projections) so the Link discharge's wf-transport — which
// resolves own-param args, not `<param>.<field>` projections — can feed
// its preservation lemma (b80 stage-2 landing evidence).
#[verifier::structural_decreases]
pub open spec fn poisoned_props_of(rs: LeafList, ds: PropDeepList) -> LeafList
    decreases ds
{
    match ds {
        PropDeepList::Nil => LeafList::Nil,
        PropDeepList::Cons(id, deep, t) =>
            if raw_exp_mentions(rs, *deep) == 1 {
                LeafList::Cons(id, Box::new(poisoned_props_of(rs, *t)))
            } else {
                poisoned_props_of(rs, *t)
            },
    }
}

pub open spec fn poisoned_props(c: FnCtxData) -> LeafList {
    poisoned_props_of(c.residue_names, c.prop_deeps)
}

// The N1 wrap gate, second half (bootstrap-74 slice 2): any POISONED
// hyp — a prop whose text mentions a residue-let name — forces
// whole-goal wrap (production's `hoist_all` bail check on binder types
// mentioning residue names). F4 (bootstrap-80 stage 2): the mark is
// DERIVED — `pp` is the `poisoned_props` set computed once at `ref_wp`;
// the FHyp bit slot is unread here (era 1; deleted era 2). Same nat
// idiom.
#[verifier::structural_decreases]
pub open spec fn has_poisoned_hyp(pp: LeafList, f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_x, _ty, t) => has_poisoned_hyp(pp, *t),
        FrameList::FHyp(_n, h, t) => if leaf_mem(pp, h) == 1 { 1 } else { has_poisoned_hyp(pp, *t) },
        FrameList::FLet(_x, _v, t) => has_poisoned_hyp(pp, *t),
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => has_poisoned_hyp(pp, *t),
        FrameList::FLetR(_x, _v, t) => has_poisoned_hyp(pp, *t),
        FrameList::FUserCloser(t) => has_poisoned_hyp(pp, *t),
    }
}

// The N1 wrap gate, third half (R1, bootstrap-77): a non-default-closer
// marker anywhere in the frame forces whole-goal wrap — production's
// `emit_split` `is_default` check / `emit_with_closer`'s unconditional
// wrap path. Same nat idiom.
#[verifier::structural_decreases]
pub open spec fn has_user_closer(f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_x, _ty, t) => has_user_closer(*t),
        FrameList::FHyp(_n, _h, t) => has_user_closer(*t),
        FrameList::FLet(_x, _v, t) => has_user_closer(*t),
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => has_user_closer(*t),
        FrameList::FLetR(_x, _v, t) => has_user_closer(*t),
        FrameList::FUserCloser(_t) => 1,
    }
}

// The combined wrap gate: the whole goal renders old-style (wrap) iff
// any frame forces it — a plain FLet (typ-less/poison-collapsed let), a
// poisoned hyp, or a non-default-closer marker (R1). Mirrors
// `hoist_all` returning None / `emit_split`'s `is_default` guard.
pub open spec fn gate_wrap(pp: LeafList, f: FrameList) -> nat {
    if has_plain_flet(f) == 1 || has_poisoned_hyp(pp, f) == 1 || has_user_closer(f) == 1 { 1 } else { 0 }
}

// Wrap-mode rendering (production's goal-position wrap — the pre-N1
// shape, still used whenever the gate trips): hyps are anonymous
// implications, lets (all three kinds) are goal-position Lets.
#[verifier::structural_decreases]
pub open spec fn close_e_wrap(f: FrameList, ob: RawExp) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => GoalData::LeafE(render_exp(ob)),
        FrameList::FBind(id, typ, t) => GoalData::All(id, typ, Box::new(close_e_wrap(*t, ob))),
        FrameList::FHyp(_hn, h, t) => GoalData::Imp(h, Box::new(close_e_wrap(*t, ob))),
        FrameList::FLet(id, v, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FLetH(id, _ty, v, _en, _ep, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FLetR(id, v, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FUserCloser(t) => close_e_wrap(*t, ob),
    }
}

// S3-pre leading sub-mode: production's `split_leading_binders` extracts
// the leading Binder/Hyp PREFIX of every wrap-mode goal to theorem-level
// binders — a pure prefix latch that stops at the first let-class frame
// (base binders always precede the frames, so there is no seed/body
// boundary to distinguish). Leading FBind/FHyp render as NAMED All
// binders (the FBind-encoding; the FHyp's hn field carries the
// serializer-interned `_h_hoist_k` name, which coincides with
// production's per-goal 1-based counter because the extracted prefix
// contains no lets); the first let-class frame latches ONE-WAY to the
// plain wrap rendering (`close_e_wrap` — hyps back to anonymous Imp).
// FUserCloser is transparent (a serializer sentinel, not a frame
// production's splitter sees).
#[verifier::structural_decreases]
pub open spec fn close_e_wrap_lead(f: FrameList, ob: RawExp) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => GoalData::LeafE(render_exp(ob)),
        FrameList::FBind(id, typ, t) => GoalData::All(id, typ, Box::new(close_e_wrap_lead(*t, ob))),
        FrameList::FHyp(hn, h, t) => GoalData::All(hn, h, Box::new(close_e_wrap_lead(*t, ob))),
        FrameList::FLet(id, v, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FLetH(id, _ty, v, _en, _ep, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FLetR(id, v, t) => GoalData::Let(id, v, Box::new(close_e_wrap(*t, ob))),
        FrameList::FUserCloser(t) => close_e_wrap_lead(*t, ob),
    }
}

// Hoist-mode rendering (production's hoist_all), TWO-PHASE exactly as
// production builds it: phase 1 (`close_e_tel`) folds every non-residue
// frame into the theorem-level binder telescope — hyps NAMED
// (`All(name, prop)`, the finding-2 FBind-encoding), hoistable lets the
// pair `All(x, typ) ∘ All(eq_name, eq_prop)` — SKIPPING residue lets;
// phase 2 (`residue_fold_e`) folds the residue (Bool) lets as
// goal-position `Let`s around the leaf, frame order (the earliest
// residue let is outermost, matching production's `.rev()` fold). A
// plain FLet cannot occur under the gate; its arm renders Let for
// totality (unreachable when dispatched).
#[verifier::structural_decreases]
pub open spec fn close_e_tel(f: FrameList, g: GoalData) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => g,
        FrameList::FBind(id, typ, t) => GoalData::All(id, typ, Box::new(close_e_tel(*t, g))),
        FrameList::FHyp(hn, h, t) => GoalData::All(hn, h, Box::new(close_e_tel(*t, g))),
        FrameList::FLet(id, v, t) => GoalData::Let(id, v, Box::new(close_e_tel(*t, g))),
        FrameList::FLetH(id, ty, _v, en, ep, t) =>
            GoalData::All(id, ty, Box::new(GoalData::All(en, ep, Box::new(close_e_tel(*t, g))))),
        FrameList::FLetR(_id, _v, t) => close_e_tel(*t, g),
        // Unreachable when dispatched (a FUserCloser trips the gate to
        // wrap mode); skipped for totality.
        FrameList::FUserCloser(t) => close_e_tel(*t, g),
    }
}

#[verifier::structural_decreases]
pub open spec fn residue_fold_e(f: FrameList, g: GoalData) -> GoalData
    decreases f
{
    match f {
        FrameList::FNil => g,
        FrameList::FLetR(id, v, t) => GoalData::Let(id, v, Box::new(residue_fold_e(*t, g))),
        FrameList::FBind(_id, _typ, t) => residue_fold_e(*t, g),
        FrameList::FHyp(_hn, _h, t) => residue_fold_e(*t, g),
        FrameList::FLet(_id, _v, t) => residue_fold_e(*t, g),
        FrameList::FLetH(_id, _ty, _v, _en, _ep, t) => residue_fold_e(*t, g),
        FrameList::FUserCloser(t) => residue_fold_e(*t, g),
    }
}

pub open spec fn close_e_hoist(f: FrameList, ob: RawExp) -> GoalData {
    close_e_tel(f, residue_fold_e(f, GoalData::LeafE(render_exp(ob))))
}

// The gated dispatcher — the ONE rendering entry point (all callers
// unchanged). Mode is decided ONCE over the whole frame list, exactly
// as production inspects all frames before hoisting (§hoist_all).
pub open spec fn close_e(pp: LeafList, f: FrameList, ob: RawExp) -> GoalData {
    if gate_wrap(pp, f) == 1 { close_e_wrap_lead(f, ob) } else { close_e_hoist(f, ob) }
}

// W6d.1b: the bare-atom obligation. An obligation leaf that carries no deep
// structure yet (an opaque interned id) rides through the deep path as
// `Var(id, TyBool)`, which `render_exp` maps to `Atom(id)`. So
// `close_e(f, atom_ob(id))` folds the SAME spine as `close(f, id)` but
// terminates in `LeafE(Atom id)` — the shape the deep bridge compares.
// `TyBool` is the honest prop type of an obligation; `render_exp(Var …)`
// ignores the type, so any tag would render identically. Used by the
// fixtures here and (W6d.2) by the serializer wherever the raw SST leaf is
// not yet one of the deepened `RawExp` shapes (G0–G7).
pub open spec fn atom_ob(id: u64) -> RawExp { RawExp::Var(id, TypData::TyBool) }

// W6d.1b-ii: close_e(frame, ·) mapped over a RawExpList → one DEEP goal per
// obligation (Call reqs, Ret enss, and — W6d.1b-iii — Loop init/maintain
// invariants over `inv_obligs`). Each terminal is `LeafE(render_exp(ob))`
// instead of `Leaf(u64)`, so the production side's `LeafE(ExprData)` matches
// the reference constructor-for-constructor. (This is the only per-list
// obligation folder now — the old stage-A `close_each` over `LeafList` and
// `close_each_binderprop` over the `inv_hyps` prop slots were both removed
// when their obligations deepened.)
#[verifier::structural_decreases]
pub open spec fn close_each_e(pp: LeafList, f: FrameList, l: RawExpList) -> GoalList
    decreases l
{
    match l {
        RawExpList::Nil => GoalList::Nil,
        RawExpList::Cons(h, t) => GoalList::Cons(Box::new(close_e(pp, f, *h)), Box::new(close_each_e(pp, f, *t))),
    }
}

// Append two goal lists (the `++` of DESIGN §2.1).
#[verifier::structural_decreases]
pub open spec fn goals_append(a: GoalList, b: GoalList) -> GoalList
    decreases a
{
    match a {
        GoalList::Nil => b,
        GoalList::Cons(h, t) => GoalList::Cons(h, Box::new(goals_append(*t, b))),
    }
}

// ── Loop havoc + binder-prop obligations (finding-3) ────────────────

// Is `x` one of a BinderList's binder ids? (The Loop havoc set membership
// test — decides whether a pre-loop `let x := …` is dropped.) Returns `nat`
// (1 = present, 0 = absent), NOT `bool`: the tactus Lean backend lowers a
// `bool`-returning spec fn to a noncomputable `Prop`, on which `decide`
// gets stuck (finding-5 / decide-checker idiom — same reason `goals_eq`
// returns nat).
#[verifier::structural_decreases]
pub open spec fn binder_has_id(b: BinderList, x: u64) -> nat
    decreases b
{
    match b {
        BinderList::Nil => 0,
        BinderList::Cons(id, _typ, t) => if id == x { 1 } else { binder_has_id(*t, x) },
    }
}

// Loop havoc: production's `push_mod_var_frames` drops any pre-loop
// `let x := …` (and any hyp mentioning x) for a modified local x before
// re-quantifying x with a fresh ∀-binder. refWp mirrors the let-drop
// exactly (the modified-var ids are visible in `binders`). It does NOT
// drop FHyp entries — leaves are opaque ids, so refWp cannot see whether a
// hyp mentions a modified var. That divergence only bites a fixture with a
// pre-loop assert OVER a modified local (an honest fail-to-close, never a
// silent pass — `goals_eq` is a structural equality). Binder frames are
// kept (an outer loop's binders are still in scope).
#[verifier::structural_decreases]
pub open spec fn havoc_lets(f: FrameList, mods: BinderList) -> FrameList
    decreases f
{
    match f {
        FrameList::FNil => FrameList::FNil,
        FrameList::FBind(id, typ, t) => FrameList::FBind(id, typ, Box::new(havoc_lets(*t, mods))),
        FrameList::FHyp(hn, h, t) => FrameList::FHyp(hn, h, Box::new(havoc_lets(*t, mods))),
        FrameList::FLet(id, v, t) =>
            if binder_has_id(mods, id) == 1 {
                havoc_lets(*t, mods)
            } else {
                FrameList::FLet(id, v, Box::new(havoc_lets(*t, mods)))
            },
        FrameList::FLetH(id, ty, v, en, ep, t) =>
            if binder_has_id(mods, id) == 1 {
                havoc_lets(*t, mods)
            } else {
                FrameList::FLetH(id, ty, v, en, ep, Box::new(havoc_lets(*t, mods)))
            },
        FrameList::FLetR(id, v, t) =>
            if binder_has_id(mods, id) == 1 {
                havoc_lets(*t, mods)
            } else {
                FrameList::FLetR(id, v, Box::new(havoc_lets(*t, mods)))
            },
        FrameList::FUserCloser(t) => FrameList::FUserCloser(Box::new(havoc_lets(*t, mods))),
    }
}

// (W6d.1b-iii: `close_each_binderprop` — the stage-A folder over `inv_hyps`'s
// prop slots — was removed when the Loop invariant obligations deepened to the
// parallel `inv_obligs: RawExpList`, folded via `close_each_e`. `inv_hyps` now
// carries only the opaque frame-HYP leaves, consumed by the maintain/use
// telescope; it no longer produces obligation goals.)

// Seed the value-param / loop-binder telescope: each binder immediately
// followed by its own bound hyp (empirical spine `∀x, ∀(h_x_bound), …`).
// Params → FBind; bound hyps → FBind too (finding-2: production renders
// them as NAMED ∀-binders, so `close` folds them into `All`, not `Imp`).
// Loop reuses this for the modified-local havoc set + their `_h_ctx`
// bounds (finding-3). Defined ahead of `frame_after`/`wp_stm` so both the
// use (frameAfter) and maintain (wpStm) loop telescopes can fold it.
#[verifier::structural_decreases]
pub open spec fn seed_params(params: BinderList, bounds: ParamBoundList) -> FrameList
    decreases params
{
    match params {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => match bounds {
            ParamBoundList::Bound(hname, prop, bt) =>
                FrameList::FBind(id, typ, Box::new(FrameList::FBind(hname, prop, Box::new(seed_params(*t, *bt))))),
            ParamBoundList::NoBound(bt) =>
                FrameList::FBind(id, typ, Box::new(seed_params(*t, *bt))),
            ParamBoundList::Nil =>
                FrameList::FBind(id, typ, Box::new(seed_params(*t, ParamBoundList::Nil))),
        },
    }
}

// ── Nested-loop (non-leading) telescope support (bootstrap-16) ───────
//
// Production names a loop's mod-var bounds / invariants / condition as
// `_h_ctx_N` ∀-hyps ONLY when the loop's frames are LEADING —
// `split_leading_binders` (sst_to_lean) hoists a prefix of Binder/Hyp
// frames from the front of the accumulated context, STOPPING at the
// first `let`. An enclosing loop pushes a `_tactus_d_old := D` `let`
// frame (walk_loop), so a NESTED (inner) loop's bounds/invs/cond come
// AFTER that let → they are NOT leading → production renders them as
// bare (unnamed) `Imp` hypotheses, while the mod-var ∀-binders themselves
// keep their source names. refWp re-derives leading-ness from the
// pre-loop frame `f` after havoc drops the modified locals' own pre-loop
// lets: LEADING iff no `let` survives in front. Ground truth: the
// find_square inner loop's maintain telescope (goal 5) is
// `All 23 1, Imp 24, Imp 25, Imp 26, Imp 27, Imp 29` — an ∀ over `b`
// then FIVE bare `Imp`s (b-bound, three invs, cond), not named ∀-hyps.
// (The prior instance's "`_h_ctx` counter offset" read was imprecise:
// the inner hyps are UNNAMED, not renamed with a shifted counter.)

// Does the frame contain any surviving `let` binder? After havoc, a
// surviving `let` = an enclosing loop's `_tactus_d_old` snapshot (or a
// non-modified pre-loop local) ⇒ this loop's leading-binder extraction
// already stopped ⇒ its hyps render as bare `Imp`. Returns nat (the
// `decide` idiom — a bool spec fn lowers to a noncomputable Prop).
#[verifier::structural_decreases]
pub open spec fn has_let(f: FrameList) -> nat
    decreases f
{
    match f {
        FrameList::FNil => 0,
        FrameList::FBind(_id, _typ, t) => has_let(*t),
        FrameList::FHyp(_hn, _h, t) => has_let(*t),
        FrameList::FLet(_id, _v, _t) => 1,
        FrameList::FLetH(_id, _ty, _v, _en, _ep, _t) => 1,
        FrameList::FLetR(_id, _v, _t) => 1,
        FrameList::FUserCloser(t) => has_let(*t),
    }
}

// A BinderList's PROP slots as anonymous `FHyp` entries — the
// non-leading counterpart of `binders_to_frame`. Each invariant's
// ANNOTATED obligation leaf (the prop slot) becomes a bare `Imp`
// hypothesis; the `_h_ctx` name slot is dropped (unnamed).
#[verifier::structural_decreases]
pub open spec fn binderprops_to_hyps(b: BinderList) -> FrameList
    decreases b
{
    match b {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(name, prop, t) => FrameList::FHyp(name, prop, Box::new(binderprops_to_hyps(*t))),
    }
}

// The non-leading counterpart of `seed_params`: each mod-var stays a
// NAMED ∀-binder (production keeps the source name on the binder), but
// its type-bound renders as a bare `Imp` (unnamed) instead of a named ∀.
#[verifier::structural_decreases]
pub open spec fn seed_binders_hyp_bounds(binders: BinderList, bounds: ParamBoundList) -> FrameList
    decreases binders
{
    match binders {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => match bounds {
            ParamBoundList::Bound(_hname, prop, bt) =>
                FrameList::FBind(id, typ, Box::new(FrameList::FHyp(0, prop, Box::new(seed_binders_hyp_bounds(*t, *bt))))),
            ParamBoundList::NoBound(bt) =>
                FrameList::FBind(id, typ, Box::new(seed_binders_hyp_bounds(*t, *bt))),
            ParamBoundList::Nil =>
                FrameList::FBind(id, typ, Box::new(seed_binders_hyp_bounds(*t, ParamBoundList::Nil))),
        },
    }
}

// The mod-var frame block for a loop telescope (bootstrap-74 slice 2,
// UNIFORM shape): each modified local is a ∀-binder followed by its
// NAMED type-bound hyp — production's `_h_hoist_i` numbering
// (sum_to evidence: `All[i: Int] (All[_h_hoist_1 : 0 ≤ i ∧ …]`). The
// `Bound` name slot carries the serializer's `_h_hoist_i` leaf. This
// REPLACES the leading/non-leading split (seed_params vs
// seed_binders_hyp_bounds): post-N1 the shape is the same whether or
// not the loop leads the fn — a surviving plain FLet wrap-forces the
// goal via the GLOBAL gate instead.
#[verifier::structural_decreases]
pub open spec fn mod_var_frames(binders: BinderList, bounds: ParamBoundList) -> FrameList
    decreases binders
{
    match binders {
        BinderList::Nil => FrameList::FNil,
        BinderList::Cons(id, typ, t) => match bounds {
            ParamBoundList::Bound(hname, prop, bt) =>
                FrameList::FBind(id, typ, Box::new(FrameList::FHyp(hname, prop, Box::new(mod_var_frames(*t, *bt))))),
            ParamBoundList::NoBound(bt) =>
                FrameList::FBind(id, typ, Box::new(mod_var_frames(*t, *bt))),
            ParamBoundList::Nil =>
                FrameList::FBind(id, typ, Box::new(mod_var_frames(*t, ParamBoundList::Nil))),
        },
    }
}

// The maintain telescope a loop pushes around its body (finding-3 +
// bootstrap-16, UNIFORM post-N1 shape — bootstrap-74 slice 2): havoc
// the pre-loop lets for the modified locals, then mod-var frames,
// NAMED invariant hyps, the NAMED cond hyp, and the `_tactus_d_old`
// snapshot as an FLetH binder pair. No leading/non-leading switch —
// `binderprops_to_hyps` keeps the `_h_hoist_i` names the serializer
// computed; the goal's render mode falls out of the global gate.
// Factored into a top-level fn (not a nested `if`/`match` inside
// `wp_stm`'s arm) per the decide-checker flattening caveat.
pub open spec fn loop_maintain_frame(
    f: FrameList,
    inv_hyps: BinderList,
    binders: BinderList,
    binder_bounds: ParamBoundList,
    cond_name: u64,
    cond_ann: u64,
    d_old_name: u64,
    d_old_ty: u64,
    d_old_val: u64,
    d_old_eq_name: u64,
    d_old_eq_prop: u64,
) -> FrameList {
    let hv = havoc_lets(f, binders);
    let d_old = FrameList::FLetH(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, Box::new(FrameList::FNil));
    frame_append(hv,
        frame_append(mod_var_frames(binders, binder_bounds),
            frame_append(binderprops_to_hyps(inv_hyps),
                frame_append(FrameList::FHyp(cond_name, cond_ann, Box::new(FrameList::FNil)),
                    d_old))))
}

// The use telescope (what FOLLOWS the loop): same uniform shape but
// ¬cond instead of cond, and NO `_tactus_d_old` (the decrease is
// body-only).
pub open spec fn loop_use_frame(
    f: FrameList,
    inv_hyps: BinderList,
    binders: BinderList,
    binder_bounds: ParamBoundList,
    cond_name: u64,
    neg_cond_ann: u64,
) -> FrameList {
    let hv = havoc_lets(f, binders);
    frame_append(hv,
        frame_append(mod_var_frames(binders, binder_bounds),
            frame_append(binderprops_to_hyps(inv_hyps),
                FrameList::FHyp(cond_name, neg_cond_ann, Box::new(FrameList::FNil)))))
}

// The shared loop telescope prefix (bootstrap-79, break-form loops):
// havoc the pre-loop lets for the modified locals, then the mod-var
// ∀-binder/bound frames, then the NAMED invariant hyps. The classical
// `loop_maintain_frame`/`loop_use_frame` keep their own (byte-identical)
// construction; the break-form derivations share this prefix and splice
// the d_old pair / setup frames / guard hyps at their three positions
// (exit-reclose / maintain / post-loop continuation).
pub open spec fn loop_telescope_base(
    f: FrameList,
    inv_hyps: BinderList,
    binders: BinderList,
    binder_bounds: ParamBoundList,
) -> FrameList {
    let hv = havoc_lets(f, binders);
    frame_append(hv,
        frame_append(mod_var_frames(binders, binder_bounds),
            binderprops_to_hyps(inv_hyps)))
}

// The `_tactus_d_old` decreases snapshot as an FLetH binder pair
// (bootstrap-79 — factored out of `loop_maintain_frame`'s inline
// construction; the classical fn keeps its own, byte-identical).
pub open spec fn d_old_frame(
    d_old_name: u64,
    d_old_ty: u64,
    d_old_val: u64,
    d_old_eq_name: u64,
    d_old_eq_prop: u64,
) -> FrameList {
    FrameList::FLetH(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, Box::new(FrameList::FNil))
}

// Is `s` the empty block? (`is_skip` guards the If fall-through frame — a
// diverging then-branch only implies `¬cond` downstream when the else is
// trivial; a non-trivial else needs the two-way join, which stage A does
// not model — DESIGN §2.4.1.) `nat` return (1/0), not `bool`, for the
// decide idiom (finding-5).
pub open spec fn is_skip(s: StmData) -> nat {
    match s {
        StmData::Skip => 1,
        _ => 0,
    }
}

// Does control through `s` UNCONDITIONALLY diverge (return, or a DeadEnd
// `false` context) before reaching its end? Used by `frame_after`'s If
// arm: when the then-branch diverges and the else is Skip, production only
// reaches the post-if continuation via the else path, so the continuation
// is visited under `¬cond` (production clones `after` into both branches,
// but the diverging then-branch's clone yields no goals — §2.4.1). A `Seq`
// diverges if EITHER half does (the second is dead code once the first
// diverges); an `If` diverges only if BOTH branches do. Everything else
// (Assert/Assume/Assign/Call/Loop/Skip) falls through. `nat` (1/0) for
// decide. SOUND either way: a too-weak `diverges` (or a non-Skip else)
// omits the `¬cond` frame and the continuation goals honest-fail; a
// too-strong one adds a `¬cond` production never emitted and they ALSO
// honest-fail (structural `goal_eq`). Never silent-pass.
#[verifier::structural_decreases]
pub open spec fn diverges(s: StmData) -> nat
    decreases s
{
    match s {
        StmData::Ret(_es, _rb) => 1,
        StmData::DeadEnd(_b) => 1,           // `false` context: control does not continue
        StmData::Seq(a, b) =>
            if diverges(*a) == 1 || diverges(*b) == 1 { 1 } else { 0 },
        StmData::If(_c, _cn, _nc, _ncn, t, e) =>
            if diverges(*t) == 1 && diverges(*e) == 1 { 1 } else { 0 },
        StmData::IfCtor { pos_binders: _, eq_name: _, eq_prop: _, neg_name: _, neg_prop: _, thn, els } =>
            if diverges(*thn) == 1 && diverges(*els) == 1 { 1 } else { 0 },
        _ => 0,
    }
}

// The AssertQuery scope frame: production's `OblCtx::new_scope` keeps
// Let and Binder frames and drops Hyps — the isolated query context
// (sst_to_lean.rs; NonLinear semantics: enclosing-scope hypotheses are
// not available to the separate query).
#[verifier::structural_decreases]
pub open spec fn strip_hyps(f: FrameList) -> FrameList
    decreases f
{
    match f {
        FrameList::FNil => FrameList::FNil,
        FrameList::FBind(x, ty, t) => FrameList::FBind(x, ty, Box::new(strip_hyps(*t))),
        FrameList::FHyp(_hn, _h, t) => strip_hyps(*t),
        FrameList::FLet(x, v, t) => FrameList::FLet(x, v, Box::new(strip_hyps(*t))),
        FrameList::FLetH(x, ty, v, en, ep, t) => FrameList::FLetH(x, ty, v, en, ep, Box::new(strip_hyps(*t))),
        FrameList::FLetR(x, v, t) => FrameList::FLetR(x, v, Box::new(strip_hyps(*t))),
        // R1: `OblCtx::new_scope` drops hyps AND resets the closer to the
        // scope's own (default-class NONLIN) ladder at the same point —
        // the marker strips with the hyps, so NL query goals inside a
        // user-closer fn hoist again.
        FrameList::FUserCloser(t) => strip_hyps(*t),
    }
}

// The IfCtor positive-branch frame delta (bootstrap-77 / N2): the field
// binders then the ctor-equation hyp, exactly as `branch_ctor_frames`
// pushes them (binders first, equation last). Top-level spec fn (not a
// match nested in wp_stm's arm) — the backend flattens inner matches
// past enclosing arms (#redundant-alternative).
pub open spec fn ctor_pos_frame(b: BinderList, en: u64, ep: u64) -> FrameList {
    frame_append(binders_to_frame(b), FrameList::FHyp(en, ep, Box::new(FrameList::FNil)))
}

// frameAfter: the frame extension visible to whatever FOLLOWS `s`.
// (DESIGN §2.2. `If` join frames are NOT merged at stage A — but a
// DIVERGING then-branch with a Skip else does forward `¬cond`, §2.4.1.)
#[verifier::structural_decreases]
pub open spec fn frame_after(pp: LeafList, f: FrameList, s: StmData) -> FrameList
    decreases s
{
    match s {
        StmData::Assert(_o, hn, h) => frame_append(f, FrameList::FHyp(hn, h, Box::new(FrameList::FNil))),
        StmData::Assume(hn, e) => frame_append(f, FrameList::FHyp(hn, e, Box::new(FrameList::FNil))),
        StmData::Assign(x, rhs) => frame_append(f, FrameList::FLet(x, rhs, Box::new(FrameList::FNil))),
        // F4: the poison collapse is DERIVED — a hoistable let whose eq
        // prop mentions a residue name collapses LOSSLESSLY to a plain
        // FLet (production's hoist_all bail), which forces whole-goal
        // wrap via `has_plain_flet`. The serializer emits AssignH
        // whenever the hoist payload exists (era 1); refWp decides.
        StmData::AssignH(x, ty, v, en, ep) =>
            if leaf_mem(pp, ep) == 1 {
                frame_append(f, FrameList::FLet(x, v, Box::new(FrameList::FNil)))
            } else {
                frame_append(f, FrameList::FLetH(x, ty, v, en, ep, Box::new(FrameList::FNil)))
            },
        StmData::AssignR(x, v) => frame_append(f, FrameList::FLetR(x, v, Box::new(FrameList::FNil))),
        // Pass-through: append the serializer-transcribed post-call frame
        // verbatim (the ∀-path or #128 ret-eq shape both live in `post`).
        StmData::Call { reqs: _, post } => frame_append(f, *post),
        StmData::DeadEnd(_b) => f,          // facts discarded
        StmData::AssertQueryNl(_b, _tq) => f,    // isolated query: no frame delta
        // The proven P re-enters the main flow as a forward hyp
        // (production's AssertFact push after the assert-by theorem).
        StmData::AssertQueryTactus(_o, hn, h) =>
            frame_append(f, FrameList::FHyp(hn, h, Box::new(FrameList::FNil))),
        StmData::Ret(_es, _rb) => f,        // control does not continue
        // If — join frames not merged at stage A (§5.1), EXCEPT the
        // fall-through case: `if C { <diverges> } rest` reaches `rest` only
        // when C was false, so the continuation sees `¬C` (the annotated
        // `nc` leaf — production's `not(cond_marked)`, §2.4.1). Guarded by
        // `diverges(then) && is_skip(else)`; the general two-way join stays
        // `f` (honest-fail, documented caveat).
        StmData::If(_c, _cn, nc, ncn, t, e) =>
            if diverges(*t) == 1 && is_skip(*e) == 1 {
                frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil)))
            } else {
                f
            },
        // Same fall-through rule as `If` — the ¬cond hyp is the plain
        // negative discriminator (never ctor-upgraded).
        StmData::IfCtor { pos_binders: _, eq_name: _, eq_prop: _, neg_name, neg_prop, thn, els } =>
            if diverges(*thn) == 1 && is_skip(*els) == 1 {
                frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil)))
            } else {
                f
            },
        StmData::Loop { inv_hyps, inv_obligs: _, inv_obligs_exit: _, inv_obligs_break: _, binders, binder_bounds, cond_name, cond_ann: _, neg_cond_ann, neg_neg_cond_ann: _, break_guard_ann: _, break_use_ann, d_old_name: _, d_old_ty: _, d_old_val: _, d_old_eq_name: _, d_old_eq_prop: _, decrease_oblig: _, setup, body: _ } =>
            // use telescope (finding-3 + bootstrap-16, uniform shape):
            // havoc the pre-loop lets for the modified locals,
            // re-quantify them, re-introduce each invariant + ¬cond.
            // No `_tactus_d_old` (decrease is body-only).
            // Break-form (bootstrap-79): the post-loop continuation
            // prefix is the telescope WITHOUT the ¬cond hyp, then the
            // exit-side setup replay frames, then the BARE ¬cond hyp
            // (`break_use_ann` — production's exit_wrap pushes
            // `LExpr::not(cond)` unmarked).
            if is_skip(*setup) == 1 {
                loop_use_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, neg_cond_ann)
            } else {
                frame_append(
                    frame_after(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup),
                    FrameList::FHyp(cond_name, break_use_ann, Box::new(FrameList::FNil)))
            },
        StmData::Skip => f,
        StmData::Seq(a, b) => frame_after(pp, frame_after(pp, f, *a), *b),
    }
}

// The frame each Ret ensures is closed under: the pre-Ret frame `f`
// extended by the return-value binding (finding-4). Production peels
// `let <ret> := <e>` off the `Wp::Done` leaf into a `CtxFrame::Let`
// (emit_done_or_split) shared by every ensures conjunct, so refWp
// appends one `FLet` before closing each ensures. A `RetNone` (unit
// return) leaves the frame unchanged. Factored into its own top-level
// spec fn — NOT a `match` nested inside `wp_stm`'s `Ret` arm — because
// the tactus Lean backend flattens an inner match past the enclosing
// arm's siblings (the decide-checker note above; #redundant-alternative).
pub open spec fn ret_frame(pp: LeafList, f: FrameList, rb: RetBind) -> FrameList {
    match rb {
        RetBind::RetNone => f,
        RetBind::RetLet(name, val) =>
            frame_append(f, FrameList::FLet(name, val, Box::new(FrameList::FNil))),
        // F4: same derived poison collapse as the `AssignH` arm of
        // `frame_after` — a poisoned ret-let eq prop collapses the
        // hoist payload to a plain FLet (lossless; wrap-forced either
        // way).
        RetBind::RetLetH(name, ty, val, en, ep) =>
            if leaf_mem(pp, ep) == 1 {
                frame_append(f, FrameList::FLet(name, val, Box::new(FrameList::FNil)))
            } else {
                frame_append(f, FrameList::FLetH(name, ty, val, en, ep, Box::new(FrameList::FNil)))
            },
    }
}

// wpStm: the goals of `s` given the frame that precedes it.
#[verifier::structural_decreases]
pub open spec fn wp_stm(pp: LeafList, f: FrameList, s: StmData) -> GoalList
    decreases s
{
    match s {
        StmData::Assert(o, _hn, _h) =>
            GoalList::Cons(Box::new(close_e(pp, f, o)), Box::new(GoalList::Nil)),
        StmData::Assume(_hn, _e) => GoalList::Nil,
        StmData::Assign(_x, _rhs) => GoalList::Nil,
        StmData::AssignH(_x, _ty, _v, _en, _ep) => GoalList::Nil,
        StmData::AssignR(_x, _v) => GoalList::Nil,
        StmData::Call { reqs, post: _ } => close_each_e(pp, f, *reqs),
        StmData::DeadEnd(b) => wp_stm(pp, f, *b),
        StmData::AssertQueryNl(b, tq) =>
            goals_append(
                wp_stm(pp, strip_hyps(f), *b),
                GoalList::Cons(
                    Box::new(close_e(pp, frame_after(pp, strip_hyps(f), *b), tq)),
                    Box::new(GoalList::Nil))),
        // The assert-by theorem: ONE goal for the annotated P, closed in
        // WRAP mode unconditionally (`emit_with_closer` never hoists) —
        // the appended FUserCloser trips the gate even in a default fn.
        StmData::AssertQueryTactus(o, _hn, _h) =>
            GoalList::Cons(
                Box::new(close_e(pp, frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), o)),
                Box::new(GoalList::Nil)),
        StmData::Ret(es, rb) => close_each_e(pp, ret_frame(pp, f, rb), *es),
        StmData::If(c, cn, nc, ncn, t, e) =>
            goals_append(
                wp_stm(pp, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t),
                wp_stm(pp, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e)),
        // The N2 fork: then-branch under the ctor frames (field binders +
        // equation hyp), else-branch under the plain ¬cond hyp.
        StmData::IfCtor { pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els } =>
            goals_append(
                wp_stm(pp, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn),
                wp_stm(pp, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els)),
        StmData::Loop { inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann: _, neg_neg_cond_ann, break_guard_ann, break_use_ann: _, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body } => {
            if is_skip(*setup) == 1 {
            // Maintain telescope (finding-3 + bootstrap-16, uniform
            // post-N1 shape): havoc pre-loop lets for the modified
            // locals, re-quantify them + NAMED bound hyps, re-assert
            // each invariant + the cond as `_h_hoist_i` hyps, then the
            // `_tactus_d_old` decreases snapshot as an FLetH binder
            // pair. The HYPOTHESIS role reads `inv_hyps` (opaque
            // `u64`s); the OBLIGATION role reads the parallel deep
            // `inv_obligs` (W6d.1b-iii).
            let mframe = loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop);
            let body_goals = wp_stm(pp, mframe, *body);
            let endf = frame_after(pp, mframe, *body);
            // Walker-synthesised body-end obligations (DESIGN §5 Q3): one DEEP
            // goal per invariant re-closed (`close_each_e` over `inv_obligs` →
            // `LeafE(render_exp(ob))`), then the DEEP decrease obligation
            // (`close_e`).
            let maintain_reclose = close_each_e(pp, endf, *inv_obligs_exit);
            let decrease_goal =
                GoalList::Cons(Box::new(close_e(pp, endf, decrease_oblig)), Box::new(GoalList::Nil));
            // Emission order = init ++ body ++ maintain-reclose ++ decrease
            // (matches production's per-clause theorem order). Init closes each
            // deep invariant obligation under the ACTUAL pre-loop frame `f` (the
            // modified-local lets still hold their initial values there).
            let init = close_each_e(pp, f, *inv_obligs);
            goals_append(init,
                goals_append(body_goals,
                    goals_append(maintain_reclose, decrease_goal)))
            } else {
            // Break-form (bootstrap-79): THREE invariant goal families.
            // The ctx prefix = telescope base (havoc + mod-var frames +
            // inv hyps, NO cond hyp), then the d_old FLetH pair
            // (body-walk ctx), then the setup replay frames. The
            // exit-reclose (the normalized body's `If(¬exp, [break])`
            // then-branch hitting the break leaf) closes
            // `inv_obligs_break` under that ctx + the ¬cond hyp; the
            // maintain path swaps the ¬cond hyp for the `¬(¬cond)`
            // else-guard and walks the body. The setup's own obligations
            // emit TWICE: once in the body run (under the d_old ctx,
            // before the exit-reclose goals) and once in the exit
            // replay (under the bare base, after the decrease goal).
            let base = loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds);
            let mframe0 = frame_append(base, d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop));
            let setup_end = frame_after(pp, mframe0, *setup);
            let exit_frame = frame_append(setup_end, FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil)));
            let guard_frame = frame_append(setup_end, FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil)));
            let endf = frame_after(pp, guard_frame, *body);
            let init = close_each_e(pp, f, *inv_obligs);
            let setup_goals = wp_stm(pp, mframe0, *setup);
            let exit_reclose = close_each_e(pp, exit_frame, *inv_obligs_break);
            let body_goals = wp_stm(pp, guard_frame, *body);
            let maintain_reclose = close_each_e(pp, endf, *inv_obligs_exit);
            let decrease_goal = GoalList::Cons(Box::new(close_e(pp, endf, decrease_oblig)), Box::new(GoalList::Nil));
            let replay_goals = wp_stm(pp, base, *setup);
            goals_append(init, goals_append(setup_goals, goals_append(exit_reclose, goals_append(body_goals, goals_append(maintain_reclose, goals_append(decrease_goal, replay_goals))))))
            }
        },
        StmData::Skip => GoalList::Nil,
        StmData::Seq(a, b) =>
            goals_append(wp_stm(pp, f, *a), wp_stm(pp, frame_after(pp, f, *a), *b)),
    }
}

// The `&mut`-param fn-entry preamble (bootstrap-78 S2): two plain FLets
// per entry, at_pre snapshot FIRST then the body shadow (production's
// `add_pre_capture` then `add_body_shadow` insertion order, sst_to_lean
// ~1526). Plain FLets trip `has_plain_flet` → every goal of a mut-param
// fn renders in WRAP mode, exactly production's `hoist_all` bail on the
// typ-less preamble lets (vec_push7 evidence).
#[verifier::structural_decreases]
pub open spec fn mut_preamble_frame(m: MutParamList) -> FrameList
    decreases m
{
    match m {
        MutParamList::Nil => FrameList::FNil,
        MutParamList::Cons(p, at_pre, deref_val, t) =>
            FrameList::FLet(at_pre, deref_val,
                Box::new(FrameList::FLet(p, deref_val,
                    Box::new(mut_preamble_frame(*t))))),
    }
}

// Seed the initial frame from the signature (DESIGN §2.2): typ-params,
// then value params interleaved with bound hyps, then reqs, then the
// `&mut`-param fn-entry preamble lets. reqs are NAMED ∀-binders
// (finding-2), so they fold in via `binders_to_frame`, not
// `hyps_of_leaves`.
pub open spec fn seed_frame(c: FnCtxData) -> FrameList {
    frame_append(binders_to_frame(c.typ_params),
        frame_append(seed_params(c.params, c.param_bounds),
            frame_append(binders_to_frame(c.reqs),
                frame_append(mut_preamble_frame(c.mut_params),
                    // R1: non-default fn-level closer → the wrap-forcing
                    // marker rides at the seed's tail (renders nothing;
                    // position is immaterial to the emitted goals).
                    if c.closer_default == 1 { FrameList::FNil }
                    else { FrameList::FUserCloser(Box::new(FrameList::FNil)) }))))
}

// refWp: the certificate LHS. Seed the frame, then walk the body. The
// serializer emits an explicit `Ret` leaf list (all fixtures end in Ret),
// so refWp does not synthesize a fall-through Ret (§5.2). F4: the poison
// set is derived ONCE here from the ctx side tables and threaded as the
// single poison source (`pp`) through the walk, the gate, and the
// FLetH/RetLetH collapse.
pub open spec fn ref_wp(c: FnCtxData, s: StmData) -> GoalList {
    wp_stm(poisoned_props(c), seed_frame(c), s)
}

// Structural equality for the `decide` bridge (DESIGN §2.3). STRICT:
// every leaf id and binder id must match. A strict checker keeps the TCB
// honest — where a fixture bridge fails to close it indicts an unfaithful
// serializer/shape (board writeup), NOT a lax comparison.
//
// IMPORTANT (finding-5): these return `nat` (1 = equal, 0 = not), NOT
// `bool`. The tactus Lean backend lowers a `bool`-returning spec fn to a
// NONCOMPUTABLE `Prop` def, for which `Decidable (goal_eq a b)` resolves
// to `Classical.propDecidable` and `decide` gets STUCK on `Classical.choice`.
// A `nat`-returning def gives the `= 1` conjuncts a concrete `Nat.decEq`
// instance, and the kernel then reduces the body (nested numeral-`ite`s).
// The W2b bridge line is therefore `goals_eq (refWp …) production = 1 := by
// decide`, not `= true` as DESIGN §2.3 sketched.
// The structural checkers must (a) recurse structurally on their first
// argument and (b) emit unambiguously. A nested `match a { … match b …}`
// keeps (a) but breaks (b): the tactus Lean backend flattens the inner
// match so later outer arms bind past its wildcard ("redundant
// alternative"). A tuple `match (a, b)` fixes (b) but breaks (a): the
// child `t1.deref` is no longer seen as a structural subterm of `a`. So
// match `a` ALONE (single match → structural + unambiguous) and read `b`
// through NON-recursive projections (a nat constructor tag + field
// accessors), keeping every arm body a chain of `if`s, never a match.

pub open spec fn gd_tag(g: GoalData) -> nat {
    match g {
        GoalData::Leaf(_) => 0,
        GoalData::Imp(_, _) => 1,
        GoalData::All(_, _, _) => 2,
        GoalData::Let(_, _, _) => 3,
        GoalData::LeafE(_) => 4,
    }
}
pub open spec fn gd_leaf_id(g: GoalData) -> u64 { match g { GoalData::Leaf(x) => x, _ => 0 } }
pub open spec fn gd_imp_hyp(g: GoalData) -> u64 { match g { GoalData::Imp(h, _) => h, _ => 0 } }
pub open spec fn gd_all_name(g: GoalData) -> u64 { match g { GoalData::All(x, _, _) => x, _ => 0 } }
pub open spec fn gd_all_typ(g: GoalData) -> u64 { match g { GoalData::All(_, t, _) => t, _ => 0 } }
pub open spec fn gd_let_name(g: GoalData) -> u64 { match g { GoalData::Let(x, _, _) => x, _ => 0 } }
pub open spec fn gd_let_val(g: GoalData) -> u64 { match g { GoalData::Let(_, v, _) => v, _ => 0 } }
// The rendered ExprData of a deep leaf (self-defaulting projection; the
// goal_eq LeafE arm reads it only after the tag guard confirms b is a LeafE).
pub open spec fn gd_leafe_expr(g: GoalData) -> ExprData {
    match g { GoalData::LeafE(e) => e, _ => ExprData::Atom(0) }
}
// The single child of a non-leaf node (self for a leaf — never recursed on).
pub open spec fn gd_child(g: GoalData) -> GoalData {
    match g {
        GoalData::Imp(_, t) => *t,
        GoalData::All(_, _, t) => *t,
        GoalData::Let(_, _, t) => *t,
        GoalData::Leaf(x) => GoalData::Leaf(x),
        GoalData::LeafE(e) => GoalData::LeafE(e),
    }
}

#[verifier::structural_decreases]
pub open spec fn goal_eq(a: GoalData, b: GoalData) -> nat
    decreases a
{
    match a {
        GoalData::Leaf(x) =>
            if gd_tag(b) == 0 { if x == gd_leaf_id(b) { 1 } else { 0 } } else { 0 },
        GoalData::Imp(h1, t1) =>
            if gd_tag(b) == 1 {
                if h1 == gd_imp_hyp(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
            } else { 0 },
        GoalData::All(x1, ty1, t1) =>
            if gd_tag(b) == 2 {
                if x1 == gd_all_name(b) {
                    if ty1 == gd_all_typ(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        GoalData::Let(x1, v1, t1) =>
            if gd_tag(b) == 3 {
                if x1 == gd_let_name(b) {
                    if v1 == gd_let_val(b) { goal_eq(*t1, gd_child(b)) } else { 0 }
                } else { 0 }
            } else { 0 },
        // Deep leaf: compare the two rendered ExprData trees structurally.
        // `expr_eq` is a SEPARATE recursion (on ExprData), so `goal_eq`'s
        // `decreases a` is unaffected — this arm makes no recursive goal_eq
        // call.
        GoalData::LeafE(e1) =>
            if gd_tag(b) == 4 { expr_eq(e1, gd_leafe_expr(b)) } else { 0 },
    }
}

pub open spec fn gl_tag(g: GoalList) -> nat {
    match g {
        GoalList::Nil => 0,
        GoalList::Cons(_, _) => 1,
    }
}
pub open spec fn gl_head(g: GoalList) -> GoalData {
    match g { GoalList::Cons(h, _) => *h, GoalList::Nil => GoalData::Leaf(0) }
}
pub open spec fn gl_tail(g: GoalList) -> GoalList {
    match g { GoalList::Cons(_, t) => *t, GoalList::Nil => GoalList::Nil }
}

#[verifier::structural_decreases]
pub open spec fn goals_eq(a: GoalList, b: GoalList) -> nat
    decreases a
{
    match a {
        GoalList::Nil => if gl_tag(b) == 0 { 1 } else { 0 },
        GoalList::Cons(h1, t1) =>
            if gl_tag(b) == 1 {
                if goal_eq(*h1, gl_head(b)) == 1 { goals_eq(*t1, gl_tail(b)) } else { 0 }
            } else { 0 },
    }
}

// ── W2a: graded reduction probes (isolate what kernel-computes) ─────

proof fn probe_goal_eq_leaf()
    ensures
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(5)) == 1,
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(6)) == 0
by { decide }

proof fn probe_goal_eq_nested()
    ensures
        goal_eq(GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
                GoalData::All(0, 1, Box::new(GoalData::Leaf(9)))) == 1,
        goal_eq(GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
                GoalData::All(7, 1, Box::new(GoalData::Leaf(9)))) == 0
by { decide }

proof fn probe_goals_eq_lit()
    ensures
        goals_eq(GoalList::Nil, GoalList::Nil) == 1,
        goals_eq(GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil)),
                 GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil))) == 1
by { decide }

proof fn probe_close()
    ensures
        goal_size(close(FrameList::FNil, 9)) == 1,
        goal_size(close(FrameList::FBind(0, 1, Box::new(FrameList::FNil)), 9)) == 2
by { decide }

// W6d.1b: close_e folds the SAME spine as close (same goal_size), but the
// terminal is the RENDERED ExprData leaf, not the opaque `Leaf(u64)`. The
// last two conjuncts are the mutation-sensitivity that makes the deep bridge
// meaningful: `close_e(·, atom_ob 9)` produces `LeafE(Atom 9)`, which
// `goal_eq` accepts against `LeafE(Atom 9)` and REJECTS against the stage-A
// `Leaf 9` (a production `LeafE` can never silently match a reference `Leaf`).
proof fn probe_close_e()
    ensures
        goal_size(close_e(LeafList::Nil, FrameList::FNil, atom_ob(9))) == 1,
        goal_size(close_e(LeafList::Nil, FrameList::FBind(0, 1, Box::new(FrameList::FNil)), atom_ob(9))) == 2,
        goal_eq(close_e(LeafList::Nil, FrameList::FNil, atom_ob(9)), GoalData::LeafE(ExprData::Atom(9))) == 1,
        goal_eq(close_e(LeafList::Nil, FrameList::FNil, atom_ob(9)), GoalData::Leaf(9)) == 0
by { decide }

proof fn probe_wp_stm()
    ensures
        goal_count(wp_stm(LeafList::Nil, FrameList::FNil, StmData::Assert(atom_ob(9), 0, 9))) == 1,
        goal_count(wp_stm(LeafList::Nil, FrameList::FNil, StmData::Skip)) == 0
by { decide }

proof fn probe_ref_wp()
    ensures
        goal_count(ref_wp(FnCtxData {
            typ_params: BinderList::Nil,
            params: BinderList::Nil,
            param_bounds: ParamBoundList::Nil,
            reqs: BinderList::Nil,
            mut_params: MutParamList::Nil,
            enss: LeafList::Nil,
            residue_names: LeafList::Nil,
            prop_deeps: PropDeepList::Nil,
            closer_default: 1,
        }, StmData::Assert(atom_ob(9), 0, 9))) == 1
by { decide }

// ── W2a: end-to-end refWp unit examples (against hand-computed goals) ──

// Minimal context: one int param `x` (name leaf 0, type leaf 1) with a
// bound hyp (name leaf 19 = h_x_bound, prop leaf 2), no reqs. seed_frame =
// FBind(0,1, FBind(19,2, FNil)) — the bound hyp is now a NAMED ∀ (finding-2).
proof fn ref_wp_seed_and_assert()
    ensures
        // refWp folds the seed around a single Assert obligation:
        //   ∀ (x:Int), ∀ (h_x_bound:2), <9>
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                    param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                    reqs: BinderList::Nil,
                    mut_params: MutParamList::Nil,
                    enss: LeafList::Nil,
                    residue_names: LeafList::Nil,
                    prop_deeps: PropDeepList::Nil,
                    closer_default: 1,
                },
                StmData::Assert(atom_ob(9), 0, 9),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2, Box::new(GoalData::LeafE(ExprData::Atom(9))))))),
                Box::new(GoalList::Nil)),
        ) == 1,
        // A Ret of two ensures leaves → two goals sharing the seed spine
        // (the max_u64 multiplicity, minus the branch-in-leaf divergence).
        goal_count(ref_wp(
            FnCtxData {
                typ_params: BinderList::Nil,
                params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                reqs: BinderList::Nil,
                mut_params: MutParamList::Nil,
                enss: LeafList::Cons(5, Box::new(LeafList::Cons(6, Box::new(LeafList::Nil)))),
                residue_names: LeafList::Nil,
                prop_deeps: PropDeepList::Nil,
                closer_default: 1,
            },
            StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(5)), Box::new(RawExpList::Cons(Box::new(atom_ob(6)), Box::new(RawExpList::Nil))))),
                RetBind::RetNone),
        )) == 2
by { decide }

// ── bootstrap-78 S2: mut-param fn-entry preamble (the vec_push7 shape) ──
// One `&mut` param (name leaf 0, MutRef wrapper typ leaf 1, no bound),
// one req binder (h_req0 = 3, prop 2), one preamble entry (at_pre name
// 4, deref value leaf 5). The derived plain FLets trip the wrap gate:
// params + reqs stay FBind→All (the theorem's base binders) and the
// preamble renders as goal-position Lets, at_pre first — production's
// `hoist_all` bail shape (E1/vec_push7 evidence, board bootstrap-78).
pub open spec fn s2_mut_ctx() -> FnCtxData {
    FnCtxData {
        typ_params: BinderList::Nil,
        params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
        param_bounds: ParamBoundList::NoBound(Box::new(ParamBoundList::Nil)),
        reqs: BinderList::Cons(3, 2, Box::new(BinderList::Nil)),
        mut_params: MutParamList::Cons(0, 4, 5, Box::new(MutParamList::Nil)),
        enss: LeafList::Nil,
        residue_names: LeafList::Nil,
        prop_deeps: PropDeepList::Nil,
        closer_default: 1,
    }
}

proof fn ref_wp_mut_preamble_wrap()
    ensures
        gate_wrap(LeafList::Nil, seed_frame(s2_mut_ctx())) == 1,
        goals_eq(
            ref_wp(s2_mut_ctx(), StmData::Assert(atom_ob(9), 0, 9)),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1,
                    Box::new(GoalData::All(3, 2,
                        Box::new(GoalData::Let(4, 5,
                            Box::new(GoalData::Let(0, 5,
                                Box::new(GoalData::LeafE(ExprData::Atom(9))))))))))),
                Box::new(GoalList::Nil)),
        ) == 1
by { decide }

// Seq threads frameAfter: the second Assert sees the first as a forward
// hyp (Assert-then-Assume behaviour, one hyp here from the Assert alone).
// The seed bound hyp is a NAMED ∀ (h_x_bound = 19). Post-N1
// (bootstrap-74): the frame is let-free → HOIST mode → the Assert
// forward hyp renders as a binder too — All(0, 9, ·) with the model's
// 0-sentinel name (the serializer supplies production's `_h_hoist_i`
// name in slice 2).
proof fn ref_wp_seq_threads_frame()
    ensures
        // ∀x,∀(h_x_bound:2). <9>   then   ∀x,∀(h_x_bound:2). h9 → <10>
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                    param_bounds: ParamBoundList::Bound(19, 2, Box::new(ParamBoundList::Nil)),
                    reqs: BinderList::Nil,
                    mut_params: MutParamList::Nil,
                    enss: LeafList::Nil,
                    residue_names: LeafList::Nil,
                    prop_deeps: PropDeepList::Nil,
                    closer_default: 1,
                },
                StmData::Seq(Box::new(StmData::Assert(atom_ob(9), 0, 9)), Box::new(StmData::Assert(atom_ob(10), 0, 10))),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2, Box::new(GoalData::LeafE(ExprData::Atom(9))))))),
                Box::new(GoalList::Cons(
                    Box::new(GoalData::All(0, 1, Box::new(GoalData::All(19, 2,
                        Box::new(GoalData::All(0, 9, Box::new(GoalData::LeafE(ExprData::Atom(10))))))))),
                    Box::new(GoalList::Nil)))),
        ) == 1
by { decide }

// Finding-2 payoff: refWp on add_capped's ctx reproduces production goal 0's
// seed telescope EXACTLY — all NAMED ∀-binders, no anonymous arrows. Leaf ids
// are the production ones from the REGENERATED cert (2026-07-14 batched regen,
// bootstrap-fixture/out/lib/cert/add_capped.cert.lean):
//   params x=0:Int=1, y=4:Int=1; bounds h_x_bound=3:prop2, h_y_bound=6:prop5;
//   reqs h_req0=8:(x<1000)=7, h_req1=10:(y<1000)=9; obligation leaf 15.
// Expected spine = All 0 1 (All 3 2 (All 4 1 (All 6 5 (All 8 7
//   (All 10 9 (Leaf 15)))))) — the first assert goal, verbatim. The Assert
// now carries BOTH roles (finding-1): oblig leaf 15 (annotated, drives the
// GOAL) and hyp leaf 14 (bare, drives the forward frame — unused here since
// nothing follows). `wp_stm` reads the oblig, so the goal ends in Leaf 15.
proof fn ref_wp_add_capped_seed_spine()
    ensures
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Cons(4, 1, Box::new(BinderList::Nil)))),
                    param_bounds: ParamBoundList::Bound(3, 2,
                        Box::new(ParamBoundList::Bound(6, 5, Box::new(ParamBoundList::Nil)))),
                    reqs: BinderList::Cons(8, 7, Box::new(BinderList::Cons(10, 9, Box::new(BinderList::Nil)))),
                    mut_params: MutParamList::Nil,
                    enss: LeafList::Cons(11, Box::new(LeafList::Nil)),
                    residue_names: LeafList::Nil,
                    prop_deeps: PropDeepList::Nil,
                    closer_default: 1,
                },
                StmData::Assert(atom_ob(15), 0, 14),
            ),
            GoalList::Cons(
                Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2,
                    Box::new(GoalData::All(4, 1, Box::new(GoalData::All(6, 5,
                        Box::new(GoalData::All(8, 7, Box::new(GoalData::All(10, 9,
                            Box::new(GoalData::LeafE(ExprData::Atom(15))))))))))))))),
                Box::new(GoalList::Nil)),
        ) == 1
by { decide }

// Finding-4 + Ret-annotation payoff: the return statement binds `let r := s`
// before the ANNOTATED postcondition, reproducing add_capped goal 3's tail
// `… Let 16 23, Let 13 16, Leaf 12` from the REGENERATED cert
// (bootstrap-fixture/out/lib/cert/add_capped.cert.lean). Isolated from the
// full body: the pre-Ret frame here carries only the last body Assign as
// FLet(16,23) (leaf 16 = `s`, leaf 23 = `s + 0`); the Ret appends the return
// binding FLet(13,16) (name 13 = `r`, val 16 = `s`) then closes the annotated
// obligation leaf 12 (`/- @rust:…85:13 -/ r = x + y`). RetNone (a unit
// return) leaves the frame unextended — just `… Leaf 12`. The FULL 4-goal
// add_capped bridge was hand-run to close by `decide` this same turn.
proof fn ref_wp_ret_return_binding()
    ensures
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FLet(16, 23, Box::new(FrameList::FNil)),
                StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(12)), Box::new(RawExpList::Nil))),
                    RetBind::RetLet(13, 16)),
            ),
            GoalList::Cons(
                Box::new(GoalData::Let(16, 23, Box::new(GoalData::Let(13, 16,
                    Box::new(GoalData::LeafE(ExprData::Atom(12))))))),
                Box::new(GoalList::Nil)),
        ) == 1,
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FLet(16, 23, Box::new(FrameList::FNil)),
                StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(12)), Box::new(RawExpList::Nil))),
                    RetBind::RetNone),
            ),
            GoalList::Cons(
                Box::new(GoalData::Let(16, 23, Box::new(GoalData::LeafE(ExprData::Atom(12))))),
                Box::new(GoalList::Nil)),
        ) == 1
by { decide }

// ── finding-3 payoff: sum_to's FULL loop bridge closes by `decide` ──
//
// Reconstructs `sum_to`'s ctx + SST (new Loop shape) and asserts refWp
// reproduces ALL 12 production goals VERBATIM. Leaf ids are the production
// ones from the fixture cert (bootstrap-fixture/out/lib/cert/sum_to.cert.lean,
// pre-finding-3 shape — the leaf TABLE is unchanged by finding-3, only the
// SST Loop node's field layout is). Key ids:
//   ctx: n=0:Int=1, h_n_bound=3:prop2, h_req0=5:(n≤1000)=4, ens(bare)=6.
//   pre-loop: Assign i(9):=0(10), Assign acc(11):=0(10).
//   loop inv_hyps: (_h_ctx_2=34,inv0_ann=23) (_h_ctx_3=33,inv1_ann=24)
//     (_h_ctx_4=32,inv2_ann=25) (_h_ctx_5=31,inv3_ann=26).
//   binders i=9:Int=1, acc=11:Int=1; bounds (_h_ctx_0=37,i_bound=38)
//     (_h_ctx_1=35,acc_bound=36). cond_name _h_ctx_6=29, cond_ann=30,
//     neg_cond_ann=40. d_old=27:=(n-i)=28, decrease_oblig=39.
//   body: Assert 18/17, Assume 17, Assign i:=i+1(19), Assert 21/20,
//     Assume 20, Assign acc:=acc+i(22).
//   Ret: annotated ens leaf 7, RetLet r=8 := acc=11.
// The 12 goals = 4 inv-init, 2 body-assert, 4 inv-maintain, 1 decrease, 1
// postcondition — the exact goal list of `cert_sum_to_goals`. Mutation-kill:
// any single leaf/binder id or constructor change flips `goals_eq` to 0
// (goal_eq compares name ids — `goal_eq_strictness`).
proof fn ref_wp_sum_to_loop()
    ensures
        goals_eq(
            ref_wp(
                FnCtxData {
                    typ_params: BinderList::Nil,
                    params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)),
                    param_bounds: ParamBoundList::Bound(3, 2, Box::new(ParamBoundList::Nil)),
                    reqs: BinderList::Cons(5, 4, Box::new(BinderList::Nil)),
                    mut_params: MutParamList::Nil,
                    enss: LeafList::Cons(6, Box::new(LeafList::Nil)),
                    residue_names: LeafList::Nil,
                    prop_deeps: PropDeepList::Nil,
                    closer_default: 1,
                },
                // Pre-loop assigns HOIST as binder pairs (real sum_to:
                // `All[i] (All[_h_i_hoist1 : i = 0]`); ids 43-52 are
                // fixture-synthetic (the eq names/props of the hoisted
                // lets), the rest stay the real cert's.
                StmData::Seq(Box::new(StmData::AssignH(9, 1, 10, 43, 44)), Box::new(
                StmData::Seq(Box::new(StmData::AssignH(11, 1, 10, 45, 46)), Box::new(
                StmData::Seq(
                    Box::new(StmData::Loop {
                        inv_hyps: Box::new(BinderList::Cons(34, 23, Box::new(
                            BinderList::Cons(33, 24, Box::new(
                            BinderList::Cons(32, 25, Box::new(
                            BinderList::Cons(31, 26, Box::new(BinderList::Nil))))))))),
                        inv_obligs: Box::new(RawExpList::Cons(Box::new(atom_ob(23)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(24)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(25)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(26)), Box::new(RawExpList::Nil))))))))),
                        // The RENAMED re-close obligations (Round D evidence):
                        // body-end inv texts rewrite shadowed locals
                        // (`i_hoist1 ≤ n`, …) — fresh synthetic ids.
                        inv_obligs_exit: Box::new(RawExpList::Cons(Box::new(atom_ob(55)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(56)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(57)), Box::new(
                            RawExpList::Cons(Box::new(atom_ob(58)), Box::new(RawExpList::Nil))))))))),
                        // Classical empty-setup loop (bootstrap-79): no
                        // break leaf, no setup, ¬¬cond sentinel.
                        inv_obligs_break: Box::new(RawExpList::Nil),
                        binders: Box::new(BinderList::Cons(9, 1, Box::new(
                            BinderList::Cons(11, 1, Box::new(BinderList::Nil))))),
                        binder_bounds: Box::new(ParamBoundList::Bound(37, 38, Box::new(
                            ParamBoundList::Bound(35, 36, Box::new(ParamBoundList::Nil))))),
                        cond_name: 29,
                        cond_ann: 30,
                        neg_cond_ann: 40,
                        neg_neg_cond_ann: 999999,
                        break_guard_ann: 999999,
                        break_use_ann: 999999,
                        d_old_name: 27,
                        d_old_ty: 1,
                        d_old_val: 28,
                        d_old_eq_name: 41,
                        d_old_eq_prop: 42,
                        decrease_oblig: atom_ob(39),
                        setup: Box::new(StmData::Skip),
                        body: Box::new(
                            StmData::Seq(Box::new(StmData::Assert(atom_ob(18), 0, 17)), Box::new(
                            StmData::Seq(Box::new(StmData::Assume(0, 17)), Box::new(
                            // The body rebinds i/acc — production's shadow
                            // freshening gives `i_hoist1` / `acc_hoist1`
                            // with the doubly-freshened eq names.
                            StmData::Seq(Box::new(StmData::AssignH(47, 1, 19, 48, 49)), Box::new(
                            StmData::Seq(Box::new(StmData::Assert(atom_ob(21), 0, 20)), Box::new(
                            StmData::Seq(Box::new(StmData::Assume(0, 20)), Box::new(
                            StmData::AssignH(50, 1, 22, 51, 52)))))))))))),
                    }),
                    Box::new(StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(7)), Box::new(RawExpList::Nil))),
                        RetBind::RetLetH(8, 1, 11, 53, 54))),
                ))))),
            ),
                        // EXPECTED goals, computed by `lib.ref_wp` on the SST above (the
            // fixture pins refWp's CURRENT output as a regression tripwire — the
            // independent byte-check is the real sum_to cert bridge, probe9).
            // Shape (uniform post-N1 loop telescope): pre-loop AssignH pairs
            // hoisted in goals 0-3; goals 4-5 carry the uniform maintain
            // telescope (named bound/inv/cond hyps + d_old FLetH pair); goals
            // 6-10 add the shadow-freshened body rebinds (i_hoist1, acc_hoist1);
            // goal 11 = use telescope + RetLetH pair.
            GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(43, 44, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(45, 46, Box::new(GoalData::LeafE(ExprData::Atom(23))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(43, 44, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(45, 46, Box::new(GoalData::LeafE(ExprData::Atom(24))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(43, 44, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(45, 46, Box::new(GoalData::LeafE(ExprData::Atom(25))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(43, 44, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(45, 46, Box::new(GoalData::LeafE(ExprData::Atom(26))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::LeafE(ExprData::Atom(18))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::LeafE(ExprData::Atom(21))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(50, 1, Box::new(GoalData::All(51, 52, Box::new(GoalData::LeafE(ExprData::Atom(55))))))))))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(50, 1, Box::new(GoalData::All(51, 52, Box::new(GoalData::LeafE(ExprData::Atom(56))))))))))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(50, 1, Box::new(GoalData::All(51, 52, Box::new(GoalData::LeafE(ExprData::Atom(57))))))))))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(50, 1, Box::new(GoalData::All(51, 52, Box::new(GoalData::LeafE(ExprData::Atom(58))))))))))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 30, Box::new(GoalData::All(27, 1, Box::new(GoalData::All(41, 42, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(0, 17, Box::new(GoalData::All(47, 1, Box::new(GoalData::All(48, 49, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(0, 20, Box::new(GoalData::All(50, 1, Box::new(GoalData::All(51, 52, Box::new(GoalData::LeafE(ExprData::Atom(39))))))))))))))))))))))))))))))))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::All(5, 4, Box::new(GoalData::All(9, 1, Box::new(GoalData::All(37, 38, Box::new(GoalData::All(11, 1, Box::new(GoalData::All(35, 36, Box::new(GoalData::All(34, 23, Box::new(GoalData::All(33, 24, Box::new(GoalData::All(32, 25, Box::new(GoalData::All(31, 26, Box::new(GoalData::All(29, 40, Box::new(GoalData::All(8, 1, Box::new(GoalData::All(53, 54, Box::new(GoalData::LeafE(ExprData::Atom(7))))))))))))))))))))))))))))))), Box::new(GoalList::Nil))))))))))))))))))))))))
        ) == 1
by { decide }

// ── bootstrap-16 revisited: UNIFORM loop telescope (bootstrap-74 slice 2) ──
//
// The leading/non-leading split is DEAD: post-N1, production numbers a
// loop's bounds/invs/cond `_h_hoist_i` whether or not the loop leads
// the fn (`_h_ctx_N` is gone from goal shapes; find_square evidence in
// DESIGN-b74-slice2-serializer §2b). `loop_maintain_frame` /
// `loop_use_frame` build ONE uniform telescope — the render mode falls
// out of the GLOBAL wrap gate instead of a loop-local `has_let`
// switch. Leaf ids below are find_square's REAL inner-loop ids (from
// bootstrap-fixture/out/lib/cert/find_square.cert.lean): b=23:Int=1,
// b-bound=24 named _h_ctx_0=11, invs 25/26/27 named _h_ctx_1/2/3=13/15/17,
// cond _h_ctx_?=28, cond_ann=29, neg_cond_ann=30, d_old=31:=32, assert
// oblig=35. (41/42 are fixture-synthetic: the d_old eq pair.)
// ── bootstrap-16 revisited: UNIFORM loop telescope (bootstrap-74 slice 2) ──
//
// The leading/non-leading split is DEAD: post-N1, production numbers a
// loop's bounds/invs/cond `_h_hoist_i` whether or not the loop leads the
// fn (`_h_ctx_N` is gone from goal shapes; find_square evidence §2b).
// `loop_maintain_frame`/`loop_use_frame` build ONE uniform telescope —
// the render mode falls out of the GLOBAL wrap gate: a surviving
// pre-loop plain `FLet` (an enclosing let the havoc didn't drop)
// wrap-forces the goal (d_old renders `Let`, hyps anonymous `Imp`),
// while a let-free prefix hoists (named `All` hyps + the d_old FLetH
// binder pair). Leaf ids are find_square's REAL inner-loop ids (from
// bootstrap-fixture/out/lib/cert/find_square.cert.lean): b=23:Int=1,
// b-bound=24 named _h_ctx_0=11, invs 25/26/27 named _h_ctx_1/2/3=13/15/17,
// cond _h_ctx_?=28, cond_ann=29, neg_cond_ann=30, d_old=31:=32, assert
// oblig=35. (41/42/43 are fixture-synthetic: the d_old eq pair.)
proof fn ref_wp_nested_loop_nonleading()
    ensures
        // WRAP-forced maintain telescope (an enclosing plain `FLet`
        // survives havoc ⇒ global gate wraps): d_old renders `Let`,
        // hyps anonymous `Imp` — the pre-slice-2 "non-leading" SHAPE,
        // now produced by the gate, not a loop-local switch.
        goal_eq(
            close_e(LeafList::Nil, 
                loop_maintain_frame(
                    FrameList::FBind(0, 1, Box::new(FrameList::FLet(20, 21, Box::new(FrameList::FNil)))),
                    BinderList::Cons(13, 25, Box::new(BinderList::Cons(15, 26,
                        Box::new(BinderList::Cons(17, 27, Box::new(BinderList::Nil)))))),
                    BinderList::Cons(23, 1, Box::new(BinderList::Nil)),
                    ParamBoundList::Bound(11, 24, Box::new(ParamBoundList::Nil)),
                    28, 29, 31, 1, 32, 41, 42),
                atom_ob(35)),
            GoalData::All(0, 1, Box::new(GoalData::Let(20, 21, Box::new(
                GoalData::All(23, 1, Box::new(GoalData::Imp(24, Box::new(
                GoalData::Imp(25, Box::new(GoalData::Imp(26, Box::new(
                GoalData::Imp(27, Box::new(GoalData::Imp(29, Box::new(
                GoalData::Let(31, 32, Box::new(GoalData::LeafE(ExprData::Atom(35)))))))))))))))))))),
        ) == 1,
        // HOISTED maintain telescope (no surviving `let`): the SAME loop
        // node renders bounds/invs/cond as NAMED ∀-hyps and d_old as the
        // FLetH binder pair `All(31, 1) ∘ All(41, 42)`. Only the front
        // frame differs — the branch is the GLOBAL gate, not the loop.
        goal_eq(
            close_e(LeafList::Nil, 
                loop_maintain_frame(
                    FrameList::FBind(0, 1, Box::new(FrameList::FNil)),
                    BinderList::Cons(13, 25, Box::new(BinderList::Cons(15, 26,
                        Box::new(BinderList::Cons(17, 27, Box::new(BinderList::Nil)))))),
                    BinderList::Cons(23, 1, Box::new(BinderList::Nil)),
                    ParamBoundList::Bound(11, 24, Box::new(ParamBoundList::Nil)),
                    28, 29, 31, 1, 32, 41, 42),
                atom_ob(35)),
            GoalData::All(0, 1, Box::new(GoalData::All(23, 1, Box::new(
                GoalData::All(11, 24, Box::new(GoalData::All(13, 25, Box::new(
                GoalData::All(15, 26, Box::new(GoalData::All(17, 27, Box::new(
                GoalData::All(28, 29, Box::new(GoalData::All(31, 1, Box::new(
                GoalData::All(41, 42, Box::new(GoalData::LeafE(ExprData::Atom(35)))))))))))))))))))),
        ) == 1,
        // WRAP-forced use telescope (¬cond, no d_old).
        goal_eq(
            close_e(LeafList::Nil, 
                loop_use_frame(
                    FrameList::FBind(0, 1, Box::new(FrameList::FLet(20, 21, Box::new(FrameList::FNil)))),
                    BinderList::Cons(13, 25, Box::new(BinderList::Cons(15, 26,
                        Box::new(BinderList::Cons(17, 27, Box::new(BinderList::Nil)))))),
                    BinderList::Cons(23, 1, Box::new(BinderList::Nil)),
                    ParamBoundList::Bound(11, 24, Box::new(ParamBoundList::Nil)),
                    28, 30),
                atom_ob(43)),
            GoalData::All(0, 1, Box::new(GoalData::Let(20, 21, Box::new(
                GoalData::All(23, 1, Box::new(GoalData::Imp(24, Box::new(
                GoalData::Imp(25, Box::new(GoalData::Imp(26, Box::new(
                GoalData::Imp(27, Box::new(GoalData::Imp(30, Box::new(
                GoalData::LeafE(ExprData::Atom(43)))))))))))))))))),
        ) == 1
by { decide }

// ── bootstrap-17: If-with-early-return fall-through (§2.4.1) ────────
//
// `if C { return } rest` — the then-branch DIVERGES, so production reaches
// `rest` only via the else path and visits the continuation under `¬C`
// (production clones `after` into both branches; the diverging then-clone
// yields no goals). refWp reproduces this with `frame_after(f, If) = f ++
// FHyp(nc)` guarded by `diverges(then) && is_skip(else)`, and the
// then-branch hyp is the annotated cond `c` (byte-matching production's
// `Wp::Branch` `cond_marked` — the serializer mints `c`/`nc` via
// `oblig_leaf`/`neg_oblig_leaf`). Verified end-to-end against the real
// find_square cert: with this fix the FULL 17-goal find_square bridge
// closes by `decide` (`goals_eq (ref_wp ctx sst) goals = 1`), including the
// previously-excluded goals 6–11.
//
// This test isolates the mechanism on a minimal diverging-then If and its
// NON-diverging contrast, so a regression flips `goals_eq`:
//   `if C { return 9 } ; assert P`  under a pre-if hyp `[34]`
// → then-goal `[34]→[36:C]→ let(8:=9) Leaf 7` (the Ret ens, under annotated
//   cond 36) THEN continuation `[34]→[37:¬C]→ Leaf 40` (the assert, under
//   the forwarded ¬cond 37). The CONTRAST (then = Skip, non-diverging)
//   forwards NO ¬cond: just `[34]→ Leaf 40`. Mutation-kill: dropping the
//   fall-through `FHyp(nc)` (pre-b17 `frame_after(f,If)=f`) removes `Imp 37`
//   from the diverging continuation; forwarding it unconditionally adds a
//   spurious `Imp 37` to the contrast. Either flips a `goals_eq`.
proof fn ref_wp_if_fallthrough_divergence()
    ensures
        // DIVERGING then (`Ret` inside) + Skip else ⇒ continuation sees ¬cond.
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FHyp(0, 34, Box::new(FrameList::FNil)),
                StmData::Seq(
                    Box::new(StmData::If(36, 0, 37, 0, Box::new(StmData::Seq(
                            Box::new(StmData::Ret(
                                Box::new(RawExpList::Cons(Box::new(atom_ob(7)), Box::new(RawExpList::Nil))),
                                RetBind::RetLet(8, 9))),
                            Box::new(StmData::Skip))), Box::new(StmData::Skip))),
                    Box::new(StmData::Assert(atom_ob(40), 0, 39)))),
            GoalList::Cons(
                // S3-pre prefix latch: the two leading hyps (ambient 34,
                // annotated cond 36) extract to NAMED binders in this
                // wrap goal (the RetLet is the first let-class frame).
                Box::new(GoalData::All(0, 34, Box::new(GoalData::All(0, 36,
                    Box::new(GoalData::Let(8, 9, Box::new(GoalData::LeafE(ExprData::Atom(7))))))))),
                Box::new(GoalList::Cons(
                    Box::new(GoalData::All(0, 34, Box::new(GoalData::All(0, 37,
                        Box::new(GoalData::LeafE(ExprData::Atom(40))))))),
                    Box::new(GoalList::Nil)))),
        ) == 1,
        // NON-diverging then (Skip) + Skip else ⇒ NO ¬cond forwarded: the
        // continuation assert closes under the bare pre-if frame `[34]`.
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FHyp(0, 34, Box::new(FrameList::FNil)),
                StmData::Seq(
                    Box::new(StmData::If(36, 0, 37, 0, Box::new(StmData::Skip), Box::new(StmData::Skip))),
                    Box::new(StmData::Assert(atom_ob(40), 0, 39)))),
            GoalList::Cons(
                Box::new(GoalData::All(0, 34, Box::new(GoalData::LeafE(ExprData::Atom(40))))),
                Box::new(GoalList::Nil)),
        ) == 1
by { decide }

// ── bootstrap-19: the two-way If-join (count_down) — Option 2 ────────
//
// `count_down(n) { if n==0 {0} else {count_down(n-1)} }` — BOTH branches
// fall through to a common `Ret`. Production computes `wp(if C {t} else {e},
// wp(rest, post))`: it CLONES the continuation `rest` into BOTH branch frames,
// so the trailing `Ret` yields one postcondition goal PER branch (4 goals),
// not one under the bare pre-If frame.
//
// refWp is FROZEN: teaching `wp_stm` the two-way join forces the branch
// subterms to match-depth 2, which the Lean backend lowers to
// `WellFounded.fix` (a `termination_by`), and `decide` cannot reduce that —
// it breaks EVERY Seq bridge (the bootstrap-19 finding, evidenced by 20
// decide-stuck errors). So the SERIALIZER desugars instead (Option 2,
// sst_serialize::block): `Seq(If(t,e), rest)` → `If(t;rest, e;rest)`. refWp's
// existing FLAT If/Seq arms (depth-1 structural recursion) then reproduce
// production's goals — and STILL kernel-compute.
//
// This literal is the REAL on-disk count_down cert AFTER the desugar
// (machine-transcribed from bootstrap-fixture/out/lib/cert/count_down.cert
// .lean): the SST is `Seq(Assign(decrease_init0:=n), If(then;Ret, else;Ret))`
// — the trailing Ret cloned into each branch. It IS the count_down bridge (the
// probe9 runner elaborates the same `goals_eq` against the emitted defs). It
// doubles as a regression guard on the FROZEN refWp: if a future refWp change
// stops reproducing the join from the desugared SST, this decide flips.
// Mutation-kill: refWp's goal 0 (then-branch postcond) binds `let tmp__3 := 0`
// (val leaf 11 from the cloned then-branch); a goal 0 expecting `:= 99` fails.
pub open spec fn cd19_ctx() -> FnCtxData { FnCtxData { typ_params: BinderList::Nil, params: BinderList::Cons(0, 1, Box::new(BinderList::Nil)), param_bounds: ParamBoundList::Bound(3, 2, Box::new(ParamBoundList::Nil)), reqs: BinderList::Nil, mut_params: MutParamList::Nil, enss: LeafList::Cons(4, Box::new(LeafList::Nil)), residue_names: LeafList::Nil, prop_deeps: PropDeepList::Nil, closer_default: 1 } }
pub open spec fn cd19_sst() -> StmData { StmData::Seq(Box::new(StmData::Assign(7, 0)), Box::new(StmData::If(8, 0, 9, 0, Box::new(StmData::Seq(Box::new(StmData::Assign(10, 11)), Box::new(StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(5)), Box::new(RawExpList::Nil))), RetBind::RetLet(6, 10))))), Box::new(StmData::Seq(Box::new(StmData::Seq(Box::new(StmData::Seq(Box::new(StmData::Assert(atom_ob(13), 0, 12)), Box::new(StmData::Seq(Box::new(StmData::Assume(0, 12)), Box::new(StmData::Seq(Box::new(StmData::Assign(14, 15)), Box::new(StmData::Seq(Box::new(StmData::Assert(atom_ob(17), 0, 16)), Box::new(StmData::Call { reqs: Box::new(RawExpList::Nil), post: Box::new(FrameList::FHyp(0, 20, Box::new(FrameList::FLet(18, 19, Box::new(FrameList::FNil))))) }))))))))), Box::new(StmData::Assign(10, 18)))), Box::new(StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(5)), Box::new(RawExpList::Nil))), RetBind::RetLet(6, 10)))))))) }
pub open spec fn cd19_goals() -> GoalList { GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::Let(7, 0, Box::new(GoalData::Imp(8, Box::new(GoalData::Let(10, 11, Box::new(GoalData::Let(6, 10, Box::new(GoalData::LeafE(ExprData::Atom(5))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::Let(7, 0, Box::new(GoalData::Imp(9, Box::new(GoalData::LeafE(ExprData::Atom(13))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::Let(7, 0, Box::new(GoalData::Imp(9, Box::new(GoalData::Imp(12, Box::new(GoalData::Imp(12, Box::new(GoalData::Let(14, 15, Box::new(GoalData::LeafE(ExprData::Atom(17))))))))))))))))), Box::new(GoalList::Cons(Box::new(GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::Let(7, 0, Box::new(GoalData::Imp(9, Box::new(GoalData::Imp(12, Box::new(GoalData::Imp(12, Box::new(GoalData::Let(14, 15, Box::new(GoalData::Imp(16, Box::new(GoalData::Imp(20, Box::new(GoalData::Let(18, 19, Box::new(GoalData::Let(10, 18, Box::new(GoalData::Let(6, 10, Box::new(GoalData::LeafE(ExprData::Atom(5))))))))))))))))))))))))))), Box::new(GoalList::Nil)))))))) }

proof fn ref_wp_if_twoway_join()
    ensures
        goals_eq(ref_wp(cd19_ctx(), cd19_sst()), cd19_goals()) == 1,
        goal_count(ref_wp(cd19_ctx(), cd19_sst())) == 4,
        goal_eq(gl_head(ref_wp(cd19_ctx(), cd19_sst())), GoalData::All(0, 1, Box::new(GoalData::All(3, 2, Box::new(GoalData::Let(7, 0, Box::new(GoalData::Imp(8, Box::new(GoalData::Let(10, 99, Box::new(GoalData::Let(6, 10, Box::new(GoalData::LeafE(ExprData::Atom(5))))))))))))))) == 0
by { decide }

// ── bootstrap-02b: the Call pass-through, both post-frame shapes ────
//
// "Lowering the mirror" (DESIGN-W2-refwp.md §2.6): the reshaped
// `Call { reqs, post: FrameList }` makes refWp a pass-through — `wp_stm`
// closes each req obligation under the pre-call frame, `frame_after`
// appends `post` verbatim — so BOTH production post-call frame shapes
// (`push_post_call_frames`) reproduce production's goals through the SAME
// refWp arm. This is the `double_exec`-shaped validation the design note
// asks for (one ret-eq, one ∀-path) before the serializer's `post`-builder
// is wired.
//
// Model: `let a = double_exec(x); assert Q` under a one-hyp ambient frame
// `[100]` (standing in for the seed telescope). The call emits ONE
// precondition obligation (`double_exec`'s requires, instantiated →
// CallPrecondition leaf 7) and appends `post`; the following assert closes
// its obligation (leaf 11) under `[100] ++ post`.
//
// * RET-EQ (#128): `double_exec` ensures `r == 2*x`, so production drops the
//   `∀ a`: `post = FHyp(E_bound=9) FLet(a=8, 2*x=10)`. The continuation is
//   `100 → (0≤2x∧2x<2^64) → let a := 2x; Q` — no quantifier. (Post-N1
//   the plain FLet gates this goal to WRAP mode; S3-pre extracts the
//   leading hyps to NAMED binders up to the FLet latch;
//   the let-free req goal and ∀-path goal HOIST — All-rendered.)
// * ∀-PATH: a callee whose ensures is NOT a ret-eq (e.g. `r > x`) quantifies
//   the result: `post = FBind(a=8, u64=1) FHyp(ret_bound=9) FHyp(ens=13)`.
//   The continuation is `100 → ∀a, (0≤a∧a<2^64) → (a>x) → Q`.
//
// Both certify the SAME `Call { reqs: [7], post }` node through the pass-
// through — the only difference is the `post` the serializer will build.
// Mutation-kill (negative control the card asks for): swapping the bound
// value E in `let a := E` (10 → 99) flips `goals_eq` to 0.
proof fn ref_wp_call_pass_through()
    ensures
        // RET-EQ post: no ∀; E_bound hyp then a `let a := 2*x`.
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FHyp(0, 100, Box::new(FrameList::FNil)),
                StmData::Seq(
                    Box::new(StmData::Call {
                        reqs: Box::new(RawExpList::Cons(Box::new(atom_ob(7)), Box::new(RawExpList::Nil))),
                        post: Box::new(FrameList::FHyp(0, 9, Box::new(FrameList::FLet(8, 10, Box::new(FrameList::FNil))))),
                    }),
                    Box::new(StmData::Assert(atom_ob(11), 0, 12)))),
            GoalList::Cons(
                Box::new(GoalData::All(0, 100, Box::new(GoalData::LeafE(ExprData::Atom(7))))),
                Box::new(GoalList::Cons(
                    // S3-pre prefix latch: the ambient hyp + E_bound hyp
                    // lead this wrap goal (FLet(a) is the latch) — NAMED.
                    Box::new(GoalData::All(0, 100, Box::new(GoalData::All(0, 9,
                        Box::new(GoalData::Let(8, 10, Box::new(GoalData::LeafE(ExprData::Atom(11))))))))),
                    Box::new(GoalList::Nil)))),
        ) == 1,
        // ∀-PATH post: quantify the result, then ret_bound → ens hyps.
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FHyp(0, 100, Box::new(FrameList::FNil)),
                StmData::Seq(
                    Box::new(StmData::Call {
                        reqs: Box::new(RawExpList::Cons(Box::new(atom_ob(7)), Box::new(RawExpList::Nil))),
                        post: Box::new(FrameList::FBind(8, 1,
                            Box::new(FrameList::FHyp(0, 9, Box::new(FrameList::FHyp(0, 13, Box::new(FrameList::FNil))))))),
                    }),
                    Box::new(StmData::Assert(atom_ob(11), 0, 12)))),
            GoalList::Cons(
                Box::new(GoalData::All(0, 100, Box::new(GoalData::LeafE(ExprData::Atom(7))))),
                Box::new(GoalList::Cons(
                    Box::new(GoalData::All(0, 100, Box::new(GoalData::All(8, 1,
                        Box::new(GoalData::All(0, 9, Box::new(GoalData::All(0, 13,
                            Box::new(GoalData::LeafE(ExprData::Atom(11))))))))))),
                    Box::new(GoalList::Nil)))),
        ) == 1,
        // Mutation-kill: the ret-eq goals with a WRONG let value (10 → 99)
        // must NOT match — the bridge is sensitive to the transcribed E.
        goals_eq(
            wp_stm(LeafList::Nil, 
                FrameList::FHyp(0, 100, Box::new(FrameList::FNil)),
                StmData::Seq(
                    Box::new(StmData::Call {
                        reqs: Box::new(RawExpList::Cons(Box::new(atom_ob(7)), Box::new(RawExpList::Nil))),
                        post: Box::new(FrameList::FHyp(0, 9, Box::new(FrameList::FLet(8, 10, Box::new(FrameList::FNil))))),
                    }),
                    Box::new(StmData::Assert(atom_ob(11), 0, 12)))),
            GoalList::Cons(
                Box::new(GoalData::All(0, 100, Box::new(GoalData::LeafE(ExprData::Atom(7))))),
                Box::new(GoalList::Cons(
                    // Same S3-pre shape as the positive pin — the ONLY
                    // difference is the let value (10 → 99), so the kill
                    // stays non-vacuous.
                    Box::new(GoalData::All(0, 100, Box::new(GoalData::All(0, 9,
                        Box::new(GoalData::Let(8, 99, Box::new(GoalData::LeafE(ExprData::Atom(11))))))))),
                    Box::new(GoalList::Nil)))),
        ) == 0
by { decide }

// Mutation sensitivity (DESIGN §2.4.2): goal_eq flips on a single leaf-id
// change, a binder-id change, or a constructor (structure) change.
proof fn goal_eq_strictness()
    ensures
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(6)) == 0,
        goal_eq(GoalData::Leaf(5), GoalData::Leaf(5)) == 1,
        // differing binder id
        goal_eq(
            GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
            GoalData::All(7, 1, Box::new(GoalData::Leaf(9)))) == 0,
        // differing hyp leaf inside an Imp
        goal_eq(
            GoalData::Imp(2, Box::new(GoalData::Leaf(9))),
            GoalData::Imp(3, Box::new(GoalData::Leaf(9)))) == 0,
        // All vs Imp (structure)
        goal_eq(
            GoalData::All(0, 1, Box::new(GoalData::Leaf(9))),
            GoalData::Imp(1, Box::new(GoalData::Leaf(9)))) == 0,
        // goals_eq flips when a goal is dropped (length mismatch)
        goals_eq(
            GoalList::Cons(Box::new(GoalData::Leaf(9)), Box::new(GoalList::Nil)),
            GoalList::Nil) == 0
by { decide }

// ── W6b: the additive LeafE goal variant threads the goal_eq bridge ──
//
// Verdict-neutral — refWp does NOT yet emit `LeafE` (`close` still produces
// `Leaf(u64)`); W6c wires the serializer. This pins that a `LeafE` wrapping
// a rendered expr kernel-computes through `goal_eq`/`goals_eq`/`goal_size`:
// a LeafE of the Case-B expr matches itself, the inconsistent mutation does
// NOT, a LeafE vs a stage-A u64 `Leaf` is a structural (tag) mismatch, and a
// goals list carrying a LeafE decides.
proof fn leafe_goal_bridge_kernel_computes()
    ensures
        goal_eq(
            GoalData::LeafE(ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))))),
            GoalData::LeafE(ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3))))))
        ) == 1,
        goal_eq(
            GoalData::LeafE(ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))))),
            GoalData::LeafE(ExprData::BinOp(1,
                Box::new(ExprData::Cast(CastKind::IntToNat, Box::new(ExprData::Atom(3)))),
                Box::new(ExprData::Atom(3))))
        ) == 0,
        // LeafE vs a stage-A u64 Leaf: tag mismatch either way.
        goal_eq(GoalData::LeafE(ExprData::Atom(5)), GoalData::Leaf(5)) == 0,
        goal_eq(GoalData::Leaf(5), GoalData::LeafE(ExprData::Atom(5))) == 0,
        // goals_eq threads a LeafE goal.
        goals_eq(
            GoalList::Cons(Box::new(GoalData::LeafE(ExprData::Atom(9))), Box::new(GoalList::Nil)),
            GoalList::Cons(Box::new(GoalData::LeafE(ExprData::Atom(9))), Box::new(GoalList::Nil))
        ) == 1,
        // goal_size counts a LeafE as one spine node (like Leaf).
        goal_size(GoalData::Imp(7, Box::new(GoalData::LeafE(ExprData::Atom(9))))) == 2
by { decide }

proof fn amended_shapes_kernel_compute()
    ensures
        // Loop: 1 + |inv_hyps=1| + |inv_obligs=1| + |inv_obligs_exit=1|
        // + |inv_obligs_break=0| + |binders=1| + size(setup Skip=1)
        // + size(body Skip=1) == 7 (binder_bounds is a ParamBoundList —
        // not counted, mirroring the serializer's `stm_size_of` token
        // sum; the scalar leaves add 0; W6d.1b-iii added the parallel
        // deep-obligation `inv_obligs` RawExpList, counted via
        // `raw_exp_list_len`; bootstrap-79 counts `inv_obligs_break` and
        // the `setup` stm the same way).
        stm_size(StmData::Loop {
            inv_hyps: Box::new(BinderList::Cons(0, 10, Box::new(BinderList::Nil))),
            inv_obligs: Box::new(RawExpList::Cons(Box::new(atom_ob(10)), Box::new(RawExpList::Nil))),
            inv_obligs_exit: Box::new(RawExpList::Cons(Box::new(atom_ob(12)), Box::new(RawExpList::Nil))),
            inv_obligs_break: Box::new(RawExpList::Nil),
            binders: Box::new(BinderList::Cons(3, 4, Box::new(BinderList::Nil))),
            binder_bounds: Box::new(ParamBoundList::Bound(20, 21, Box::new(ParamBoundList::Nil))),
            cond_name: 5,
            cond_ann: 1,
            neg_cond_ann: 2,
            neg_neg_cond_ann: 999999,
            break_guard_ann: 999999,
            break_use_ann: 999999,
            d_old_name: 6,
            d_old_ty: 4,
            d_old_val: 7,
            d_old_eq_name: 9,
            d_old_eq_prop: 11,
            decrease_oblig: atom_ob(8),
            setup: Box::new(StmData::Skip),
            body: Box::new(StmData::Skip),
        }) == 7,
        // Call: 1 + |reqs=1| + frame_len(post = FBind(5,6,FNil) = 1) == 3
        stm_size(StmData::Call {
            reqs: Box::new(RawExpList::Cons(Box::new(atom_ob(0)), Box::new(RawExpList::Nil))),
            post: Box::new(FrameList::FBind(5, 6, Box::new(FrameList::FNil))),
        }) == 3,
        // Ret: 1 + |es=2| == 3 (RetBind adds no statements to the size).
        stm_size(StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(0)),
            Box::new(RawExpList::Cons(Box::new(atom_ob(1)), Box::new(RawExpList::Nil))))), RetBind::RetNone)) == 3,
        stm_size(StmData::Ret(Box::new(RawExpList::Cons(Box::new(atom_ob(0)),
            Box::new(RawExpList::Cons(Box::new(atom_ob(1)), Box::new(RawExpList::Nil))))), RetBind::RetLet(23, 9))) == 3,
        binder_len(BinderList::Cons(1, 2, Box::new(BinderList::Nil))) == 1,
        param_bound_len(ParamBoundList::Bound(4, 5,
            Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil))))) == 2,
        frame_len(FrameList::FBind(1, 2,
            Box::new(FrameList::FHyp(0, 3, Box::new(FrameList::FLet(4, 5, Box::new(FrameList::FNil))))))) == 3,
        // FnCtxData projection: 2 value params.
        fnctx_arity(FnCtxData {
            typ_params: BinderList::Cons(0, 100, Box::new(BinderList::Nil)),
            params: BinderList::Cons(1, 101,
                Box::new(BinderList::Cons(2, 102, Box::new(BinderList::Nil)))),
            param_bounds: ParamBoundList::Bound(199, 200,
                Box::new(ParamBoundList::NoBound(Box::new(ParamBoundList::Nil)))),
            reqs: BinderList::Nil,
            mut_params: MutParamList::Nil,
            enss: LeafList::Cons(300, Box::new(LeafList::Nil)),
            residue_names: LeafList::Nil,
            prop_deeps: PropDeepList::Nil,
            closer_default: 1,
        }) == 2
by {
    decide
}

// ═════════════════════════════════════════════════════════════════════
// W5 SEMANTIC MODEL (bootstrap-61) — the operational side of the
// soundness loop, authored per the hand-Lean probes (probe21–26, probe24
// = the frame-carrying W5c formulation) in the shape frozen by probe33
// (bootstrap-60). Valuation-parametric (DESIGN-W5-soundness.md §1 opt b):
// three opaque leaf oracles, a function-typed state, and a semantic
// telescope with the continuation DEFUNCTIONALIZED into the exact two
// shapes `exec_safe_f` needs (`close_sem_e` = one deep obligation;
// `close_sem_obligs` = an obligation list) — no higher-order continuation
// params, no ContK datatype (probe33 REPORT, frozen interface).
//
// Authoring discipline (probe33 F1/F2, binding here and in the proofs):
// facts can NEVER be injected under a binder (proof-fn calls inside
// `assert forall … by` are dropped by the backend), so every
// state-dependent lemma over these defs is ST-GENERIC — ∀st lives in the
// ENSURES. The soundness proofs (bootstrap-62..64) build on that idiom.
// ═════════════════════════════════════════════════════════════════════

/// The semantic state: an assignment of Int values to interned binder
/// ids (hand-Lean `St := Int → Int`).
pub type St = spec_fn(u64) -> int;

/// Opaque prop-leaf oracle (hypotheses + stage-A `Leaf` obligations).
pub type HpOracle = spec_fn(u64, St) -> bool;
/// Deep-obligation oracle (`render_exp` output stays opaque to W5).
pub type HeOracle = spec_fn(ExprData, St) -> bool;
/// Let-value oracle (`FLet` / `GoalData::Let` / `RetLet` value leaves).
pub type LvOracle = spec_fn(u64, St) -> int;

/// Point-update on the semantic state (spec closure — probe33 M1).
pub open spec fn upd(st: St, x: u64, n: int) -> St {
    |k: u64| if k == x { n } else { st(k) }
}

/// Goal denotation (Val-level toProp), faithful on every GoalData arm.
#[verifier::structural_decreases]
pub open spec fn holds(hp: HpOracle, he: HeOracle, lv: LvOracle, g: GoalData, st: St) -> bool
    decreases g
{
    match g {
        GoalData::Leaf(id) => hp(id, st),
        GoalData::Imp(h, t) => hp(h, st) ==> holds(hp, he, lv, *t, st),
        GoalData::All(x, _ty, t) =>
            forall|n: int| #[trigger] holds(hp, he, lv, *t, upd(st, x, n)),
        GoalData::Let(x, v, t) => holds(hp, he, lv, *t, upd(st, x, lv(v, st))),
        GoalData::LeafE(e) => he(e, st),
    }
}

#[verifier::structural_decreases]
pub open spec fn holds_all(hp: HpOracle, he: HeOracle, lv: LvOracle, gs: GoalList, st: St) -> bool
    decreases gs
{
    match gs {
        GoalList::Nil => true,
        GoalList::Cons(g, t) => holds(hp, he, lv, *g, st) && holds_all(hp, he, lv, *t, st),
    }
}

/// The conjunction of DEEP obligations in a RawExpList at a state (the
/// semantic content of a `close_each_e` list — Call reqs / Ret enss /
/// Loop init + maintain-reclose invariants).
#[verifier::structural_decreases]
pub open spec fn obligs_safe(he: HeOracle, l: RawExpList, st: St) -> bool
    decreases l
{
    match l {
        RawExpList::Nil => true,
        RawExpList::Cons(h, t) => he(render_exp(*h), st) && obligs_safe(he, *t, st),
    }
}

/// Frame-telescope interpretation, continuation = "the deep obligation
/// `o` holds at the inner state" (FBind→∀, FHyp→→, FLet/FLetR→let). The
/// defunctionalized form of hand-Lean
/// `closeSem f st (fun st' => he (render_exp o) st')`.
#[verifier::structural_decreases]
pub open spec fn close_sem_e_wrap(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, o: RawExp) -> bool
    decreases f
{
    match f {
        FrameList::FNil => he(render_exp(o), st),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_e_wrap(hp, he, lv, *t, upd(st, x, n), o),
        FrameList::FHyp(_hn, h, t) => hp(h, st) ==> close_sem_e_wrap(hp, he, lv, *t, st, o),
        FrameList::FLet(x, v, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FLetH(x, _ty, v, _en, _ep, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FLetR(x, v, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FUserCloser(t) => close_sem_e_wrap(hp, he, lv, *t, st, o),
    }
}

// S3-pre leading sub-mode semantics, moving in step with
// `close_e_wrap_lead`: leading FHyps take the tel-style ABSTRACT-BINDER
// reading (`∀ n, … upd(st, hn, n)` — `holds` reads All as value
// quantification, so the implication reading would break the weave; the
// adequacy layer recovers the dependent-product meaning exactly as it
// already does for hoist-mode named hyps). The first let-class frame
// latches one-way to the plain wrap walk.
#[verifier::structural_decreases]
pub open spec fn close_sem_e_wrap_lead(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, o: RawExp) -> bool
    decreases f
{
    match f {
        FrameList::FNil => he(render_exp(o), st),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_e_wrap_lead(hp, he, lv, *t, upd(st, x, n), o),
        FrameList::FHyp(hn, _h, t) =>
            forall|n: int| #[trigger] close_sem_e_wrap_lead(hp, he, lv, *t, upd(st, hn, n), o),
        FrameList::FLet(x, v, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FLetH(x, _ty, v, _en, _ep, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FLetR(x, v, t) => close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FUserCloser(t) => close_sem_e_wrap_lead(hp, he, lv, *t, st, o),
    }
}

// Hoist-mode semantics — TWO-PHASE, paralleling close_e_tel /
// residue_fold_e arm-for-arm so holds(close_e_hoist …) ==
// close_sem_e_hoist … is a mechanical induction: the telescope phase
// reads named hyps and let-pairs as ∀-binders (the abstract FBind
// reading; the adequacy layer recovers the dependent-product meaning,
// exactly as it already does for the reqs binders) and SKIPS residue
// lets; the residue phase then folds each residue let as a state update
// (the goal-position-Let reading), in frame order. `f0` is the whole
// frame list, carried so the residue phase can walk it at the
// telescope's end.
//
// EVALUATION-CONTEXT NOTE (the adequacy-layer invariant, same class as
// the 0-sentinel collision note): the residue phase evaluates each
// `lv(v, st)` with `st` holding ALL telescope upds — including binders
// that come AFTER the residue let in frame order. Production evaluates
// the residue value in the earlier context. The two readings coincide
// precisely because a residue let's value text mentions only
// EARLIER-bound names (production's textual scoping — invisible here,
// leaves are opaque ids) and freshening keeps binder ids distinct, so
// the extra upds are no-ops on the value's free names. The weave
// (rendering ≡ semantics) is internally consistent regardless; the
// scoping invariant is what the adequacy layer relies on to read the
// abstract model as the real Lean meaning.
#[verifier::structural_decreases]
pub open spec fn close_sem_e_tel(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, f0: FrameList, st: St, o: RawExp) -> bool
    decreases f
{
    match f {
        FrameList::FNil => close_sem_e_res(hp, he, lv, f0, st, o),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(st, x, n), o),
        FrameList::FHyp(hn, _h, t) =>
            forall|n: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(st, hn, n), o),
        FrameList::FLet(x, v, t) => close_sem_e_tel(hp, he, lv, *t, f0, upd(st, x, lv(v, st)), o),
        FrameList::FLetH(x, _ty, _v, en, _ep, t) =>
            forall|a: int, b: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(upd(st, x, a), en, b), o),
        FrameList::FLetR(_x, _v, t) => close_sem_e_tel(hp, he, lv, *t, f0, st, o),
        FrameList::FUserCloser(t) => close_sem_e_tel(hp, he, lv, *t, f0, st, o),
    }
}

#[verifier::structural_decreases]
pub open spec fn close_sem_e_res(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, o: RawExp) -> bool
    decreases f
{
    match f {
        FrameList::FNil => he(render_exp(o), st),
        FrameList::FLetR(x, v, t) => close_sem_e_res(hp, he, lv, *t, upd(st, x, lv(v, st)), o),
        FrameList::FBind(_x, _ty, t) => close_sem_e_res(hp, he, lv, *t, st, o),
        FrameList::FHyp(_hn, _h, t) => close_sem_e_res(hp, he, lv, *t, st, o),
        FrameList::FLet(_x, _v, t) => close_sem_e_res(hp, he, lv, *t, st, o),
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => close_sem_e_res(hp, he, lv, *t, st, o),
        FrameList::FUserCloser(t) => close_sem_e_res(hp, he, lv, *t, st, o),
    }
}

pub open spec fn close_sem_e_hoist(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, o: RawExp) -> bool {
    close_sem_e_tel(hp, he, lv, f, f, st, o)
}

pub open spec fn close_sem_e(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, o: RawExp) -> bool {
    if gate_wrap(pp, f) == 1 { close_sem_e_wrap_lead(hp, he, lv, f, st, o) } else { close_sem_e_hoist(hp, he, lv, f, st, o) }
}

/// Frame-telescope interpretation, continuation = "every obligation in
/// `l` holds at the inner state" (the second and last continuation shape
/// `exec_safe_f` needs).
#[verifier::structural_decreases]
pub open spec fn close_sem_obligs_wrap(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, l: RawExpList) -> bool
    decreases f
{
    match f {
        FrameList::FNil => obligs_safe(he, l, st),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, n), l),
        FrameList::FHyp(_hn, h, t) => hp(h, st) ==> close_sem_obligs_wrap(hp, he, lv, *t, st, l),
        FrameList::FLet(x, v, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FLetH(x, _ty, v, _en, _ep, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FLetR(x, v, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FUserCloser(t) => close_sem_obligs_wrap(hp, he, lv, *t, st, l),
    }
}

// S3-pre leading sub-mode, `obligs_safe` continuation (same prefix
// latch as `close_sem_e_wrap_lead`).
#[verifier::structural_decreases]
pub open spec fn close_sem_obligs_wrap_lead(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, l: RawExpList) -> bool
    decreases f
{
    match f {
        FrameList::FNil => obligs_safe(he, l, st),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, *t, upd(st, x, n), l),
        FrameList::FHyp(hn, _h, t) =>
            forall|n: int| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, *t, upd(st, hn, n), l),
        FrameList::FLet(x, v, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FLetH(x, _ty, v, _en, _ep, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FLetR(x, v, t) => close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FUserCloser(t) => close_sem_obligs_wrap_lead(hp, he, lv, *t, st, l),
    }
}

// Hoist-mode obligs semantics — the same two-phase split as
// close_sem_e_hoist (telescope skips residue lets; residue phase folds
// them as state updates), with the `obligs_safe` continuation.
#[verifier::structural_decreases]
pub open spec fn close_sem_obligs_tel(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, f0: FrameList, st: St, l: RawExpList) -> bool
    decreases f
{
    match f {
        FrameList::FNil => close_sem_obligs_res(hp, he, lv, f0, st, l),
        FrameList::FBind(x, _ty, t) =>
            forall|n: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, x, n), l),
        FrameList::FHyp(hn, _h, t) =>
            forall|n: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, hn, n), l),
        FrameList::FLet(x, v, t) => close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, x, lv(v, st)), l),
        FrameList::FLetH(x, _ty, _v, en, _ep, t) =>
            forall|a: int, b: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(upd(st, x, a), en, b), l),
        FrameList::FLetR(_x, _v, t) => close_sem_obligs_tel(hp, he, lv, *t, f0, st, l),
        FrameList::FUserCloser(t) => close_sem_obligs_tel(hp, he, lv, *t, f0, st, l),
    }
}

#[verifier::structural_decreases]
pub open spec fn close_sem_obligs_res(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, l: RawExpList) -> bool
    decreases f
{
    match f {
        FrameList::FNil => obligs_safe(he, l, st),
        FrameList::FLetR(x, v, t) => close_sem_obligs_res(hp, he, lv, *t, upd(st, x, lv(v, st)), l),
        FrameList::FBind(_x, _ty, t) => close_sem_obligs_res(hp, he, lv, *t, st, l),
        FrameList::FHyp(_hn, _h, t) => close_sem_obligs_res(hp, he, lv, *t, st, l),
        FrameList::FLet(_x, _v, t) => close_sem_obligs_res(hp, he, lv, *t, st, l),
        FrameList::FLetH(_x, _ty, _v, _en, _ep, t) => close_sem_obligs_res(hp, he, lv, *t, st, l),
        FrameList::FUserCloser(t) => close_sem_obligs_res(hp, he, lv, *t, st, l),
    }
}

pub open spec fn close_sem_obligs_hoist(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, l: RawExpList) -> bool {
    close_sem_obligs_tel(hp, he, lv, f, f, st, l)
}

pub open spec fn close_sem_obligs(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, st: St, l: RawExpList) -> bool {
    if gate_wrap(pp, f) == 1 { close_sem_obligs_wrap_lead(hp, he, lv, f, st, l) } else { close_sem_obligs_hoist(hp, he, lv, f, st, l) }
}

/// Operational safety — FRAME-CARRYING (the W5c lift, probe24): mirrors
/// `wp_stm f s`'s frame threading; each obligation is closed under the
/// frame that precedes it, sequential composition threads `frame_after`,
/// and the Loop havocs `f` internally through `loop_maintain_frame` —
/// the havoc'd frames stay opaque, never decomposed. TOTAL on StmData
/// (no fragment predicate). Non-circular: the leaf arms require the
/// ACTUAL obligation (`he(render_exp(o))`), never `true`.
#[verifier::structural_decreases]
pub open spec fn exec_safe_f(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, s: StmData, st: St) -> bool
    decreases s
{
    match s {
        StmData::Assert(o, _hn, _h) => close_sem_e(pp, hp, he, lv, f, st, o),
        StmData::Assume(_hn, _e) => true,
        StmData::Assign(_x, _rhs) => true,
        StmData::AssignH(_x, _ty, _v, _en, _ep) => true,
        StmData::AssignR(_x, _v) => true,
        StmData::Call { reqs, post: _ } => close_sem_obligs(pp, hp, he, lv, f, st, *reqs),
        StmData::DeadEnd(b) => exec_safe_f(pp, hp, he, lv, f, *b, st),
        StmData::AssertQueryNl(b, tq) =>
            exec_safe_f(pp, hp, he, lv, strip_hyps(f), *b, st)
                && close_sem_e(pp, hp, he, lv, frame_after(pp, strip_hyps(f), *b), st, tq),
        // Assert-analogue: the inline-proven P is an obligation (closed
        // under the wrap-forced frame — the marker is semantically
        // transparent, so the meaning matches Assert's).
        StmData::AssertQueryTactus(o, _hn, _h) =>
            close_sem_e(pp, hp, he, lv, frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), st, o),
        StmData::Ret(es, rb) => close_sem_obligs(pp, hp, he, lv, ret_frame(pp, f, rb), st, *es),
        StmData::If(c, cn, nc, ncn, t, e) =>
            exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t, st)
                && exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e, st),
        StmData::IfCtor { pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els } =>
            exec_safe_f(pp, hp, he, lv, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn, st)
                && exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els, st),
        StmData::Loop { inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann: _, neg_neg_cond_ann, break_guard_ann, break_use_ann: _, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body } => {
            if is_skip(*setup) == 1 {
            let mframe = loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop);
            let endf = frame_after(pp, mframe, *body);
            close_sem_obligs(pp, hp, he, lv, f, st, *inv_obligs)
                && exec_safe_f(pp, hp, he, lv, mframe, *body, st)
                && close_sem_obligs(pp, hp, he, lv, endf, st, *inv_obligs_exit)
                && close_sem_e(pp, hp, he, lv, endf, st, decrease_oblig)
            } else {
            // Break-form (bootstrap-79): the semantic analog of the
            // three-family goal list — init under the pre-loop frame,
            // setup body-run under the d_old ctx, exit-reclose under
            // ctx+¬cond, body under ctx+¬(¬cond), maintain-reclose and
            // decrease at body end, then the exit-side setup replay
            // under the bare base.
            let base = loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds);
            let mframe0 = frame_append(base, d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop));
            let setup_end = frame_after(pp, mframe0, *setup);
            let exit_frame = frame_append(setup_end, FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil)));
            let guard_frame = frame_append(setup_end, FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil)));
            let endf = frame_after(pp, guard_frame, *body);
            close_sem_obligs(pp, hp, he, lv, f, st, *inv_obligs)
                && exec_safe_f(pp, hp, he, lv, mframe0, *setup, st)
                && close_sem_obligs(pp, hp, he, lv, exit_frame, st, *inv_obligs_break)
                && exec_safe_f(pp, hp, he, lv, guard_frame, *body, st)
                && close_sem_obligs(pp, hp, he, lv, endf, st, *inv_obligs_exit)
                && close_sem_e(pp, hp, he, lv, endf, st, decrease_oblig)
                && exec_safe_f(pp, hp, he, lv, base, *setup, st)
            }
        },
        StmData::Skip => true,
        StmData::Seq(a, b) =>
            exec_safe_f(pp, hp, he, lv, f, *a, st)
                && exec_safe_f(pp, hp, he, lv, frame_after(pp, f, *a), *b, st),
    }
}

// ── W5 model one-step unfold pins (the u_* idiom, probe32/33): the
//    backend gives height-recursive spec fns no Lean eq-lemmas, so these
//    st-generic empty-body lemmas both PIN that every arm emits and
//    unfolds kernel-clean, and serve the soundness proofs as arm-body
//    rewrite rules (∀st-equations usable under binders — probe33 F2). ──

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_leaf(hp: HpOracle, he: HeOracle, lv: LvOracle, id: u64)
    ensures forall|st: St| #[trigger] holds(hp, he, lv, GoalData::Leaf(id), st) == hp(id, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_imp(hp: HpOracle, he: HeOracle, lv: LvOracle, h: u64, t: Box<GoalData>)
    ensures forall|st: St| #[trigger] holds(hp, he, lv, GoalData::Imp(h, t), st)
        == (hp(h, st) ==> holds(hp, he, lv, *t, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_binder(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<GoalData>)
    ensures forall|st: St| #[trigger] holds(hp, he, lv, GoalData::All(x, ty, t), st)
        == (forall|n: int| #[trigger] holds(hp, he, lv, *t, upd(st, x, n)))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<GoalData>)
    ensures forall|st: St| #[trigger] holds(hp, he, lv, GoalData::Let(x, v, t), st)
        == holds(hp, he, lv, *t, upd(st, x, lv(v, st)))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_leafe(hp: HpOracle, he: HeOracle, lv: LvOracle, e: ExprData)
    ensures forall|st: St| #[trigger] holds(hp, he, lv, GoalData::LeafE(e), st) == he(e, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_nil(hp: HpOracle, he: HeOracle, lv: LvOracle)
    ensures forall|st: St| #[trigger] holds_all(hp, he, lv, GoalList::Nil, st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_holds_all_cons(hp: HpOracle, he: HeOracle, lv: LvOracle, g: Box<GoalData>, t: Box<GoalList>)
    ensures forall|st: St| #[trigger] holds_all(hp, he, lv, GoalList::Cons(g, t), st)
        == (holds(hp, he, lv, *g, st) && holds_all(hp, he, lv, *t, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_obligs_nil(he: HeOracle)
    ensures forall|st: St| #[trigger] obligs_safe(he, RawExpList::Nil, st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_obligs_cons(he: HeOracle, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] obligs_safe(he, RawExpList::Cons(h, t), st)
        == (he(render_exp(*h), st) && obligs_safe(he, *t, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cse_nil(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e(pp, hp, he, lv, FrameList::FNil, st, o)
        == he(render_exp(o), st)
{}
// Post-N1: per-MODE one-step semantic unfolds (dispatcher-level cons
// unfolds are false across mode boundaries — see the close_e pin note).
// Dispatch pins first.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all [lib.close_sem_e])")]
pub proof fn u_cse_wrap_mode(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures gate_wrap(pp, f) == 1 ==> forall|st: St| #[trigger] close_sem_e(pp, hp, he, lv, f, st, o)
        == close_sem_e_wrap_lead(hp, he, lv, f, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all [lib.close_sem_e])")]
pub proof fn u_cse_hoist_mode(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures gate_wrap(pp, f) != 1 ==> forall|st: St| #[trigger] close_sem_e(pp, hp, he, lv, f, st, o)
        == close_sem_e_hoist(hp, he, lv, f, st, o)
{}

// close_sem_e_wrap one-step unfolds.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FNil, st, o)
        == he(render_exp(o), st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FBind(x, ty, t), st, o)
        == (forall|n: int| #[trigger] close_sem_e_wrap(hp, he, lv, *t, upd(st, x, n), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FHyp(n, h, t), st, o)
        == (hp(h, st) ==> close_sem_e_wrap(hp, he, lv, *t, st, o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FLet(x, v, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FLetR(x, v, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csew_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap(hp, he, lv, FrameList::FUserCloser(t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, st, o)
{}

// close_sem_e_wrap_lead one-step unfolds (S3-pre leading sub-mode; the
// let-class arms are the one-way latch into the plain wrap walk).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FNil, st, o)
        == he(render_exp(o), st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FBind(x, ty, t), st, o)
        == (forall|n: int| #[trigger] close_sem_e_wrap_lead(hp, he, lv, *t, upd(st, x, n), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FHyp(n, h, t), st, o)
        == (forall|m: int| #[trigger] close_sem_e_wrap_lead(hp, he, lv, *t, upd(st, n, m), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FLet(x, v, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FLetR(x, v, t), st, o)
        == close_sem_e_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csewl_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_wrap_lead(hp, he, lv, FrameList::FUserCloser(t), st, o)
        == close_sem_e_wrap_lead(hp, he, lv, *t, st, o)
{}

// close_sem_e_hoist = tel ∘ res (two-phase). One-step unfolds are
// per-PHASE: hoist-level cons unfolds would have to commute the residue
// walk past the head frame (true but not rfl — the phase pins are the
// rewrite rules the soundness proofs use).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cseh_unfold(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_hoist(hp, he, lv, f, st, o)
        == close_sem_e_tel(hp, he, lv, f, f, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FNil, f0, st, o)
        == close_sem_e_res(hp, he, lv, f0, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FBind(x, ty, t), f0, st, o)
        == (forall|n: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(st, x, n), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FHyp(n, h, t), f0, st, o)
        == (forall|v: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(st, n, v), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FLet(x, v, t), f0, st, o)
        == close_sem_e_tel(hp, he, lv, *t, f0, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), f0, st, o)
        == (forall|a: int, b: int| #[trigger] close_sem_e_tel(hp, he, lv, *t, f0, upd(upd(st, x, a), en, b), o))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FLetR(x, v, t), f0, st, o)
        == close_sem_e_tel(hp, he, lv, *t, f0, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cset_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, f0: FrameList, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_tel(hp, he, lv, FrameList::FUserCloser(t), f0, st, o)
        == close_sem_e_tel(hp, he, lv, *t, f0, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FNil, st, o)
        == he(render_exp(o), st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FLetR(x, v, t), st, o)
        == close_sem_e_res(hp, he, lv, *t, upd(st, x, lv(v, st)), o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FBind(x, ty, t), st, o)
        == close_sem_e_res(hp, he, lv, *t, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FHyp(n, h, t), st, o)
        == close_sem_e_res(hp, he, lv, *t, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FLet(x, v, t), st, o)
        == close_sem_e_res(hp, he, lv, *t, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, o)
        == close_sem_e_res(hp, he, lv, *t, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cser_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, o: RawExp)
    ensures forall|st: St| #[trigger] close_sem_e_res(hp, he, lv, FrameList::FUserCloser(t), st, o)
        == close_sem_e_res(hp, he, lv, *t, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_cso_nil(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs(pp, hp, he, lv, FrameList::FNil, st, l)
        == obligs_safe(he, l, st)
{}
// Post-N1 dispatch + per-mode cso pins (same shape as the cse family).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all [lib.close_sem_obligs])")]
pub proof fn u_cso_wrap_mode(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, l: RawExpList)
    ensures gate_wrap(pp, f) == 1 ==> forall|st: St| #[trigger] close_sem_obligs(pp, hp, he, lv, f, st, l)
        == close_sem_obligs_wrap_lead(hp, he, lv, f, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all [lib.close_sem_obligs])")]
pub proof fn u_cso_hoist_mode(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, l: RawExpList)
    ensures gate_wrap(pp, f) != 1 ==> forall|st: St| #[trigger] close_sem_obligs(pp, hp, he, lv, f, st, l)
        == close_sem_obligs_hoist(hp, he, lv, f, st, l)
{}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FNil, st, l)
        == obligs_safe(he, l, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FBind(x, ty, t), st, l)
        == (forall|n: int| #[trigger] close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, n), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FHyp(n, h, t), st, l)
        == (hp(h, st) ==> close_sem_obligs_wrap(hp, he, lv, *t, st, l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FLet(x, v, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FLetR(x, v, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csow_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, FrameList::FUserCloser(t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, st, l)
{}

// close_sem_obligs_wrap_lead one-step unfolds (S3-pre).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FNil, st, l)
        == obligs_safe(he, l, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FBind(x, ty, t), st, l)
        == (forall|n: int| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, *t, upd(st, x, n), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FHyp(n, h, t), st, l)
        == (forall|m: int| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, *t, upd(st, n, m), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FLet(x, v, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FLetR(x, v, t), st, l)
        == close_sem_obligs_wrap(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csowl_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, FrameList::FUserCloser(t), st, l)
        == close_sem_obligs_wrap_lead(hp, he, lv, *t, st, l)
{}

// Hoist-mode obligs: the tel/res two-phase pins (mirror of the cse
// family above, with the obligs_safe continuation).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csoh_unfold(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_hoist(hp, he, lv, f, st, l)
        == close_sem_obligs_tel(hp, he, lv, f, f, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FNil, f0, st, l)
        == close_sem_obligs_res(hp, he, lv, f0, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FBind(x, ty, t), f0, st, l)
        == (forall|n: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, x, n), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FHyp(n, h, t), f0, st, l)
        == (forall|v: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, n, v), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FLet(x, v, t), f0, st, l)
        == close_sem_obligs_tel(hp, he, lv, *t, f0, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), f0, st, l)
        == (forall|a: int, b: int| #[trigger] close_sem_obligs_tel(hp, he, lv, *t, f0, upd(upd(st, x, a), en, b), l))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FLetR(x, v, t), f0, st, l)
        == close_sem_obligs_tel(hp, he, lv, *t, f0, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csot_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, f0: FrameList, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, FrameList::FUserCloser(t), f0, st, l)
        == close_sem_obligs_tel(hp, he, lv, *t, f0, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_nil(hp: HpOracle, he: HeOracle, lv: LvOracle, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FNil, st, l)
        == obligs_safe(he, l, st)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_letr(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FLetR(x, v, t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, upd(st, x, lv(v, st)), l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_bind(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FBind(x, ty, t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_hyp(hp: HpOracle, he: HeOracle, lv: LvOracle, n: u64, h: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FHyp(n, h, t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_let(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, v: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FLet(x, v, t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_leth(hp: HpOracle, he: HeOracle, lv: LvOracle, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FLetH(x, ty, v, en, ep, t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_csor_ucl(hp: HpOracle, he: HeOracle, lv: LvOracle, t: Box<FrameList>, l: RawExpList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, FrameList::FUserCloser(t), st, l)
        == close_sem_obligs_res(hp, he, lv, *t, st, l)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_assert(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp, hn: u64, h: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Assert(o, hn, h), st)
        == close_sem_e(pp, hp, he, lv, f, st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_assume(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, hn: u64, e: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Assume(hn, e), st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_assign(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, x: u64, rhs: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Assign(x, rhs), st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_assignh(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, x: u64, ty: u64, v: u64, en: u64, ep: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::AssignH(x, ty, v, en, ep), st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_assignr(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, x: u64, v: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::AssignR(x, v), st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_call(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, reqs: Box<RawExpList>, post: Box<FrameList>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Call { reqs, post }, st)
        == close_sem_obligs(pp, hp, he, lv, f, st, *reqs)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_deadend(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, b: Box<StmData>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::DeadEnd(b), st)
        == exec_safe_f(pp, hp, he, lv, f, *b, st)
{}
pub proof fn u_esf_aqnl(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, b: Box<StmData>, tq: RawExp)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::AssertQueryNl(b, tq), st)
        == (exec_safe_f(pp, hp, he, lv, strip_hyps(f), *b, st)
            && close_sem_e(pp, hp, he, lv, frame_after(pp, strip_hyps(f), *b), st, tq))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_aqt(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp, hn: u64, h: u64)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::AssertQueryTactus(o, hn, h), st)
        == close_sem_e(pp, hp, he, lv, frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), st, o)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_ifctor(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, pos_binders: Box<BinderList>, eq_name: u64, eq_prop: u64, neg_name: u64, neg_prop: u64, thn: Box<StmData>, els: Box<StmData>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::IfCtor { pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els }, st)
        == (exec_safe_f(pp, hp, he, lv, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn, st)
            && exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_ret(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, es: Box<RawExpList>, rb: RetBind)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Ret(es, rb), st)
        == close_sem_obligs(pp, hp, he, lv, ret_frame(pp, f, rb), st, *es)
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_if(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, c: u64, cn: u64, nc: u64, ncn: u64, t: Box<StmData>, e: Box<StmData>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::If(c, cn, nc, ncn, t, e), st)
        == (exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t, st)
            && exec_safe_f(pp, hp, he, lv, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e, st))
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_loop(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList,
    inv_hyps: Box<BinderList>, inv_obligs: Box<RawExpList>, inv_obligs_exit: Box<RawExpList>,
    inv_obligs_break: Box<RawExpList>, binders: Box<BinderList>,
    binder_bounds: Box<ParamBoundList>, cond_name: u64, cond_ann: u64, neg_cond_ann: u64,
    neg_neg_cond_ann: u64, break_guard_ann: u64, break_use_ann: u64, d_old_name: u64, d_old_ty: u64, d_old_val: u64, d_old_eq_name: u64,
    d_old_eq_prop: u64, decrease_oblig: RawExp, setup: Box<StmData>, body: Box<StmData>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        }, st)
        == (if is_skip(*setup) == 1 {
            close_sem_obligs(pp, hp, he, lv, f, st, *inv_obligs)
            && exec_safe_f(pp, hp, he, lv,
                loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop),
                *body, st)
            && close_sem_obligs(pp, hp, he, lv,
                frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body),
                st, *inv_obligs_exit)
            && close_sem_e(pp, hp, he, lv,
                frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body),
                st, decrease_oblig)
        } else {
            close_sem_obligs(pp, hp, he, lv, f, st, *inv_obligs)
            && exec_safe_f(pp, hp, he, lv,
                frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)),
                *setup, st)
            && close_sem_obligs(pp, hp, he, lv,
                frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))),
                st, *inv_obligs_break)
            && exec_safe_f(pp, hp, he, lv,
                frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))),
                *body, st)
            && close_sem_obligs(pp, hp, he, lv,
                frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
                st, *inv_obligs_exit)
            && close_sem_e(pp, hp, he, lv,
                frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
                st, decrease_oblig)
            && exec_safe_f(pp, hp, he, lv,
                loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds),
                *setup, st)
        })
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_skip(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Skip, st) == true
{}
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]
pub proof fn u_esf_seq(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, a: Box<StmData>, b: Box<StmData>)
    ensures forall|st: St| #[trigger] exec_safe_f(pp, hp, he, lv, f, StmData::Seq(a, b), st)
        == (exec_safe_f(pp, hp, he, lv, f, *a, st)
            && exec_safe_f(pp, hp, he, lv, frame_after(pp, f, *a), *b, st))
{}

// ── W5 data-side one-step unfolds (bootstrap-62): the reference fns the
//    soundness proofs rewrite with. Data-only (no st) — probe32 empty
//    shape, default closer. ──

// Post-N1 (bootstrap-74): close_e is a gated dispatcher, so one-step
// unfolds are stated per MODE fn — a dispatcher-level cons unfold would
// be false whenever head and tail dispatch differently (e.g. FLet head
// forces wrap but a let-free tail re-dispatches hoist).

// Gate one-step pins.
pub proof fn u_gate_nil()
    ensures has_plain_flet(FrameList::FNil) == 0
{}
pub proof fn u_gate_bind(x: u64, ty: u64, t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FBind(x, ty, t)) == has_plain_flet(*t)
{}
pub proof fn u_gate_hyp(n: u64, h: u64, t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FHyp(n, h, t)) == has_plain_flet(*t)
{}
pub proof fn u_gate_let(x: u64, v: u64, t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FLet(x, v, t)) == 1
{}
pub proof fn u_gate_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FLetH(x, ty, v, en, ep, t)) == has_plain_flet(*t)
{}
pub proof fn u_gate_letr(x: u64, v: u64, t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FLetR(x, v, t)) == has_plain_flet(*t)
{}
pub proof fn u_gate_ucl(t: Box<FrameList>)
    ensures has_plain_flet(FrameList::FUserCloser(t)) == has_plain_flet(*t)
{}

// Poison-gate one-step pins.
pub proof fn u_gatep_nil(pp: LeafList, )
    ensures has_poisoned_hyp(pp, FrameList::FNil) == 0
{}
pub proof fn u_gatep_bind(pp: LeafList, x: u64, ty: u64, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FBind(x, ty, t)) == has_poisoned_hyp(pp, *t)
{}
pub proof fn u_gatep_hyp(pp: LeafList, n: u64, h: u64, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FHyp(n, h, t)) == (if leaf_mem(pp, h) == 1 { 1 } else { has_poisoned_hyp(pp, *t) })
{}
pub proof fn u_gatep_let(pp: LeafList, x: u64, v: u64, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FLet(x, v, t)) == has_poisoned_hyp(pp, *t)
{}
pub proof fn u_gatep_leth(pp: LeafList, x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FLetH(x, ty, v, en, ep, t)) == has_poisoned_hyp(pp, *t)
{}
pub proof fn u_gatep_letr(pp: LeafList, x: u64, v: u64, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FLetR(x, v, t)) == has_poisoned_hyp(pp, *t)
{}
pub proof fn u_gatep_ucl(pp: LeafList, t: Box<FrameList>)
    ensures has_poisoned_hyp(pp, FrameList::FUserCloser(t)) == has_poisoned_hyp(pp, *t)
{}

// User-closer-gate one-step pins (R1, bootstrap-77).
pub proof fn u_gateu_nil()
    ensures has_user_closer(FrameList::FNil) == 0
{}
pub proof fn u_gateu_bind(x: u64, ty: u64, t: Box<FrameList>)
    ensures has_user_closer(FrameList::FBind(x, ty, t)) == has_user_closer(*t)
{}
pub proof fn u_gateu_hyp(n: u64, h: u64, t: Box<FrameList>)
    ensures has_user_closer(FrameList::FHyp(n, h, t)) == has_user_closer(*t)
{}
pub proof fn u_gateu_let(x: u64, v: u64, t: Box<FrameList>)
    ensures has_user_closer(FrameList::FLet(x, v, t)) == has_user_closer(*t)
{}
pub proof fn u_gateu_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>)
    ensures has_user_closer(FrameList::FLetH(x, ty, v, en, ep, t)) == has_user_closer(*t)
{}
pub proof fn u_gateu_letr(x: u64, v: u64, t: Box<FrameList>)
    ensures has_user_closer(FrameList::FLetR(x, v, t)) == has_user_closer(*t)
{}
pub proof fn u_gateu_ucl(t: Box<FrameList>)
    ensures has_user_closer(FrameList::FUserCloser(t)) == 1
{}

// Dispatch pins (conditional): which mode fn the dispatcher selects.
// REQUIRES-FREE (the gate rides in the ensures as an implication):
// requires-carrying pins called under an `if` emit branch-guarded
// precondition VCs the Link discharge spine cannot yet compose —
// implication-form pins keep every caller straight-line.
pub proof fn u_ce_wrap_mode(pp: LeafList, f: FrameList, ob: RawExp)
    ensures gate_wrap(pp, f) == 1 ==> close_e(pp, f, ob) == close_e_wrap_lead(f, ob)
{}
pub proof fn u_ce_hoist_mode(pp: LeafList, f: FrameList, ob: RawExp)
    ensures gate_wrap(pp, f) != 1 ==> close_e(pp, f, ob) == close_e_hoist(f, ob)
{}

// close_e_wrap one-step unfolds.
pub proof fn u_cew_nil(ob: RawExp)
    ensures close_e_wrap(FrameList::FNil, ob) == GoalData::LeafE(render_exp(ob))
{}
pub proof fn u_cew_bind(x: u64, ty: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FBind(x, ty, t), ob) == GoalData::All(x, ty, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cew_hyp(n: u64, h: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FHyp(n, h, t), ob) == GoalData::Imp(h, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cew_let(x: u64, v: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FLet(x, v, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cew_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FLetH(x, ty, v, en, ep, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cew_letr(x: u64, v: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FLetR(x, v, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cew_ucl(t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap(FrameList::FUserCloser(t), ob) == close_e_wrap(*t, ob)
{}

// close_e_wrap_lead one-step unfolds (S3-pre leading sub-mode).
pub proof fn u_cewl_nil(ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FNil, ob) == GoalData::LeafE(render_exp(ob))
{}
pub proof fn u_cewl_bind(x: u64, ty: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FBind(x, ty, t), ob) == GoalData::All(x, ty, Box::new(close_e_wrap_lead(*t, ob)))
{}
pub proof fn u_cewl_hyp(n: u64, h: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FHyp(n, h, t), ob) == GoalData::All(n, h, Box::new(close_e_wrap_lead(*t, ob)))
{}
pub proof fn u_cewl_let(x: u64, v: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FLet(x, v, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cewl_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FLetH(x, ty, v, en, ep, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cewl_letr(x: u64, v: u64, t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FLetR(x, v, t), ob) == GoalData::Let(x, v, Box::new(close_e_wrap(*t, ob)))
{}
pub proof fn u_cewl_ucl(t: Box<FrameList>, ob: RawExp)
    ensures close_e_wrap_lead(FrameList::FUserCloser(t), ob) == close_e_wrap_lead(*t, ob)
{}

// close_e_hoist = close_e_tel ∘ residue_fold_e (two-phase, mirroring
// production's binder pass + residue fold). One-step unfolds are
// per-PHASE (see the semantic pin note).
pub proof fn u_ceh_unfold(f: FrameList, ob: RawExp)
    ensures close_e_hoist(f, ob)
        == close_e_tel(f, residue_fold_e(f, GoalData::LeafE(render_exp(ob))))
{}
pub proof fn u_cet_nil(g: GoalData)
    ensures close_e_tel(FrameList::FNil, g) == g
{}
pub proof fn u_cet_bind(x: u64, ty: u64, t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FBind(x, ty, t), g) == GoalData::All(x, ty, Box::new(close_e_tel(*t, g)))
{}
pub proof fn u_cet_hyp(n: u64, h: u64, t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FHyp(n, h, t), g) == GoalData::All(n, h, Box::new(close_e_tel(*t, g)))
{}
pub proof fn u_cet_let(x: u64, v: u64, t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FLet(x, v, t), g) == GoalData::Let(x, v, Box::new(close_e_tel(*t, g)))
{}
pub proof fn u_cet_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FLetH(x, ty, v, en, ep, t), g)
        == GoalData::All(x, ty, Box::new(GoalData::All(en, ep, Box::new(close_e_tel(*t, g)))))
{}
pub proof fn u_cet_letr(x: u64, v: u64, t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FLetR(x, v, t), g) == close_e_tel(*t, g)
{}
pub proof fn u_cet_ucl(t: Box<FrameList>, g: GoalData)
    ensures close_e_tel(FrameList::FUserCloser(t), g) == close_e_tel(*t, g)
{}
pub proof fn u_cer_nil(g: GoalData)
    ensures residue_fold_e(FrameList::FNil, g) == g
{}
pub proof fn u_cer_letr(x: u64, v: u64, t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FLetR(x, v, t), g) == GoalData::Let(x, v, Box::new(residue_fold_e(*t, g)))
{}
pub proof fn u_cer_bind(x: u64, ty: u64, t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FBind(x, ty, t), g) == residue_fold_e(*t, g)
{}
pub proof fn u_cer_hyp(n: u64, h: u64, t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FHyp(n, h, t), g) == residue_fold_e(*t, g)
{}
pub proof fn u_cer_let(x: u64, v: u64, t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FLet(x, v, t), g) == residue_fold_e(*t, g)
{}
pub proof fn u_cer_leth(x: u64, ty: u64, v: u64, en: u64, ep: u64, t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FLetH(x, ty, v, en, ep, t), g) == residue_fold_e(*t, g)
{}
pub proof fn u_cer_ucl(t: Box<FrameList>, g: GoalData)
    ensures residue_fold_e(FrameList::FUserCloser(t), g) == residue_fold_e(*t, g)
{}
pub proof fn u_cce_nil(pp: LeafList, f: FrameList)
    ensures close_each_e(pp, f, RawExpList::Nil) == GoalList::Nil
{}
pub proof fn u_cce_cons(pp: LeafList, f: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures close_each_e(pp, f, RawExpList::Cons(h, t))
        == GoalList::Cons(Box::new(close_e(pp, f, *h)), Box::new(close_each_e(pp, f, *t)))
{}
pub proof fn u_gapp_nil(b: GoalList)
    ensures goals_append(GoalList::Nil, b) == b
{}
pub proof fn u_gapp_cons(h: Box<GoalData>, t: Box<GoalList>, b: GoalList)
    ensures goals_append(GoalList::Cons(h, t), b)
        == GoalList::Cons(h, Box::new(goals_append(*t, b)))
{}
pub proof fn u_wp_assert(pp: LeafList, f: FrameList, o: RawExp, hn: u64, h: u64)
    ensures wp_stm(pp, f, StmData::Assert(o, hn, h))
        == GoalList::Cons(Box::new(close_e(pp, f, o)), Box::new(GoalList::Nil))
{}
pub proof fn u_wp_assume(pp: LeafList, f: FrameList, hn: u64, e: u64)
    ensures wp_stm(pp, f, StmData::Assume(hn, e)) == GoalList::Nil
{}
pub proof fn u_wp_assign(pp: LeafList, f: FrameList, x: u64, rhs: u64)
    ensures wp_stm(pp, f, StmData::Assign(x, rhs)) == GoalList::Nil
{}
pub proof fn u_wp_assignh(pp: LeafList, f: FrameList, x: u64, ty: u64, v: u64, en: u64, ep: u64)
    ensures wp_stm(pp, f, StmData::AssignH(x, ty, v, en, ep)) == GoalList::Nil
{}
pub proof fn u_wp_assignr(pp: LeafList, f: FrameList, x: u64, v: u64)
    ensures wp_stm(pp, f, StmData::AssignR(x, v)) == GoalList::Nil
{}
pub proof fn u_wp_call(pp: LeafList, f: FrameList, reqs: Box<RawExpList>, post: Box<FrameList>)
    ensures wp_stm(pp, f, StmData::Call { reqs, post }) == close_each_e(pp, f, *reqs)
{}
pub proof fn u_wp_deadend(pp: LeafList, f: FrameList, b: Box<StmData>)
    ensures wp_stm(pp, f, StmData::DeadEnd(b)) == wp_stm(pp, f, *b)
{}
pub proof fn u_wp_aqnl(pp: LeafList, f: FrameList, b: Box<StmData>, tq: RawExp)
    ensures wp_stm(pp, f, StmData::AssertQueryNl(b, tq))
        == goals_append(
            wp_stm(pp, strip_hyps(f), *b),
            GoalList::Cons(
                Box::new(close_e(pp, frame_after(pp, strip_hyps(f), *b), tq)),
                Box::new(GoalList::Nil)))
{}
pub proof fn u_wp_aqt(pp: LeafList, f: FrameList, o: RawExp, hn: u64, h: u64)
    ensures wp_stm(pp, f, StmData::AssertQueryTactus(o, hn, h))
        == GoalList::Cons(
            Box::new(close_e(pp, frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), o)),
            Box::new(GoalList::Nil))
{}
pub proof fn u_wp_ifctor(pp: LeafList, f: FrameList, pos_binders: Box<BinderList>, eq_name: u64, eq_prop: u64, neg_name: u64, neg_prop: u64, thn: Box<StmData>, els: Box<StmData>)
    ensures wp_stm(pp, f, StmData::IfCtor { pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els })
        == goals_append(
            wp_stm(pp, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn),
            wp_stm(pp, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els))
{}
pub proof fn u_wp_ret(pp: LeafList, f: FrameList, es: Box<RawExpList>, rb: RetBind)
    ensures wp_stm(pp, f, StmData::Ret(es, rb)) == close_each_e(pp, ret_frame(pp, f, rb), *es)
{}
pub proof fn u_wp_if(pp: LeafList, f: FrameList, c: u64, cn: u64, nc: u64, ncn: u64, t: Box<StmData>, e: Box<StmData>)
    ensures wp_stm(pp, f, StmData::If(c, cn, nc, ncn, t, e))
        == goals_append(
            wp_stm(pp, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t),
            wp_stm(pp, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e))
{}
pub proof fn u_wp_loop(pp: LeafList, f: FrameList,
    inv_hyps: Box<BinderList>, inv_obligs: Box<RawExpList>, inv_obligs_exit: Box<RawExpList>,
    inv_obligs_break: Box<RawExpList>, binders: Box<BinderList>,
    binder_bounds: Box<ParamBoundList>, cond_name: u64, cond_ann: u64, neg_cond_ann: u64,
    neg_neg_cond_ann: u64, break_guard_ann: u64, break_use_ann: u64, d_old_name: u64, d_old_ty: u64, d_old_val: u64, d_old_eq_name: u64,
    d_old_eq_prop: u64, decrease_oblig: RawExp, setup: Box<StmData>, body: Box<StmData>)
    ensures wp_stm(pp, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        })
        == (if is_skip(*setup) == 1 {
            goals_append(close_each_e(pp, f, *inv_obligs),
                goals_append(
                    wp_stm(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body),
                    goals_append(
                        close_each_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), *inv_obligs_exit),
                        GoalList::Cons(
                            Box::new(close_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig)),
                            Box::new(GoalList::Nil)))))
        } else {
            goals_append(close_each_e(pp, f, *inv_obligs),
                goals_append(
                    wp_stm(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup),
                    goals_append(
                        close_each_e(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))), *inv_obligs_break),
                        goals_append(
                            wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
                            goals_append(
                                close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
                                goals_append(
                                    GoalList::Cons(
                                        Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)),
                                        Box::new(GoalList::Nil)),
                                    wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup)))))))
        })
{}
pub proof fn u_wp_skip(pp: LeafList, f: FrameList)
    ensures wp_stm(pp, f, StmData::Skip) == GoalList::Nil
{}
pub proof fn u_wp_seq(pp: LeafList, f: FrameList, a: Box<StmData>, b: Box<StmData>)
    ensures wp_stm(pp, f, StmData::Seq(a, b))
        == goals_append(wp_stm(pp, f, *a), wp_stm(pp, frame_after(pp, f, *a), *b))
{}

// ── W5 support lemma A (bootstrap-62, hand-Lean `holds_close_e`): a
//    frame-closed obligation goal holds iff the obligation holds under the
//    frame's ∀/→/let telescope. ST-GENERIC (probe33 idiom): induction over
//    f, IH + unfolds as plain arm-body calls, ∀st-equations rewrite under
//    the FBind binder in the postcondition VC. ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_close_e_wrap(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, close_e_wrap(f, o), st) == close_sem_e_wrap(hp, he, lv, f, st, o)
    decreases f
{
    match f {
        FrameList::FNil => {
            u_cew_nil(o);
            u_holds_leafe(hp, he, lv, render_exp(o));
            u_csew_nil(hp, he, lv, o);
        }
        FrameList::FBind(x, ty, t) => {
            u_cew_bind(x, ty, t, o);
            u_holds_all_binder(hp, he, lv, x, ty, Box::new(close_e_wrap(*t, o)));
            u_csew_bind(hp, he, lv, x, ty, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_cew_hyp(hn, h, t, o);
            u_holds_imp(hp, he, lv, h, Box::new(close_e_wrap(*t, o)));
            u_csew_hyp(hp, he, lv, hn, h, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_cew_let(x, v, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csew_let(hp, he, lv, x, v, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_cew_leth(x, ty, v, en, ep, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csew_leth(hp, he, lv, x, ty, v, en, ep, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FLetR(x, v, t) => {
            u_cew_letr(x, v, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csew_letr(hp, he, lv, x, v, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_cew_ucl(t, o);
            u_csew_ucl(hp, he, lv, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // IH (st-generic)
        }
    }
}

// Leading sub-mode weave (S3-pre): the FHyp arm reads the named binder
// on BOTH sides (`u_holds_all_binder` — All is value-quantification,
// exactly the hoist-mode telescope treatment); the let-class arms hand
// off to the PLAIN wrap weave at the latch point.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_close_e_wrap_lead(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, close_e_wrap_lead(f, o), st) == close_sem_e_wrap_lead(hp, he, lv, f, st, o)
    decreases f
{
    match f {
        FrameList::FNil => {
            u_cewl_nil(o);
            u_holds_leafe(hp, he, lv, render_exp(o));
            u_csewl_nil(hp, he, lv, o);
        }
        FrameList::FBind(x, ty, t) => {
            u_cewl_bind(x, ty, t, o);
            u_holds_all_binder(hp, he, lv, x, ty, Box::new(close_e_wrap_lead(*t, o)));
            u_csewl_bind(hp, he, lv, x, ty, t, o);
            holds_close_e_wrap_lead(hp, he, lv, *t, o);         // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_cewl_hyp(hn, h, t, o);
            u_holds_all_binder(hp, he, lv, hn, h, Box::new(close_e_wrap_lead(*t, o)));
            u_csewl_hyp(hp, he, lv, hn, h, t, o);
            holds_close_e_wrap_lead(hp, he, lv, *t, o);         // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_cewl_let(x, v, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csewl_let(hp, he, lv, x, v, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // latch → plain weave
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_cewl_leth(x, ty, v, en, ep, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csewl_leth(hp, he, lv, x, ty, v, en, ep, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // latch → plain weave
        }
        FrameList::FLetR(x, v, t) => {
            u_cewl_letr(x, v, t, o);
            u_holds_let(hp, he, lv, x, v, Box::new(close_e_wrap(*t, o)));
            u_csewl_letr(hp, he, lv, x, v, t, o);
            holds_close_e_wrap(hp, he, lv, *t, o);              // latch → plain weave
        }
        FrameList::FUserCloser(t) => {
            u_cewl_ucl(t, o);
            u_csewl_ucl(hp, he, lv, t, o);
            holds_close_e_wrap_lead(hp, he, lv, *t, o);         // IH (st-generic)
        }
    }
}

// Hoist-mode analog, TWO-PHASE (bootstrap-74 slice 2): close_e_hoist =
// close_e_tel ∘ residue_fold_e, so the weave splits into a residue
// lemma (the folded Lets read as state updates) and a telescope lemma
// (named hyps and let-pairs are ∀-binders on BOTH sides — the FLetH arm
// applies the All unfold TWICE for the binder pair). The telescope
// lemma's continuation is the residue-folded leaf, so it inducts with
// f0 (the whole frame list) FIXED.

// Residue phase: holds of the residue-folded leaf == the residue
// semantic walk. FLetR's Let reads via u_holds_let; every other frame
// is skipped by BOTH sides.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_residue_fold(hp: HpOracle, he: HeOracle, lv: LvOracle, f0: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, residue_fold_e(f0, GoalData::LeafE(render_exp(o))), st)
            == close_sem_e_res(hp, he, lv, f0, st, o)
    decreases f0
{
    match f0 {
        FrameList::FNil => {
            u_cer_nil(GoalData::LeafE(render_exp(o)));
            u_holds_leafe(hp, he, lv, render_exp(o));
            u_cser_nil(hp, he, lv, o);
        }
        FrameList::FLetR(x, v, t) => {
            u_cer_letr(x, v, t, GoalData::LeafE(render_exp(o)));
            u_holds_let(hp, he, lv, x, v, Box::new(residue_fold_e(*t, GoalData::LeafE(render_exp(o)))));
            u_cser_letr(hp, he, lv, x, v, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FBind(x, ty, t) => {
            u_cer_bind(x, ty, t, GoalData::LeafE(render_exp(o)));
            u_cser_bind(hp, he, lv, x, ty, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_cer_hyp(hn, h, t, GoalData::LeafE(render_exp(o)));
            u_cser_hyp(hp, he, lv, hn, h, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_cer_let(x, v, t, GoalData::LeafE(render_exp(o)));
            u_cser_let(hp, he, lv, x, v, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_cer_leth(x, ty, v, en, ep, t, GoalData::LeafE(render_exp(o)));
            u_cser_leth(hp, he, lv, x, ty, v, en, ep, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_cer_ucl(t, GoalData::LeafE(render_exp(o)));
            u_cser_ucl(hp, he, lv, t, o);
            holds_residue_fold(hp, he, lv, *t, o);              // IH (st-generic)
        }
    }
}

// Telescope phase: holds of the telescope wrapped around the
// residue-folded leaf == the telescope semantic walk (which hands off
// to the residue walk at FNil — the holds_residue_fold lemma).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_close_tel(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, f0: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, close_e_tel(f, residue_fold_e(f0, GoalData::LeafE(render_exp(o)))), st)
            == close_sem_e_tel(hp, he, lv, f, f0, st, o)
    decreases f
{
    match f {
        FrameList::FNil => {
            u_cet_nil(residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_cset_nil(hp, he, lv, f0, o);
            holds_residue_fold(hp, he, lv, f0, o);
        }
        FrameList::FBind(x, ty, t) => {
            u_cet_bind(x, ty, t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_holds_all_binder(hp, he, lv, x, ty,
                Box::new(close_e_tel(*t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))))));
            u_cset_bind(hp, he, lv, x, ty, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_cet_hyp(hn, h, t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_holds_all_binder(hp, he, lv, hn, h,
                Box::new(close_e_tel(*t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))))));
            u_cset_hyp(hp, he, lv, hn, h, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_cet_let(x, v, t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_holds_let(hp, he, lv, x, v,
                Box::new(close_e_tel(*t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))))));
            u_cset_let(hp, he, lv, x, v, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_cet_leth(x, ty, v, en, ep, t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_holds_all_binder(hp, he, lv, x, ty,
                Box::new(GoalData::All(en, ep,
                    Box::new(close_e_tel(*t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))))))));
            u_holds_all_binder(hp, he, lv, en, ep,
                Box::new(close_e_tel(*t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))))));
            u_cset_leth(hp, he, lv, x, ty, v, en, ep, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
        FrameList::FLetR(x, v, t) => {
            u_cet_letr(x, v, t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_cset_letr(hp, he, lv, x, v, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_cet_ucl(t, residue_fold_e(f0, GoalData::LeafE(render_exp(o))));
            u_cset_ucl(hp, he, lv, t, f0, o);
            holds_close_tel(hp, he, lv, *t, f0, o);              // IH (st-generic)
        }
    }
}

// The composed hoist weave: close_e_hoist unfolds to the two-phase
// composition, and holds_close_tel at f0 := f closes it.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
pub proof fn holds_close_e_hoist(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, close_e_hoist(f, o), st) == close_sem_e_hoist(hp, he, lv, f, st, o)
{
    u_ceh_unfold(f, o);
    u_cseh_unfold(hp, he, lv, f, o);
    holds_close_tel(hp, he, lv, f, f, o);
}

// The gated dispatcher — ORIGINAL statement, so every downstream caller
// (wp_stm_sound, holds_all_close_each_e) is untouched. Mode decided once
// over the whole frame list, mirroring production's hoist_all.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> by_cases _hgate : lib.gate_wrap pp f = 1 <;> simp_all)")]
pub proof fn holds_close_e(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, o: RawExp)
    ensures forall|st: St|
        #[trigger] holds(hp, he, lv, close_e(pp, f, o), st) == close_sem_e(pp, hp, he, lv, f, st, o)
{
    u_ce_wrap_mode(pp, f, o);
    u_cse_wrap_mode(pp, hp, he, lv, f, o);
    holds_close_e_wrap_lead(hp, he, lv, f, o);
    u_ce_hoist_mode(pp, f, o);
    u_cse_hoist_mode(pp, hp, he, lv, f, o);
    holds_close_e_hoist(hp, he, lv, f, o);
}

// ── W5 support lemma D (bootstrap-62, hand-Lean `holdsAll_append`):
//    holds_all distributes over goals_append. st stays a PARAM (no binder
//    crossed in the GoalList induction — probe33 idiom note 2). ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_all_append(hp: HpOracle, he: HeOracle, lv: LvOracle, a: GoalList, b: GoalList, st: St)
    ensures holds_all(hp, he, lv, goals_append(a, b), st)
        == (holds_all(hp, he, lv, a, st) && holds_all(hp, he, lv, b, st))
    decreases a
{
    match a {
        GoalList::Nil => {
            u_gapp_nil(b);
            u_holds_all_nil(hp, he, lv);
        }
        GoalList::Cons(g, t) => {
            u_gapp_cons(g, t, b);
            u_holds_all_cons(hp, he, lv, g, t);
            u_holds_all_cons(hp, he, lv, g, Box::new(goals_append(*t, b)));
            holds_all_append(hp, he, lv, *t, b, st);            // IH
        }
    }
}

// ── W5 obligs-bridge structure lemmas (bootstrap-63). With the
//    defunctionalized continuations, hand-Lean's closeSem congr/triv/
//    mono/and helper zoo collapses into two telescope inductions:
//    triviality on Nil and ∧-splitting on Cons. Both ST-GENERIC. ──

// close_sem_obligs over the empty list is trivially true through any
// telescope (hand-Lean `closeSem_triv` specialized).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn cso_nil_true_wrap(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, f, st, RawExpList::Nil) == true
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csow_nil(hp, he, lv, RawExpList::Nil);
            u_obligs_nil(he);
        }
        FrameList::FBind(x, ty, t) => {
            u_csow_bind(hp, he, lv, x, ty, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_csow_hyp(hp, he, lv, hn, h, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_csow_let(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_csow_leth(hp, he, lv, x, ty, v, en, ep, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
        FrameList::FLetR(x, v, t) => {
            u_csow_letr(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_csow_ucl(hp, he, lv, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // IH (st-generic)
        }
    }
}

// Leading sub-mode triviality (S3-pre): let-class arms hand off to the
// plain wrap lemma at the latch point.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn cso_nil_true_wrap_lead(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, f, st, RawExpList::Nil) == true
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csowl_nil(hp, he, lv, RawExpList::Nil);
            u_obligs_nil(he);
        }
        FrameList::FBind(x, ty, t) => {
            u_csowl_bind(hp, he, lv, x, ty, t, RawExpList::Nil);
            cso_nil_true_wrap_lead(hp, he, lv, *t);             // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_csowl_hyp(hp, he, lv, hn, h, t, RawExpList::Nil);
            cso_nil_true_wrap_lead(hp, he, lv, *t);             // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_csowl_let(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // latch → plain
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_csowl_leth(hp, he, lv, x, ty, v, en, ep, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // latch → plain
        }
        FrameList::FLetR(x, v, t) => {
            u_csowl_letr(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_wrap(hp, he, lv, *t);                  // latch → plain
        }
        FrameList::FUserCloser(t) => {
            u_csowl_ucl(hp, he, lv, t, RawExpList::Nil);
            cso_nil_true_wrap_lead(hp, he, lv, *t);             // IH (st-generic)
        }
    }
}

// Hoist side, TWO-PHASE: tel-phase triviality inducts with f0 fixed and
// hands off to the res-phase lemma at FNil.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn cso_nil_true_res(hp: HpOracle, he: HeOracle, lv: LvOracle, f0: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, f0, st, RawExpList::Nil) == true
    decreases f0
{
    match f0 {
        FrameList::FNil => {
            u_csor_nil(hp, he, lv, RawExpList::Nil);
            u_obligs_nil(he);
        }
        FrameList::FLetR(x, v, t) => {
            u_csor_letr(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
        FrameList::FBind(x, ty, t) => {
            u_csor_bind(hp, he, lv, x, ty, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_csor_hyp(hp, he, lv, hn, h, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_csor_let(hp, he, lv, x, v, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_csor_leth(hp, he, lv, x, ty, v, en, ep, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_csor_ucl(hp, he, lv, t, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, *t);                   // IH (st-generic)
        }
    }
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn cso_nil_true_tel(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, f0: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, f, f0, st, RawExpList::Nil) == true
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csot_nil(hp, he, lv, f0, RawExpList::Nil);
            cso_nil_true_res(hp, he, lv, f0);
        }
        FrameList::FBind(x, ty, t) => {
            u_csot_bind(hp, he, lv, x, ty, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
        FrameList::FHyp(hn, h, t) => {
            u_csot_hyp(hp, he, lv, hn, h, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
        FrameList::FLet(x, v, t) => {
            u_csot_let(hp, he, lv, x, v, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, t) => {
            u_csot_leth(hp, he, lv, x, ty, v, en, ep, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
        FrameList::FLetR(x, v, t) => {
            u_csot_letr(hp, he, lv, x, v, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
        FrameList::FUserCloser(t) => {
            u_csot_ucl(hp, he, lv, t, f0, RawExpList::Nil);
            cso_nil_true_tel(hp, he, lv, *t, f0);               // IH (st-generic)
        }
    }
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
pub proof fn cso_nil_true_hoist(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs_hoist(hp, he, lv, f, st, RawExpList::Nil) == true
{
    u_csoh_unfold(hp, he, lv, f, RawExpList::Nil);
    cso_nil_true_tel(hp, he, lv, f, f);
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> by_cases _hgate : lib.gate_wrap pp f = 1 <;> simp_all (config := { zetaDelta := true }))")]
pub proof fn cso_nil_true(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList)
    ensures forall|st: St| #[trigger] close_sem_obligs(pp, hp, he, lv, f, st, RawExpList::Nil) == true
{
    u_cso_wrap_mode(pp, hp, he, lv, f, RawExpList::Nil);
    cso_nil_true_wrap_lead(hp, he, lv, f);
    u_cso_hoist_mode(pp, hp, he, lv, f, RawExpList::Nil);
    cso_nil_true_hoist(hp, he, lv, f);
}

// close_sem_obligs over a Cons splits into head (close_sem_e) ∧ tail —
// the ∧ distributes through the whole telescope (hand-Lean
// `closeSem_and_iff` + `closeSem_congr`, collapsed).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))")]
#[verifier::structural_decreases]
pub proof fn cso_cons_split_wrap(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap(hp, he, lv, f, st, RawExpList::Cons(h, t))
        == (close_sem_e_wrap(hp, he, lv, f, st, *h) && close_sem_obligs_wrap(hp, he, lv, f, st, *t))
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csow_nil(hp, he, lv, RawExpList::Cons(h, t));
            u_obligs_cons(he, h, t);
            u_csew_nil(hp, he, lv, *h);
            u_csow_nil(hp, he, lv, *t);
        }
        FrameList::FBind(x, ty, tl) => {
            u_csow_bind(hp, he, lv, x, ty, tl, RawExpList::Cons(h, t));
            u_csew_bind(hp, he, lv, x, ty, tl, *h);
            u_csow_bind(hp, he, lv, x, ty, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
        FrameList::FHyp(hn, hh, tl) => {
            u_csow_hyp(hp, he, lv, hn, hh, tl, RawExpList::Cons(h, t));
            u_csew_hyp(hp, he, lv, hn, hh, tl, *h);
            u_csow_hyp(hp, he, lv, hn, hh, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
        FrameList::FLet(x, v, tl) => {
            u_csow_let(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_csew_let(hp, he, lv, x, v, tl, *h);
            u_csow_let(hp, he, lv, x, v, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, tl) => {
            u_csow_leth(hp, he, lv, x, ty, v, en, ep, tl, RawExpList::Cons(h, t));
            u_csew_leth(hp, he, lv, x, ty, v, en, ep, tl, *h);
            u_csow_leth(hp, he, lv, x, ty, v, en, ep, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
        FrameList::FLetR(x, v, tl) => {
            u_csow_letr(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_csew_letr(hp, he, lv, x, v, tl, *h);
            u_csow_letr(hp, he, lv, x, v, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
        FrameList::FUserCloser(tl) => {
            u_csow_ucl(hp, he, lv, tl, RawExpList::Cons(h, t));
            u_csew_ucl(hp, he, lv, tl, *h);
            u_csow_ucl(hp, he, lv, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // IH (st-generic)
        }
    }
}

// Leading sub-mode ∧-split (S3-pre): the FHyp arm distributes the ∧
// through the abstract ∀-binder exactly as FBind does (forall_and);
// let-class arms hand off to the plain wrap split at the latch point.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))")]
#[verifier::structural_decreases]
pub proof fn cso_cons_split_wrap_lead(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs_wrap_lead(hp, he, lv, f, st, RawExpList::Cons(h, t))
        == (close_sem_e_wrap_lead(hp, he, lv, f, st, *h) && close_sem_obligs_wrap_lead(hp, he, lv, f, st, *t))
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csowl_nil(hp, he, lv, RawExpList::Cons(h, t));
            u_obligs_cons(he, h, t);
            u_csewl_nil(hp, he, lv, *h);
            u_csowl_nil(hp, he, lv, *t);
        }
        FrameList::FBind(x, ty, tl) => {
            u_csowl_bind(hp, he, lv, x, ty, tl, RawExpList::Cons(h, t));
            u_csewl_bind(hp, he, lv, x, ty, tl, *h);
            u_csowl_bind(hp, he, lv, x, ty, tl, *t);
            cso_cons_split_wrap_lead(hp, he, lv, *tl, h, t);    // IH (st-generic)
        }
        FrameList::FHyp(hn, hh, tl) => {
            u_csowl_hyp(hp, he, lv, hn, hh, tl, RawExpList::Cons(h, t));
            u_csewl_hyp(hp, he, lv, hn, hh, tl, *h);
            u_csowl_hyp(hp, he, lv, hn, hh, tl, *t);
            cso_cons_split_wrap_lead(hp, he, lv, *tl, h, t);    // IH (st-generic)
        }
        FrameList::FLet(x, v, tl) => {
            u_csowl_let(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_csewl_let(hp, he, lv, x, v, tl, *h);
            u_csowl_let(hp, he, lv, x, v, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // latch → plain
        }
        FrameList::FLetH(x, ty, v, en, ep, tl) => {
            u_csowl_leth(hp, he, lv, x, ty, v, en, ep, tl, RawExpList::Cons(h, t));
            u_csewl_leth(hp, he, lv, x, ty, v, en, ep, tl, *h);
            u_csowl_leth(hp, he, lv, x, ty, v, en, ep, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // latch → plain
        }
        FrameList::FLetR(x, v, tl) => {
            u_csowl_letr(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_csewl_letr(hp, he, lv, x, v, tl, *h);
            u_csowl_letr(hp, he, lv, x, v, tl, *t);
            cso_cons_split_wrap(hp, he, lv, *tl, h, t);         // latch → plain
        }
        FrameList::FUserCloser(tl) => {
            u_csowl_ucl(hp, he, lv, tl, RawExpList::Cons(h, t));
            u_csewl_ucl(hp, he, lv, tl, *h);
            u_csowl_ucl(hp, he, lv, tl, *t);
            cso_cons_split_wrap_lead(hp, he, lv, *tl, h, t);    // IH (st-generic)
        }
    }
}

// Hoist analog, TWO-PHASE: the ∧ distributes through the ∀-telescope
// exactly as through FBind in the wrap proof (forall_and) — the FLetH
// arm's two-variable ∀ splits the same way. Tel-phase induction with f0
// fixed; the FNil arm is the res-phase split.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))")]
#[verifier::structural_decreases]
pub proof fn cso_cons_split_res(hp: HpOracle, he: HeOracle, lv: LvOracle, f0: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs_res(hp, he, lv, f0, st, RawExpList::Cons(h, t))
        == (close_sem_e_res(hp, he, lv, f0, st, *h) && close_sem_obligs_res(hp, he, lv, f0, st, *t))
    decreases f0
{
    match f0 {
        FrameList::FNil => {
            u_csor_nil(hp, he, lv, RawExpList::Cons(h, t));
            u_obligs_cons(he, h, t);
            u_cser_nil(hp, he, lv, *h);
            u_csor_nil(hp, he, lv, *t);
        }
        FrameList::FLetR(x, v, tl) => {
            u_csor_letr(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_cser_letr(hp, he, lv, x, v, tl, *h);
            u_csor_letr(hp, he, lv, x, v, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
        FrameList::FBind(x, ty, tl) => {
            u_csor_bind(hp, he, lv, x, ty, tl, RawExpList::Cons(h, t));
            u_cser_bind(hp, he, lv, x, ty, tl, *h);
            u_csor_bind(hp, he, lv, x, ty, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
        FrameList::FHyp(hn, hh, tl) => {
            u_csor_hyp(hp, he, lv, hn, hh, tl, RawExpList::Cons(h, t));
            u_cser_hyp(hp, he, lv, hn, hh, tl, *h);
            u_csor_hyp(hp, he, lv, hn, hh, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
        FrameList::FLet(x, v, tl) => {
            u_csor_let(hp, he, lv, x, v, tl, RawExpList::Cons(h, t));
            u_cser_let(hp, he, lv, x, v, tl, *h);
            u_csor_let(hp, he, lv, x, v, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, tl) => {
            u_csor_leth(hp, he, lv, x, ty, v, en, ep, tl, RawExpList::Cons(h, t));
            u_cser_leth(hp, he, lv, x, ty, v, en, ep, tl, *h);
            u_csor_leth(hp, he, lv, x, ty, v, en, ep, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
        FrameList::FUserCloser(tl) => {
            u_csor_ucl(hp, he, lv, tl, RawExpList::Cons(h, t));
            u_cser_ucl(hp, he, lv, tl, *h);
            u_csor_ucl(hp, he, lv, tl, *t);
            cso_cons_split_res(hp, he, lv, *tl, h, t);          // IH (st-generic)
        }
    }
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))")]
#[verifier::structural_decreases]
pub proof fn cso_cons_split_tel(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, f0: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs_tel(hp, he, lv, f, f0, st, RawExpList::Cons(h, t))
        == (close_sem_e_tel(hp, he, lv, f, f0, st, *h) && close_sem_obligs_tel(hp, he, lv, f, f0, st, *t))
    decreases f
{
    match f {
        FrameList::FNil => {
            u_csot_nil(hp, he, lv, f0, RawExpList::Cons(h, t));
            u_cset_nil(hp, he, lv, f0, *h);
            u_csot_nil(hp, he, lv, f0, *t);
            cso_cons_split_res(hp, he, lv, f0, h, t);
        }
        FrameList::FBind(x, ty, tl) => {
            u_csot_bind(hp, he, lv, x, ty, tl, f0, RawExpList::Cons(h, t));
            u_cset_bind(hp, he, lv, x, ty, tl, f0, *h);
            u_csot_bind(hp, he, lv, x, ty, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
        FrameList::FHyp(hn, hh, tl) => {
            u_csot_hyp(hp, he, lv, hn, hh, tl, f0, RawExpList::Cons(h, t));
            u_cset_hyp(hp, he, lv, hn, hh, tl, f0, *h);
            u_csot_hyp(hp, he, lv, hn, hh, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
        FrameList::FLet(x, v, tl) => {
            u_csot_let(hp, he, lv, x, v, tl, f0, RawExpList::Cons(h, t));
            u_cset_let(hp, he, lv, x, v, tl, f0, *h);
            u_csot_let(hp, he, lv, x, v, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
        FrameList::FLetH(x, ty, v, en, ep, tl) => {
            u_csot_leth(hp, he, lv, x, ty, v, en, ep, tl, f0, RawExpList::Cons(h, t));
            u_cset_leth(hp, he, lv, x, ty, v, en, ep, tl, f0, *h);
            u_csot_leth(hp, he, lv, x, ty, v, en, ep, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
        FrameList::FLetR(x, v, tl) => {
            u_csot_letr(hp, he, lv, x, v, tl, f0, RawExpList::Cons(h, t));
            u_cset_letr(hp, he, lv, x, v, tl, f0, *h);
            u_csot_letr(hp, he, lv, x, v, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
        FrameList::FUserCloser(tl) => {
            u_csot_ucl(hp, he, lv, tl, f0, RawExpList::Cons(h, t));
            u_cset_ucl(hp, he, lv, tl, f0, *h);
            u_csot_ucl(hp, he, lv, tl, f0, *t);
            cso_cons_split_tel(hp, he, lv, *tl, f0, h, t);      // IH (st-generic)
        }
    }
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc, forall_and]))")]
pub proof fn cso_cons_split_hoist(hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs_hoist(hp, he, lv, f, st, RawExpList::Cons(h, t))
        == (close_sem_e_hoist(hp, he, lv, f, st, *h) && close_sem_obligs_hoist(hp, he, lv, f, st, *t))
{
    u_csoh_unfold(hp, he, lv, f, RawExpList::Cons(h, t));
    u_cseh_unfold(hp, he, lv, f, *h);
    u_csoh_unfold(hp, he, lv, f, *t);
    cso_cons_split_tel(hp, he, lv, f, f, h, t);
}

#[verifier::tactus_tactic("first | tactus_auto | (intros <;> by_cases _hgate : lib.gate_wrap pp f = 1 <;> simp_all (config := { zetaDelta := true }))")]
pub proof fn cso_cons_split(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, h: Box<RawExp>, t: Box<RawExpList>)
    ensures forall|st: St| #[trigger] close_sem_obligs(pp, hp, he, lv, f, st, RawExpList::Cons(h, t))
        == (close_sem_e(pp, hp, he, lv, f, st, *h) && close_sem_obligs(pp, hp, he, lv, f, st, *t))
{
    u_cso_wrap_mode(pp, hp, he, lv, f, RawExpList::Cons(h, t));
    u_cse_wrap_mode(pp, hp, he, lv, f, *h);
    u_cso_wrap_mode(pp, hp, he, lv, f, *t);
    cso_cons_split_wrap_lead(hp, he, lv, f, h, t);
    u_cso_hoist_mode(pp, hp, he, lv, f, RawExpList::Cons(h, t));
    u_cse_hoist_mode(pp, hp, he, lv, f, *h);
    u_cso_hoist_mode(pp, hp, he, lv, f, *t);
    cso_cons_split_hoist(hp, he, lv, f, h, t);
}

// ── W5 support lemma B/C (bootstrap-63, hand-Lean `holdsAll_close_each_e`):
//    a closed obligation list holds iff every obligation holds under the
//    telescope. Works for ANY frame — incl. the Loop's havoc'd mframe/endf,
//    so the havoc is never decomposed. st stays a PARAM (the RawExpList
//    induction crosses no binder). ──
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
pub proof fn holds_all_close_each_e(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, l: RawExpList, st: St)
    ensures holds_all(hp, he, lv, close_each_e(pp, f, l), st)
        == close_sem_obligs(pp, hp, he, lv, f, st, l)
    decreases l
{
    match l {
        RawExpList::Nil => {
            u_cce_nil(pp, f);
            u_holds_all_nil(hp, he, lv);
            cso_nil_true(pp, hp, he, lv, f);
        }
        RawExpList::Cons(h, t) => {
            u_cce_cons(pp, f, h, t);
            u_holds_all_cons(hp, he, lv, Box::new(close_e(pp, f, *h)), Box::new(close_each_e(pp, f, *t)));
            holds_close_e(pp, hp, he, lv, f, *h);
            cso_cons_split(pp, hp, he, lv, f, h, t);
            holds_all_close_each_e(pp, hp, he, lv, f, *t, st);      // IH
        }
    }
}

// ═════════════════════════════════════════════════════════════════════
// bootstrap-79: the Loop arm's branch bodies, EXTRACTED from
// `wp_stm_sound` so the arm's postcondition VC stays small (inline, the
// four break-form IH facts + the full split/close sequence blew the
// whnf budget — gate-3). Each lemma takes its IH facts as `requires` —
// they are NOT in the recursive cycle (no calls to `wp_stm_sound`), so
// no termination VCs chain here. The ensures ctor matches the arm's
// match-bound fields positionally, so the arm's call sites are defeq.
// ═════════════════════════════════════════════════════════════════════
#[verifier::tactus_tactic("first | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc]) | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
pub proof fn wp_stm_sound_loop_classical(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList,
    inv_hyps: Box<BinderList>, inv_obligs: Box<RawExpList>, inv_obligs_exit: Box<RawExpList>,
    inv_obligs_break: Box<RawExpList>, binders: Box<BinderList>,
    binder_bounds: Box<ParamBoundList>, cond_name: u64, cond_ann: u64, neg_cond_ann: u64,
    neg_neg_cond_ann: u64, break_guard_ann: u64, break_use_ann: u64, d_old_name: u64, d_old_ty: u64, d_old_val: u64, d_old_eq_name: u64,
    d_old_eq_prop: u64, decrease_oblig: RawExp, setup: Box<StmData>, body: Box<StmData>, st: St)
    requires
        is_skip(*setup) == 1,
        holds_all(hp, he, lv,
            wp_stm(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), st)
            == exec_safe_f(pp, hp, he, lv, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body, st),
    ensures holds_all(hp, he, lv, wp_stm(pp, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        }), st)
        == exec_safe_f(pp, hp, he, lv, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        }, st)
{
    u_wp_loop(pp, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body);
    u_esf_loop(pp, hp, he, lv, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body);
    // the three ++ splits (init ++ (body ++ (reclose ++ decrease)))
    holds_all_append(hp, he, lv, close_each_e(pp, f, *inv_obligs),
        goals_append(wp_stm(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body),
            goals_append(close_each_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), *inv_obligs_exit),
                GoalList::Cons(Box::new(close_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig)), Box::new(GoalList::Nil)))), st);
    holds_all_append(hp, he, lv, wp_stm(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body),
        goals_append(close_each_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), *inv_obligs_exit),
            GoalList::Cons(Box::new(close_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig)), Box::new(GoalList::Nil))), st);
    holds_all_append(hp, he, lv, close_each_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), *inv_obligs_exit),
        GoalList::Cons(Box::new(close_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig)), Box::new(GoalList::Nil)), st);
    // the four goal groups (body group = the IH fact in `requires`)
    holds_all_close_each_e(pp, hp, he, lv, f, *inv_obligs, st);          // init
    holds_all_close_each_e(pp, hp, he, lv, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), *inv_obligs_exit, st);  // maintain-reclose
    u_holds_all_cons(hp, he, lv, Box::new(close_e(pp, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig)), Box::new(GoalList::Nil));
    u_holds_all_nil(hp, he, lv);
    holds_close_e(pp, hp, he, lv, frame_after(pp, loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop), *body), decrease_oblig);  // decrease
}

#[verifier::tactus_tactic("first | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc]) | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
pub proof fn wp_stm_sound_loop_bf(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList,
    inv_hyps: Box<BinderList>, inv_obligs: Box<RawExpList>, inv_obligs_exit: Box<RawExpList>,
    inv_obligs_break: Box<RawExpList>, binders: Box<BinderList>,
    binder_bounds: Box<ParamBoundList>, cond_name: u64, cond_ann: u64, neg_cond_ann: u64,
    neg_neg_cond_ann: u64, break_guard_ann: u64, break_use_ann: u64, d_old_name: u64, d_old_ty: u64, d_old_val: u64, d_old_eq_name: u64,
    d_old_eq_prop: u64, decrease_oblig: RawExp, setup: Box<StmData>, body: Box<StmData>, st: St)
    requires
        is_skip(*setup) != 1,
        holds_all(hp, he, lv,
            wp_stm(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), st)
            == exec_safe_f(pp, hp, he, lv, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup, st),
        holds_all(hp, he, lv,
            wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), st)
            == exec_safe_f(pp, hp, he, lv, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body, st),
        holds_all(hp, he, lv,
            wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup), st)
            == exec_safe_f(pp, hp, he, lv, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup, st),
    ensures holds_all(hp, he, lv, wp_stm(pp, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        }), st)
        == exec_safe_f(pp, hp, he, lv, f, StmData::Loop {
            inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann,
            neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name,
            d_old_eq_prop, decrease_oblig, setup, body,
        }, st)
{
    u_wp_loop(pp, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body);
    u_esf_loop(pp, hp, he, lv, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body);
    // the six ++ splits (init ++ setup ++ exit-reclose ++ body
    // ++ maintain-reclose ++ (decrease ++ replay))
    holds_all_append(hp, he, lv, close_each_e(pp, f, *inv_obligs),
        goals_append(
            wp_stm(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup),
            goals_append(
                close_each_e(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))), *inv_obligs_break),
                goals_append(
                    wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
                    goals_append(
                        close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
                        goals_append(
                            GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
                            wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup)))))), st);
    holds_all_append(hp, he, lv,
        wp_stm(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup),
        goals_append(
            close_each_e(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))), *inv_obligs_break),
            goals_append(
                wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
                goals_append(
                    close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
                    goals_append(
                        GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
                        wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup))))), st);
    holds_all_append(hp, he, lv,
        close_each_e(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))), *inv_obligs_break),
        goals_append(
            wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
            goals_append(
                close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
                goals_append(
                    GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
                    wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup)))), st);
    holds_all_append(hp, he, lv,
        wp_stm(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
        goals_append(
            close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
            goals_append(
                GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
                wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup))), st);
    holds_all_append(hp, he, lv,
        close_each_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), *inv_obligs_exit),
        goals_append(
            GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
            wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup)), st);
    holds_all_append(hp, he, lv,
        GoalList::Cons(Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil)),
        wp_stm(pp, loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), *setup), st);
    // the seven goal groups (the three wp_stm groups = the IH facts)
    holds_all_close_each_e(pp, hp, he, lv, f, *inv_obligs, st);          // init
    holds_all_close_each_e(pp, hp, he, lv,
        frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, break_guard_ann, Box::new(FrameList::FNil))),
        *inv_obligs_break, st);                                      // exit-reclose
    holds_all_close_each_e(pp, hp, he, lv,
        frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body),
        *inv_obligs_exit, st);                                       // maintain-reclose
    u_holds_all_cons(hp, he, lv, Box::new(close_e(pp, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig)), Box::new(GoalList::Nil));
    u_holds_all_nil(hp, he, lv);
    holds_close_e(pp, hp, he, lv, frame_after(pp, frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))), *body), decrease_oblig);  // decrease
}

// ═════════════════════════════════════════════════════════════════════
// W5 MAIN THEOREM (bootstrap-64, hand-Lean probe24 `wp_stm_sound`):
// reference-WP soundness AND faithfulness on the FULL StmData vocabulary
// — Skip/Assume/Assign/Assert/Call/Ret/DeadEnd/If/Seq/Loop — over an
// arbitrary frame telescope. TOTAL: no fragment predicate. The Loop arm
// never decomposes its havoc'd frames (mframe/endf stay opaque args to
// the frame-agnostic bridge lemmas — the W5c Opt-2 resolution).
// ═════════════════════════════════════════════════════════════════════
// Closer note: `cases s <;> omega` runs FIRST — the termination goals
// are pure height inequalities once `cases s` exposes the ctor (omega
// treats `height x` as an atom; `h_b < 1 + h_setup + h_b` needs no
// simp), and on the b79 chain VCs (3 nested IH posts) the zetaDelta
// simp_all branch burns the WHOLE budget (123s standalone vs 1.9s
// omega-only, hand-isolated on the emitted theorems). Second: the
// constructor/contradiction/assumption branch — the Loop arm's
// part-lemma precondition VCs (conjunctions of the branch guard + IH
// facts, all in ctx) and the arm's postcondition VC (the part-lemma
// posts give the goal modulo `s = Loop <projections>`, which `cases s`
// + iota recovers; the 19 off-cases die by contradiction) close in
// ~3s, where zetaDelta simp_all explodes. VCs where the height
// expression needs the simp reduction (If/Seq arms) fail both in ~2s
// and fall through to the pre-b79 branch. Historical: the explicit
// simp_all branch runs before tactus_auto because on the Loop
// termination VC tactus_auto itself burns the whole whnf budget.
#[verifier::tactus_tactic("first | (intros <;> cases s <;> omega) | (intros <;> (try constructor) <;> cases s <;> (try contradiction) <;> assumption) | (intros <;> cases s <;> simp_all (config := { zetaDelta := true }) [and_assoc] <;> omega) | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
#[verifier::structural_decreases]
#[verifier::heartbeats(1600000)]
pub proof fn wp_stm_sound(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, s: StmData, st: St)
    ensures holds_all(hp, he, lv, wp_stm(pp, f, s), st) == exec_safe_f(pp, hp, he, lv, f, s, st)
    decreases s
{
    match s {
        StmData::Assert(o, hn, h) => {
            u_wp_assert(pp, f, o, hn, h);
            u_holds_all_cons(hp, he, lv, Box::new(close_e(pp, f, o)), Box::new(GoalList::Nil));
            u_holds_all_nil(hp, he, lv);
            holds_close_e(pp, hp, he, lv, f, o);
            u_esf_assert(pp, hp, he, lv, f, o, hn, h);
        }
        StmData::Assume(hn, e) => {
            u_wp_assume(pp, f, hn, e);
            u_holds_all_nil(hp, he, lv);
            u_esf_assume(pp, hp, he, lv, f, hn, e);
        }
        StmData::Assign(x, rhs) => {
            u_wp_assign(pp, f, x, rhs);
            u_holds_all_nil(hp, he, lv);
            u_esf_assign(pp, hp, he, lv, f, x, rhs);
        }
        StmData::AssignH(x, ty, v, en, ep) => {
            u_wp_assignh(pp, f, x, ty, v, en, ep);
            u_holds_all_nil(hp, he, lv);
            u_esf_assignh(pp, hp, he, lv, f, x, ty, v, en, ep);
        }
        StmData::AssignR(x, v) => {
            u_wp_assignr(pp, f, x, v);
            u_holds_all_nil(hp, he, lv);
            u_esf_assignr(pp, hp, he, lv, f, x, v);
        }
        StmData::Call { reqs, post } => {
            u_wp_call(pp, f, reqs, post);
            holds_all_close_each_e(pp, hp, he, lv, f, *reqs, st);
            u_esf_call(pp, hp, he, lv, f, reqs, post);
        }
        StmData::DeadEnd(b) => {
            u_wp_deadend(pp, f, b);
            u_esf_deadend(pp, hp, he, lv, f, b);
            wp_stm_sound(pp, hp, he, lv, f, *b, st);                // IH
        }
        StmData::AssertQueryNl(b, tq) => {
            u_wp_aqnl(pp, f, b, tq);
            u_esf_aqnl(pp, hp, he, lv, f, b, tq);
            wp_stm_sound(pp, hp, he, lv, strip_hyps(f), *b, st);    // IH at the stripped frame
            // The appended degenerate-True goal closes under the
            // post-body frame (the query's own accumulated hyps).
            holds_all_append(hp, he, lv,
                wp_stm(pp, strip_hyps(f), *b),
                GoalList::Cons(
                    Box::new(close_e(pp, frame_after(pp, strip_hyps(f), *b), tq)),
                    Box::new(GoalList::Nil)),
                st);
            u_holds_all_cons(hp, he, lv,
                Box::new(close_e(pp, frame_after(pp, strip_hyps(f), *b), tq)),
                Box::new(GoalList::Nil));
            u_holds_all_nil(hp, he, lv);
            holds_close_e(pp, hp, he, lv, frame_after(pp, strip_hyps(f), *b), tq);
        }
        StmData::AssertQueryTactus(o, hn, h) => {
            u_wp_aqt(pp, f, o, hn, h);
            u_holds_all_cons(hp, he, lv,
                Box::new(close_e(pp, frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), o)),
                Box::new(GoalList::Nil));
            u_holds_all_nil(hp, he, lv);
            holds_close_e(pp, hp, he, lv,
                frame_append(f, FrameList::FUserCloser(Box::new(FrameList::FNil))), o);
            u_esf_aqt(pp, hp, he, lv, f, o, hn, h);
        }
        StmData::Ret(es, rb) => {
            u_wp_ret(pp, f, es, rb);
            holds_all_close_each_e(pp, hp, he, lv, ret_frame(pp, f, rb), *es, st);
            u_esf_ret(pp, hp, he, lv, f, es, rb);
        }
        StmData::If(c, cn, nc, ncn, t, e) => {
            u_wp_if(pp, f, c, cn, nc, ncn, t, e);
            u_esf_if(pp, hp, he, lv, f, c, cn, nc, ncn, t, e);
            holds_all_append(hp, he, lv,
                wp_stm(pp, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t),
                wp_stm(pp, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e), st);
            wp_stm_sound(pp, hp, he, lv, frame_append(f, FrameList::FHyp(cn, c, Box::new(FrameList::FNil))), *t, st);   // IH
            wp_stm_sound(pp, hp, he, lv, frame_append(f, FrameList::FHyp(ncn, nc, Box::new(FrameList::FNil))), *e, st);  // IH
        }
        StmData::IfCtor { pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els } => {
            u_wp_ifctor(pp, f, pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els);
            u_esf_ifctor(pp, hp, he, lv, f, pos_binders, eq_name, eq_prop, neg_name, neg_prop, thn, els);
            holds_all_append(hp, he, lv,
                wp_stm(pp, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn),
                wp_stm(pp, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els), st);
            wp_stm_sound(pp, hp, he, lv, frame_append(f, ctor_pos_frame(*pos_binders, eq_name, eq_prop)), *thn, st);   // IH
            wp_stm_sound(pp, hp, he, lv, frame_append(f, FrameList::FHyp(neg_name, neg_prop, Box::new(FrameList::FNil))), *els, st);  // IH
        }
        StmData::Loop { inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body } => {
            // NO `let mframe/endf` bindings and the IHs come FIRST: Rust lets
            // ride into every subsequent VC (incl. the height-decrease
            // termination VC) and zetaDelta then forces simp to normalize
            // `loop_maintain_frame`/`frame_after` on symbolic args — a whnf
            // heartbeat explosion. Inlined, the termination goal is just the
            // height inequality. bootstrap-79: the IHs also sit OUTSIDE the
            // branch split (inside, the termination VC picks up the
            // `is_skip` guard in its path condition and `cases s` +
            // simp_all whnf-explodes on it). Each recursive call is on a
            // subterm either way, so the other branch's IH facts are
            // simply unused. (`assert … by` pairing does NOT work in the
            // Tactus backend: lemma-call posts are DROPPED from assert-by
            // blocks — the assert's VC sees only `True` — so the closer
            // had to re-prove the IH equalities from scratch. gate-4.)
            wp_stm_sound(pp, hp, he, lv,
                loop_maintain_frame(f, *inv_hyps, *binders, *binder_bounds, cond_name, cond_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop),
                *body, st);                                                  // IH (classical body)
            wp_stm_sound(pp, hp, he, lv,
                frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)),
                *setup, st);                                                 // IH (break-form setup, body run)
            wp_stm_sound(pp, hp, he, lv,
                frame_append(frame_after(pp, frame_append(loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds), d_old_frame(d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop)), *setup), FrameList::FHyp(cond_name, neg_neg_cond_ann, Box::new(FrameList::FNil))),
                *body, st);                                                  // IH (break-form body)
            wp_stm_sound(pp, hp, he, lv,
                loop_telescope_base(f, *inv_hyps, *binders, *binder_bounds),
                *setup, st);                                                 // IH (break-form setup, exit replay)
            if is_skip(*setup) == 1 {
                wp_stm_sound_loop_classical(pp, hp, he, lv, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body, st);
            } else {
                wp_stm_sound_loop_bf(pp, hp, he, lv, f, inv_hyps, inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds, cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop, decrease_oblig, setup, body, st);
            }
        }
        StmData::Skip => {
            u_wp_skip(pp, f);
            u_holds_all_nil(hp, he, lv);
            u_esf_skip(pp, hp, he, lv, f);
        }
        StmData::Seq(a, b) => {
            u_wp_seq(pp, f, a, b);
            u_esf_seq(pp, hp, he, lv, f, a, b);
            holds_all_append(hp, he, lv, wp_stm(pp, f, *a), wp_stm(pp, frame_after(pp, f, *a), *b), st);
            wp_stm_sound(pp, hp, he, lv, f, *a, st);                             // IH
            wp_stm_sound(pp, hp, he, lv, frame_after(pp, f, *a), *b, st);            // IH (shifted frame)
        }
    }
}

// ref_wp unfold + top-level soundness through the genuine seed_frame.
pub proof fn u_ref_wp(c: FnCtxData, s: StmData)
    ensures ref_wp(c, s) == wp_stm(poisoned_props(c), seed_frame(c), s)
{}

/// THE LOOP-CLOSURE THEOREM (hand-Lean `ref_wp_sound`): the emitted
/// certificate goals all hold at a state iff the statement is
/// operationally safe under the per-fn seed frame — for EVERY oracle
/// triple consistent with the leaf typing (valuation-parametric).
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])")]
pub proof fn ref_wp_sound(hp: HpOracle, he: HeOracle, lv: LvOracle, c: FnCtxData, s: StmData, st: St)
    ensures holds_all(hp, he, lv, ref_wp(c, s), st) == exec_safe_f(poisoned_props(c), hp, he, lv, seed_frame(c), s, st)
{
    u_ref_wp(c, s);
    wp_stm_sound(poisoned_props(c), hp, he, lv, seed_frame(c), s, st);
}

// ── W5 frame-algebra one-step unfolds (bootstrap-65): the frame_after /
//    frame_append arms the prophecy/closure corollaries reduce through.
//    Data-only, probe32 empty shape. ──

pub proof fn u_fa_assume(pp: LeafList, f: FrameList, e: u64)
    ensures frame_after(pp, f, StmData::Assume(0, e))
        == frame_append(f, FrameList::FHyp(0, e, Box::new(FrameList::FNil)))
{}
pub proof fn u_fa_deadend(pp: LeafList, f: FrameList, b: Box<StmData>)
    ensures frame_after(pp, f, StmData::DeadEnd(b)) == f
{}
pub proof fn u_fa_seq(pp: LeafList, f: FrameList, a: Box<StmData>, b: Box<StmData>)
    ensures frame_after(pp, f, StmData::Seq(a, b)) == frame_after(pp, frame_after(pp, f, *a), *b)
{}
pub proof fn u_fapp_fnil(g: FrameList)
    ensures frame_append(FrameList::FNil, g) == g
{}
pub proof fn u_fapp_fbind(x: u64, ty: u64, t: Box<FrameList>, g: FrameList)
    ensures frame_append(FrameList::FBind(x, ty, t), g)
        == FrameList::FBind(x, ty, Box::new(frame_append(*t, g)))
{}
pub proof fn u_fapp_fhyp(n: u64, h: u64, t: Box<FrameList>, g: FrameList)
    ensures frame_append(FrameList::FHyp(n, h, t), g)
        == FrameList::FHyp(n, h, Box::new(frame_append(*t, g)))
{}

// ═════════════════════════════════════════════════════════════════════
// W5 MODEL-LEVEL COROLLARIES (bootstrap-65, hand-Lean probe25/probe26).
// Neither prophecy nor closures add a StmData arm — both Verus encodings
// use existing constructors — so these are corollaries of wp_stm_sound +
// the frame algebra, each paired with a DISCRIMINATOR theorem (the two
// reduced forms differing is what proves the placement/isolation is
// real, not vacuous).
// ═════════════════════════════════════════════════════════════════════

/// W5d MAIN (probe25 `prophecy_sound`) — STRUCTURAL post-N1
/// (bootstrap-74): the reference WP for `resolve; assert P(*x)` under
/// the borrow frame `∀ x_fut` reduces to ONE goal with the resolve pin
/// sitting INSIDE the binder telescope, as the hoisted hyp binder
/// production emits. Structural equality is stronger than the old
/// holds-reading (decidable, and the pin's placement is visible in the
/// goal itself); the semantic reading follows via holds_close_e. (In
/// hoist mode the abstract holds-semantics reads hyp binders as ∀ —
/// the dependent-product meaning lives in the adequacy layer, exactly
/// as for the reqs binders.) (`lib.gate_wrap` in the simp set: the
/// derived gate needs delta-unfolding to consume the
/// `leaf_mem pp resolve = 0` side condition — F4.)
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc, lib.gate_wrap])")]
pub proof fn prophecy_sound(pp: LeafList, xfut: u64, ty: u64, resolve: u64, h: u64, obl: RawExp)
    // F4: the hoist-mode reading requires the resolve hyp UNPOISONED —
    // derived now (a membership check on the poison set), not a bit.
    requires leaf_mem(pp, resolve) == 0,
    ensures wp_stm(pp, FrameList::FBind(xfut, ty, Box::new(FrameList::FNil)),
            StmData::Seq(
                Box::new(StmData::Assume(0, resolve)),
                Box::new(StmData::Assert(obl, 0, h))))
        == GoalList::Cons(
            Box::new(GoalData::All(xfut, ty,
                Box::new(GoalData::All(0, resolve,
                    Box::new(GoalData::LeafE(render_exp(obl))))))),
            Box::new(GoalList::Nil))
{
    let f = FrameList::FBind(xfut, ty, Box::new(FrameList::FNil));
    let fh = FrameList::FBind(xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))));
    u_wp_seq(pp, f, Box::new(StmData::Assume(0, resolve)), Box::new(StmData::Assert(obl, 0, h)));
    u_wp_assume(pp, f, 0, resolve);
    u_fa_assume(pp, f, resolve);
    u_fapp_fbind(xfut, ty, Box::new(FrameList::FNil), FrameList::FHyp(0, resolve, Box::new(FrameList::FNil)));
    u_fapp_fnil(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil)));
    u_wp_assert(pp, fh, obl, 0, h);
    u_gapp_nil(wp_stm(pp, fh, StmData::Assert(obl, 0, h)));
    u_gate_bind(xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))));
    u_gate_hyp(0, resolve, Box::new(FrameList::FNil));
    u_gate_nil();
    u_gatep_bind(pp, xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))));
    u_gatep_hyp(pp, 0, resolve, Box::new(FrameList::FNil));
    u_gatep_nil(pp, );
    u_gateu_bind(xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))));
    u_gateu_hyp(0, resolve, Box::new(FrameList::FNil));
    u_gateu_nil();
    u_ce_hoist_mode(pp, fh, obl);
    u_ceh_unfold(fh, obl);
    u_cer_bind(xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))), GoalData::LeafE(render_exp(obl)));
    u_cer_hyp(0, resolve, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cer_nil(GoalData::LeafE(render_exp(obl)));
    u_cet_bind(xfut, ty, Box::new(FrameList::FHyp(0, resolve, Box::new(FrameList::FNil))), GoalData::LeafE(render_exp(obl)));
    u_cet_hyp(0, resolve, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cet_nil(GoalData::LeafE(render_exp(obl)));
}

/// W5d DISCRIMINATOR (probe25 `prophecy_swapped_sound`) — STRUCTURAL:
/// the swapped `assert P(*x); resolve` reduces to the goal WITHOUT the
/// resolve binder — the pin never reaches an upstream obligation. The
/// two reduced shapes DIFFERING (All(0, resolve, ·) present vs absent)
/// is the proof that `frame_after` places the pin temporally correctly.
pub proof fn prophecy_swapped_sound(pp: LeafList, xfut: u64, ty: u64, resolve: u64, h: u64, obl: RawExp)
    ensures wp_stm(pp, FrameList::FBind(xfut, ty, Box::new(FrameList::FNil)),
            StmData::Seq(
                Box::new(StmData::Assert(obl, 0, h)),
                Box::new(StmData::Assume(0, resolve))))
        == GoalList::Cons(
            Box::new(GoalData::All(xfut, ty,
                Box::new(GoalData::LeafE(render_exp(obl))))),
            Box::new(GoalList::Nil))
{
    let f = FrameList::FBind(xfut, ty, Box::new(FrameList::FNil));
    u_wp_seq(pp, f, Box::new(StmData::Assert(obl, 0, h)), Box::new(StmData::Assume(0, resolve)));
    u_wp_assert(pp, f, obl, 0, h);
    u_wp_assume(pp, frame_after(pp, f, StmData::Assert(obl, 0, h)), 0, resolve);
    u_gapp_cons(Box::new(close_e(pp, f, obl)), Box::new(GoalList::Nil), GoalList::Nil);
    u_gapp_nil(GoalList::Nil);
    u_gate_bind(xfut, ty, Box::new(FrameList::FNil));
    u_gate_nil();
    u_gatep_bind(pp, xfut, ty, Box::new(FrameList::FNil));
    u_gatep_nil(pp, );
    u_ce_hoist_mode(pp, f, obl);
    u_ceh_unfold(f, obl);
    u_cer_bind(xfut, ty, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cer_nil(GoalData::LeafE(render_exp(obl)));
    u_cet_bind(xfut, ty, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cet_nil(GoalData::LeafE(render_exp(obl)));
}

/// W5e MAIN (probe26 `closure_creation_sound`): the reference WP for a
/// closure creation — `Seq (DeadEnd body) (Assume external_spec)`, the
/// actual Verus lowering — reduces EXACTLY to the body obligation under
/// the ENCLOSING frame: wrapper and Assume add nothing.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])")]
pub proof fn closure_creation_sound(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, f: FrameList, body: Box<StmData>, ext: u64, st: St)
    ensures holds_all(hp, he, lv,
            wp_stm(pp, f, StmData::Seq(
                Box::new(StmData::DeadEnd(body)),
                Box::new(StmData::Assume(0, ext)))), st)
        == exec_safe_f(pp, hp, he, lv, f, *body, st)
{
    wp_stm_sound(pp, hp, he, lv, f,
        StmData::Seq(Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext))), st);
    u_esf_seq(pp, hp, he, lv, f, Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext)));
    u_esf_deadend(pp, hp, he, lv, f, body);
    u_fa_deadend(pp, f, body);
    u_esf_assume(pp, hp, he, lv, frame_after(pp, f, StmData::DeadEnd(body)), 0, ext);
}

/// W5e ISOLATION (probe26 `closure_deadend_isolates`) — STRUCTURAL
/// post-N1: the closure body's local assumption does NOT leak — the
/// assert's goal carries NO binder for q.
pub proof fn closure_deadend_isolates(pp: LeafList, q: u64, h: u64, obl: RawExp)
    ensures wp_stm(pp, FrameList::FNil, StmData::Seq(
                Box::new(StmData::DeadEnd(Box::new(StmData::Assume(0, q)))),
                Box::new(StmData::Assert(obl, 0, h))))
        == GoalList::Cons(Box::new(GoalData::LeafE(render_exp(obl))), Box::new(GoalList::Nil))
{
    u_wp_seq(pp, FrameList::FNil,
        Box::new(StmData::DeadEnd(Box::new(StmData::Assume(0, q)))),
        Box::new(StmData::Assert(obl, 0, h)));
    u_wp_deadend(pp, FrameList::FNil, Box::new(StmData::Assume(0, q)));
    u_wp_assume(pp, FrameList::FNil, 0, q);
    u_fa_deadend(pp, FrameList::FNil, Box::new(StmData::Assume(0, q)));
    u_wp_assert(pp, FrameList::FNil, obl, 0, h);
    u_gapp_nil(wp_stm(pp, FrameList::FNil, StmData::Assert(obl, 0, h)));
    u_gate_nil();
    u_gatep_nil(pp, );
    u_ce_hoist_mode(pp, FrameList::FNil, obl);
    u_ceh_unfold(FrameList::FNil, obl);
    u_cer_nil(GoalData::LeafE(render_exp(obl)));
    u_cet_nil(GoalData::LeafE(render_exp(obl)));
}

/// W5e DISCRIMINATOR (probe26 `seq_assume_gates`) — STRUCTURAL: the
/// BARE `Seq (Assume q) (Assert P)` (no DeadEnd) DOES bind q over the
/// assert — the hoisted hyp binder All(0, q, ·) present here and absent
/// above is the proof the DeadEnd quarantines. (`lib.gate_wrap` in the
/// simp set: consume the `leaf_mem pp q = 0` side condition — F4.)
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc, lib.gate_wrap])")]
pub proof fn seq_assume_gates(pp: LeafList, q: u64, h: u64, obl: RawExp)
    // F4: hoist mode requires the assumed hyp unpoisoned (derived).
    requires leaf_mem(pp, q) == 0,
    ensures wp_stm(pp, FrameList::FNil, StmData::Seq(
                Box::new(StmData::Assume(0, q)),
                Box::new(StmData::Assert(obl, 0, h))))
        == GoalList::Cons(
            Box::new(GoalData::All(0, q, Box::new(GoalData::LeafE(render_exp(obl))))),
            Box::new(GoalList::Nil))
{
    let fh = FrameList::FHyp(0, q, Box::new(FrameList::FNil));
    u_wp_seq(pp, FrameList::FNil, Box::new(StmData::Assume(0, q)), Box::new(StmData::Assert(obl, 0, h)));
    u_wp_assume(pp, FrameList::FNil, 0, q);
    u_fa_assume(pp, FrameList::FNil, q);
    u_fapp_fnil(fh);
    u_wp_assert(pp, fh, obl, 0, h);
    u_gapp_nil(wp_stm(pp, fh, StmData::Assert(obl, 0, h)));
    u_gate_hyp(0, q, Box::new(FrameList::FNil));
    u_gate_nil();
    u_gatep_hyp(pp, 0, q, Box::new(FrameList::FNil));
    u_gatep_nil(pp, );
    u_gateu_hyp(0, q, Box::new(FrameList::FNil));
    u_gateu_nil();
    u_ce_hoist_mode(pp, fh, obl);
    u_ceh_unfold(fh, obl);
    u_cer_hyp(0, q, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cer_nil(GoalData::LeafE(render_exp(obl)));
    u_cet_hyp(0, q, Box::new(FrameList::FNil), GoalData::LeafE(render_exp(obl)));
    u_cet_nil(GoalData::LeafE(render_exp(obl)));
}

/// W5e CONTRACT FORWARDING (probe26 `closure_forwards_contract`): after
/// the closure, the continuation DOES see the external spec — the Assume
/// threads the contract forward (the analog of the W5d resolve pin).
/// Post-N1 the assert's goal closes over the hoisted ext binder, so the
/// abstract reading is the ∀-form (the ext-gating meaning lives in the
/// goal structure — All(0, ext, ·) — and the adequacy layer).
/// (`lib.gate_wrap` in the simp set: the mode pin's `gate_wrap fh ≠ 1`
/// side condition is a COMPOSITE term — by_cases dispatchers get it
/// for free, but this corollary applies the pin straight-line, so the
/// closer must delta-unfold the gate to the u_gate*/u_gatep* facts.)
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc, lib.gate_wrap])")]
pub proof fn closure_forwards_contract(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, body: Box<StmData>, ext: u64, h: u64, obl: RawExp, st: St)
    // F4: hoist mode requires the threaded hyp unpoisoned (derived).
    requires leaf_mem(pp, ext) == 0,
    ensures holds_all(hp, he, lv,
            wp_stm(pp, FrameList::FNil, StmData::Seq(
                Box::new(StmData::Seq(
                    Box::new(StmData::DeadEnd(body)),
                    Box::new(StmData::Assume(0, ext)))),
                Box::new(StmData::Assert(obl, 0, h)))), st)
        == (exec_safe_f(pp, hp, he, lv, FrameList::FNil, *body, st)
            && (forall|v: int| #[trigger] he(render_exp(obl), upd(st, 0, v))))
{
    wp_stm_sound(pp, hp, he, lv, FrameList::FNil, StmData::Seq(
        Box::new(StmData::Seq(Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext)))),
        Box::new(StmData::Assert(obl, 0, h))), st);
    u_esf_seq(pp, hp, he, lv, FrameList::FNil,
        Box::new(StmData::Seq(Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext)))),
        Box::new(StmData::Assert(obl, 0, h)));
    u_esf_seq(pp, hp, he, lv, FrameList::FNil, Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext)));
    u_esf_deadend(pp, hp, he, lv, FrameList::FNil, body);
    u_fa_deadend(pp, FrameList::FNil, body);
    u_esf_assume(pp, hp, he, lv, frame_after(pp, FrameList::FNil, StmData::DeadEnd(body)), 0, ext);
    u_fa_seq(pp, FrameList::FNil, Box::new(StmData::DeadEnd(body)), Box::new(StmData::Assume(0, ext)));
    u_fa_assume(pp, frame_after(pp, FrameList::FNil, StmData::DeadEnd(body)), ext);
    u_fapp_fnil(FrameList::FHyp(0, ext, Box::new(FrameList::FNil)));
    u_esf_assert(pp, hp, he, lv, FrameList::FHyp(0, ext, Box::new(FrameList::FNil)), obl, 0, h);
    u_gate_hyp(0, ext, Box::new(FrameList::FNil));
    u_gate_nil();
    u_gatep_hyp(pp, 0, ext, Box::new(FrameList::FNil));
    u_gatep_nil(pp, );
    u_gateu_hyp(0, ext, Box::new(FrameList::FNil));
    u_gateu_nil();
    u_cse_hoist_mode(pp, hp, he, lv, FrameList::FHyp(0, ext, Box::new(FrameList::FNil)), obl);
    u_cseh_unfold(hp, he, lv, FrameList::FHyp(0, ext, Box::new(FrameList::FNil)), obl);
    u_cset_hyp(hp, he, lv, 0, ext, Box::new(FrameList::FNil), FrameList::FHyp(0, ext, Box::new(FrameList::FNil)), obl);
    u_cset_nil(hp, he, lv, FrameList::FHyp(0, ext, Box::new(FrameList::FNil)), obl);
    u_cser_hyp(hp, he, lv, 0, ext, Box::new(FrameList::FNil), obl);
    u_cser_nil(hp, he, lv, obl);
}

// ── Non-vacuity: the theorem BITES (the leaf arms demand the ACTUAL
//    obligations, never `true`). ──

// (1) Assert under the empty frame: the emitted goal forces the deep
//     obligation at the very state.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc])")]
pub proof fn wp_sound_bites_assert(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle, o: RawExp, h: u64, st: St)
    requires holds_all(hp, he, lv, wp_stm(pp, FrameList::FNil, StmData::Assert(o, 0, h)), st)
    ensures he(render_exp(o), st)
{
    wp_stm_sound(pp, hp, he, lv, FrameList::FNil, StmData::Assert(o, 0, h), st);
    u_esf_assert(pp, hp, he, lv, FrameList::FNil, o, 0, h);
    u_cse_nil(pp, hp, he, lv, o);
}

// (2) Loop INIT (probe24 witness 1): the invariant obligation must hold
//     on ENTRY at the pre-loop state — deliverable only from the emitted
//     init goal (he is opaque). The closer carries `lib.is_skip` in the
//     simp set (bootstrap-79): the b79 branch-gate `if is_skip(*setup)
//     == 1` in u_esf_loop's post is a CLOSED ite here (setup = Skip) —
//     the equation lemmas reduce it where the default set stalls.
#[verifier::tactus_tactic("first | tactus_auto | (intros <;> simp_all (config := { zetaDelta := true }) [and_assoc, lib.is_skip])")]
pub proof fn wp_sound_bites_loop_init(pp: LeafList, hp: HpOracle, he: HeOracle, lv: LvOracle,
    inv_hyps: Box<BinderList>, ob: Box<RawExp>, binders: Box<BinderList>,
    binder_bounds: Box<ParamBoundList>, cond_name: u64, cond_ann: u64, neg_cond_ann: u64, d_old_name: u64, d_old_ty: u64, d_old_val: u64, d_old_eq_name: u64,
    d_old_eq_prop: u64, decrease_oblig: RawExp, body: Box<StmData>, st: St)
    requires holds_all(hp, he, lv, wp_stm(pp, FrameList::FNil, StmData::Loop {
            inv_hyps,
            inv_obligs: Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
            inv_obligs_exit: Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
            inv_obligs_break: Box::new(RawExpList::Nil),
            binders, binder_bounds, cond_name, cond_ann, neg_cond_ann,
            neg_neg_cond_ann: 999999,
            break_guard_ann: 999999,
            break_use_ann: 999999, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop,
            decrease_oblig, setup: Box::new(StmData::Skip), body,
        }), st)
    ensures he(render_exp(*ob), st)
{
    wp_stm_sound(pp, hp, he, lv, FrameList::FNil, StmData::Loop {
        inv_hyps,
        inv_obligs: Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
        inv_obligs_exit: Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
        inv_obligs_break: Box::new(RawExpList::Nil),
        binders, binder_bounds, cond_name, cond_ann, neg_cond_ann,
        neg_neg_cond_ann: 999999,
        break_guard_ann: 999999,
        break_use_ann: 999999, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop,
        decrease_oblig, setup: Box::new(StmData::Skip), body,
    }, st);
    u_esf_loop(pp, hp, he, lv, FrameList::FNil, inv_hyps,
        Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
        Box::new(RawExpList::Cons(ob, Box::new(RawExpList::Nil))),
        Box::new(RawExpList::Nil),
        binders, binder_bounds, cond_name, cond_ann, neg_cond_ann,
        999999, 999999, 999999, d_old_name, d_old_ty, d_old_val, d_old_eq_name, d_old_eq_prop,
        decrease_oblig, Box::new(StmData::Skip), body);
    u_cso_nil(pp, hp, he, lv, RawExpList::Cons(ob, Box::new(RawExpList::Nil)));
    u_obligs_cons(he, ob, Box::new(RawExpList::Nil));
}

} // verus!
