//! SST → certificate serializer (bootstrap N3a — THE new trusted component).
//!
//! # Role
//!
//! This module is the one piece of the R2 certificate architecture a
//! skeptic must read. Everything else the bootstrap adds is *checked*
//! (by Lean's kernel, at bridge time); this is trusted. Its design goals
//! are therefore inverted from normal code: boring beats clever, 1:1
//! beats abstracted, explicit beats inferred, small enough to audit in
//! one sitting. Spec: `DESIGN-N3-serializer.md`.
//!
//! Per verified exec/WP-proof fn, [`emit_cert`] writes a certificate file
//! `<TACTUS_LEAN_OUT>/<crate>/cert/<fn>.cert.lean` containing the fn's
//! post-transform SST body, printed as a Lean term of the `tactus-core`
//! mirror vocabulary (`lib.StmData` / `lib.LeafList` / …), plus the
//! `FnCtxData` seed refWp (W2) will recompute obligations from, plus (N3b)
//! the production `GoalList` refWp's result is compared against. The
//! `refWp … = production` bridge line joins in W2.
//!
//! # Goal half (N3b) — the one production-emitter touch
//!
//! The production goals are captured as *structured* [`GoalShape`] spines
//! by the Wp walker at its single `wrap` site (before the frames fold
//! into the flat statement), NOT by marking nodes on the shared
//! `lean_ast::Expr` type. This is the provenance of DESIGN-N3 §5 realized
//! without touching the pretty-printer or `Expr`'s ~50 match arms — the
//! frame list IS the walker's construction record. `goal_serialize`
//! ([`Serializer::goal_data`]/[`Serializer::goal_list`]) turns each spine
//! into a `lib.GoalData`, interning every spine leaf into the SAME leaf
//! table as the SST half so matching leaves cancel across the W2 bridge.
//! Non-circular exactly as §5 requires: refWp recomputes structure from
//! the SST literal independently, and the `decide` equality validates the
//! claim — a mismark fails the bridge, never silent-passes.
//!
//! One qualification to that claim (endgame policy P1,
//! `DESIGN-bootstrap-endgame.md` §1) — RETIRED at bootstrap-80 stage 2
//! (F4): the N1 wrap-gate POISON MARK was a semantic predicate computed
//! here ([`Serializer::hyp_poison`]), mirroring `hoist_all`'s
//! `lexpr_mentions_var` bail check — a common-mode channel carried as
//! trusted until deep leaves let refWp derive the mark reference-side.
//! That derivation is now the ONLY channel: the cert carries
//! `FnCtxData.residue_names` + the `prop_deeps` side table (dumb
//! faithful `raw_exp` transcriptions of exactly the props
//! [`Serializer::hyp_poison`] checks), and refWp derives the poison set
//! (`poisoned_props`) — the bit slots are DELETED from the vocabulary.
//! `hyp_poison` / `lexpr_mentions_var` no longer reach the cert; they
//! remain ONLY as (a) the forced-state mirror feeding `mark_flet_forced`
//! / `mark_poison_forced` (production's branch-join classification state)
//! and (b) emission-time guards: a residue mention on a prop with no
//! transcriber (`Call.post` LExpr-side props) or an uncoverable
//! transcription rejects loud (`prop-deep-uncoverable`), and an
//! uncoverable bit-0 prop registers the opaque-atom fallback deep (guaranteed
//! mention-free by the same check; the bridge backstops even a buggy
//! check — a wrong 0 hoists where production wrapped). The channel is
//! pinned live by the probe13 `poison_residue_drop` / `poison_deep_drop`
//! mutation kills (the derivation INPUTS are perturbed; each must flip
//! the bridge 1→0).
//!
//! SECOND named trusted predicate (bootstrap-77): the N2 IsVariant
//! DETECTOR. `ctor_fork_frames` decides whether a fork's positive
//! branch gets ctor frames using production's own
//! `branch_isvariant_of` (shared single-source) — a detector bug is
//! therefore COMMON-MODE: both sides would upgrade (or not) in the
//! same wrong places and the bridge would close on the wrong shape.
//! The krate-data gates (dt-in-map, multi-variant, typ-args exposed,
//! wrapper-deref count) and the FRAME ASSEMBLY are recomputed here
//! independently; only the peel-to-IsVariant decision is shared.
//! Like the poison mark, this is carried as trusted until the
//! reference side can express the check (a mirror datatype
//! environment — W7-adjacent, the next trust-shrink target after
//! milestone B); the assembled frames are pinned live meanwhile by the
//! probe13 `ifctor_eq_drop` / `ifctor_binder_drop` / `ifctor_neg_drop`
//! / `ifctor_arm_swap` mutation kills — one per assembly output channel
//! (ctor-equation hyp, field-binder telescope, else-branch hyp, arm
//! attachment), each must flip the bridge 1→0. The peel DECISION remains
//! uncovered. The IfCtor poison bits are GONE with F4 (their props ride
//! the same `prop_deeps` table, registered mention-equivalent via the
//! scrutinee).
//!
//! # Snapshot point (faithfulness anchor #1)
//!
//! [`emit_cert`] is called at the inputs of
//! `sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check,
//! broadcast_lemmas)` — the single source of obligation shape both the
//! island and package paths feed. The serializer transcribes
//! `check.body: Stm` after ONE shared pre-pass —
//! `loop_normalize::normalize_setup_loops`, the same function
//! production applies, identity unless a setup-carrying `while` is
//! present — so refWp sees the single loop encoding production walks
//! rather than having to model the normalization itself (2026-07-26).
//! The mut-ref rewrite and `WpCtx` construction happen *inside*
//! `exec_fn_theorems_to_ast`, downstream of this snapshot, so they are
//! deliberately not the serializer's input — refWp recomputes whatever
//! the walker does from the literal, and the `decide` equality (W2) is
//! what validates the recomputation.
//!
//! # Faithfulness contract (anchor #2) — audit this list, not the code
//!
//! Every field the serializer reads from `FunctionSst` / `FuncCheckSst`,
//! and every field it deliberately does not, with one line of why.
//!
//! ## Read (captured into the literal)
//!
//! * `fn_sst.x.typ_params` — type-param telescope → `FnCtxData.typ_params`
//!   (`BinderList`; kind leaf = rendered `Type`). Polymorphic opens
//!   (`∀ (A : Type)`). Instance/`[Nonempty A]` bounds from `typ_bounds`
//!   are NOT yet distinguished (see "Deferred"; census will quantify the
//!   tgt impact).
//! * `fn_sst.x.pars` (non-`%`-synthetic) — value-param telescope →
//!   `FnCtxData.params` (binder-id + typ leaf via `param_binder_typ`).
//! * per-param `type_bound_predicate` → `FnCtxData.param_bounds`
//!   (`Bound(name, prop)` for an int-typed param — `name` = the
//!   `h_<param>_bound` name leaf, `prop` = the range-predicate leaf — else
//!   `NoBound`; finding-2: production renders these as NAMED ∀-binders).
//! * `check.reqs` — requires exps → `FnCtxData.reqs` `BinderList` of
//!   `(h_req<i> name leaf, req-prop leaf)` (finding-2: NAMED ∀-binders).
//! * mut-ref pars + `BorrowMut` local_decls → `FnCtxData.mut_params`
//!   `MutParamList` of `(param name, <p>_at_pre_tactus name, <p>.deref
//!   value leaf)` in production's declaration order (bootstrap-78 S2).
//!   refWp derives the two typ-less fn-entry FLets per entry
//!   (`mut_preamble_frame`) — plainness trips the wrap gate exactly as
//!   production's `hoist_all` bails on the typ-less preamble lets, so
//!   every goal of a mut-param fn renders wrap-mode (and the walk's
//!   shadow-freshening is off, `mark_flet_forced`).
//! * `check.post_condition.ens_exps` — ensures exps read TWICE: bare via
//!   `exp_leaf` → `FnCtxData.enss` (refWp does not read this slot), and
//!   ANNOTATED via `oblig_leaf` → the `StmData::Ret` obligation leaves (the
//!   `Return` goal, span_mark'd like production's `WpCtx` postcondition —
//!   finding-1's Ret-annotation).
//! * `check.post_condition.dest` — the declared `-> (r: T)` return-var name
//!   → the `RetBind::RetLet` name leaf (`sanitize`d to match production's
//!   `let_bind_synthetic(sanitize(ret), …)`; finding-4). `None` (unit
//!   return) ⇒ `RetNone`.
//! * `StmX::Return { ret_exp }` — the returned expression → the
//!   `RetBind::RetLet` value leaf (`exp_leaf`), paired with `dest` above to
//!   reproduce production's `let <ret> := <e>` frame binding.
//! * `check.body` — the `Stm` tree, LOOP-NORMALIZED first
//!   (`loop_normalize::normalize_setup_loops` — the same pre-pass
//!   production applies before its walk; identity unless a
//!   setup-carrying `while` is present, so this is byte-neutral on
//!   bodies without one) → `StmData` (the stage-A subset:
//!   Assert, Assume, Assign, DeadEnd, Return, If, Loop, Block→Seq/Skip).
//!   `Assert` carries TWO leaves (finding-1): the ANNOTATED obligation
//!   leaf (`oblig_leaf` — production's `span_mark` render, the goal) and
//!   the BARE prop leaf (`exp_leaf` — the forward hyp for the rest of the
//!   body). Production renders the prop once and uses it span_mark'd for
//!   the goal, bare for the hyp (`sst_to_lean::walk_obligations`).
//! * `StmX::Loop{cond|original_cond, invs, decrease, id}` (finding-3) —
//!   the maintain/use telescopes production builds. `modified_vars` is
//!   NOT read (it is `None` at this SST stage); the havoc set is
//!   RE-DERIVED via `sst_to_lean::collect_modifications(body)` filtered
//!   by `local_typs` (= production's `WpCtx.type_map`), exactly as
//!   `build_wp_loop` does. Emits: the modified-local `∀`-binders +
//!   parallel `_h_hoist_N` type-bound hyps, the standard invariants as
//!   `(_h_hoist_N, ANNOTATED obligation leaf)`, the ANNOTATED cond /
//!   ¬cond hyps (shared `_h_hoist_N` name), and the single-level decrease
//!   snapshot (`_tactus_d_old_<id>_0`) + its annotated
//!   `0 ≤ D ∧ D < d_old` obligation. `_h_hoist_N` names replay
//!   `hoist_all`'s walk counter (and, S3-pre, the per-goal counter of
//!   `OblCtx::split_leading_binders` — the extracted prefix contains no
//!   lets, so positions coincide with walk ordinals) so the binder-name
//!   ids unify with the goal side.
//!   bootstrap-79 (break-form): when the loop is `loop_normalize`'s
//!   canonical `loop { setup; if !exp { break; } body }` (cond: None,
//!   original_cond: Some((setup, exp)), non-empty setup, exactly the
//!   synthesized guard break), the Loop node additionally carries the
//!   transcribed setup (`setup` — ONE transcription from
//!   `original_cond`; refWp derives the maintain-inline and
//!   exit-hoisted renderings), the exit-reclose obligations
//!   (`inv_obligs_break` — invariant texts at the post-setup rename
//!   state), and the three cond-flavored guard leaves production's
//!   three goal families actually carry (`break_guard_ann` = span_mark'd
//!   `¬exp` for the exit-reclose telescope, `neg_neg_cond_ann` =
//!   `¬(span_mark'd ¬exp)` for the maintain else-guard,
//!   `break_use_ann` = BARE `¬exp` for the post-loop exit-fact hyp —
//!   production's exit_wrap pushes `LExpr::not(cond)` unmarked). The
//!   classical slots stay in their classical shapes (`neg_cond_ann` =
//!   999999 for break-form; the three break-form slots = 999999 for
//!   classical). Anything else with a `Break` keeps the loud
//!   `break-or-continue` reject.
//! * `StmX::Call` (bootstrap-02b — THE one non-transcription trusted
//!   step). The callee's `requires`/`ensures` are VIR-AST clauses that
//!   must be INSTANTIATED at THIS call's actual args before they can be
//!   rendered — the serializer cannot transcribe them verbatim. The
//!   instantiation (callee resolution + param→arg substitution + the
//!   #128 ret-eq detection + the return-typ coerce) is done by
//!   `sst_to_lean::cert_call_leaves`, which reuses production's EXACT
//!   renderers (`build_call_substitutions` / `render_call_ensures` /
//!   `type_bound_predicate`) so the leaf TEXT byte-matches the goal
//!   side (leaf content is uncertified — see the trusted-surface caveats
//!   — so it MUST reuse the production path to match). The resulting
//!   `StmData::Call { reqs, post }` FrameList STRUCTURE is then assembled
//!   INDEPENDENTLY by `call_stm` (this module), so the frame shape — the
//!   content the W2 `decide` bridge validates — is the serializer's own
//!   code, not a copy of production's `push_post_call_frames` (Option 1,
//!   DESIGN-W2-refwp.md §2.6). Restricted subset: Static + same-crate +
//!   no-`&mut` + no-generic + ret-eq path + dest present. Every other
//!   shape fails loud (sharp census tags below).
//! * EMITTER-COUNTER discipline (bootstrap-78 S1, card E5): production
//!   names its per-call gensyms (`_tactus_mut_post_<id>`,
//!   `_tactus_ret_<id>`) from the per-fn `ObligationEmitter.counter`,
//!   which is ALSO consumed by every emitted theorem — so the names
//!   depend on how many theorems precede the call in walk order. The
//!   serializer replays the counter (`Serializer.emit_ordinal`, threaded
//!   into `cert_call_leaves`): Assert/AssertCompute +1 (incl. the
//!   recursion pass's CheckDecreaseHeight termination asserts, which are
//!   ordinary raw-body Asserts), AssertQueryTactus +1, AssertQueryNl
//!   body walk + 1 for the query's `Wp::Done(True)` terminator (the
//!   `_tactus_ensures_` theorem, S1b/mul_bound), loop entry invs
//!   +|invs| before the body walk, loop maintain + decrease +|invs|+1
//!   after, each Ret terminal +|obligation list|, each call
//!   +muts+1(+1 iff requires), the two-way-join desugar REPLAYS the
//!   reused continuation's theorem count after the else branch —
//!   production clones `after` into both branch Wps and consumes twice
//!   (S1b/count_down id 5, clamped_inc ids 4-5; a gensym-consuming
//!   continuation rejects `call-in-branch-join`), and a break-form
//!   loop's cond-setup walks TWICE (bootstrap-79): the body run (the
//!   normalized body's inline copy) consumes its call ordinals between
//!   the entry and exit-reclose theorems, the exit-reclose theorems
//!   (+|invs|) land between the body-run setup and the user-body walk
//!   (mirroring the break leaf's position in production's emission),
//!   and the exit replay (production's `exit_wrap` re-running
//!   `build_wp(cond_setup, …)` around the post-loop continuation)
//!   consumes the setup's ordinals AGAIN after the decrease theorem
//!   (count_to_len ids 2/7, copy_word ids 5/20). This row is NOT a trusted
//!   predicate (unlike poison / the N2 peel): it is CHECKED twice — at
//!   emission time, the replayed per-theorem id predictions are compared
//!   element-wise against the ids production's goal names carry
//!   (`emit-counter-drift` reject on mismatch, validating the whole
//!   table incl. loop rows + wrap-mode walk-order timing on every
//!   cert), and any surviving gensym-name drift diverges cert leaf ids
//!   from production's goals and fails the W2 bridge loudly (fill_zeros
//!   `_5`/`_6` is the pinning evidence; the per-call shell-counter-from-0
//!   it replaced matched only single-consumer fns by accident).
//!
//! ## Deliberately NOT read (each a stage-A exclusion — fail-loud)
//!
//! * `StmX::Call` shapes OUTSIDE the restricted subset above — each a
//!   sharp fail-loud tag (so the census pinpoints the missing arm):
//!   `call-trait` (trait-method-impl callee), `call-crosscrate` (callee
//!   not in `fn_map`), `call-mut` (`&mut` param — the bootstrap-78 S3
//!   existential/rebind arm, pending), `call-mut-ret` (`&mut` RETURN —
//!   the returned-mut-ref prophecy-composition machinery, out of scope
//!   with zero corpus population), `call-generic` (type params —
//!   instantiated-typ leaves), `call-unit-dest` (unit-returning call, no
//!   dest binder), `call-dynamic-resolved` / `call-trait-default`
//!   (non-Static resolution), and `call-forall-path` (a callee with no
//!   `r == E` ensures — the ∀-path frame assembly, pending a validating
//!   fixture).
//! * `StmX::AssertBitVector` / `AssertQuery` — bv/compute/query asserts
//!   and their isolated contexts (tags `assert-bitvector`/`assert-query`).
//! * `StmX::OpenInvariant` / `ClosureInner` / `BreakOrContinue` —
//!   concurrency, closures, loop control. `BreakOrContinue` therefore also
//!   excludes `invariant_except_break` loops. The ONE Break the walk
//!   accepts is `loop_normalize`'s synthesized guard break inside the
//!   canonical break-form — and it is never walked: the Loop arm
//!   pattern-matches the shape and mirrors at the `original_cond` level
//!   (bootstrap-79). Verus-lowered user while-with-breaks (original_cond
//!   with an EMPTY setup — production's `original_cond_recoverable`
//!   path, vacuous break-leaf goals) stay rejected for now.
//! * `check.unwind`, masks, recommends, fuel/reveal *state*,
//!   `assert_id`/`base_error`, `mode`, trait dispatch/impl-subst — none
//!   bear a stage-A obligation the mirror models. (`check.local_decls`
//!   IS read now — finding-3 uses it as the loop havoc set's typ map;
//!   loop `decrease` measures ARE read for the decrease obligation.)
//! * `StmX::Air` / `Fuel` / `RevealString` — transparently ELIDED (the
//!   walker returns `after` unchanged for these); not obligation-bearing,
//!   so not a rejection.
//!
//! ## Trusted-surface caveats (leaf content is opaque; stage A does not
//! certify it — W6 does)
//!
//! * Most leaves are rendered by the PRODUCTION renderer with an EMPTY
//!   `RenderCtx` (`sst_exp_to_ast_checked`), then pretty-printed
//!   (`lean_pp::pp_expr`) and interned by text: identical text ⇒ same id.
//!   Obligation leaves (`oblig_leaf` / `neg_oblig_leaf`) and the RetBind
//!   return value instead use the binder-aware `render_ctx()` (next bullet).
//!   Leaf-renderer bugs beyond that are NOT caught here.
//! * Binder id = the interned leaf id of the binder's rendered name.
//!   The SSA-fresh-per-occurrence discipline (DESIGN-W2-refwp §2.1) is a
//!   W2 refinement — deferred because N3a's only consumer of ids is
//!   `stm_size`/`binder_len`, which ignore the id value.
//! * `Ret` ensures obligations and the `RetBind` return value are rendered
//!   through `render_ctx()` — byte-for-byte production's `WpCtx`
//!   postcondition ctx `with_fn_map(&fn_map).with_binder_typs(&caller_param_typs)`
//!   (bootstrap-18) — so an explicit `&`-param deref (`*p`) in the ensures
//!   renders as `p.deref`, matching the goal side (closes head_exec's
//!   obligation leaf). The `RetBind` return VALUE additionally applies
//!   production's per-leaf return-typ coercion (`lift_if_value_coerced`
//!   base case → `coerce_leaf`): the rendered value is coerced from its own
//!   Exp typ to the declared `ret_typ`, inserting the `.deref` for a bare
//!   `&`-value return (`fn clone(self: &S) -> S` → `self.deref`) that
//!   `binder_typs` alone can't reach — closing the clone RetBind divergence.
//!   Still NOT replicated: if-value LIFTING (a genuinely-liftable `if`
//!   return renders as one leaf here vs production's lifted `And`/`Imp`
//!   structure). A return needing that still diverges and HONEST-FAILS the
//!   `decide` bridge, never silent-passes. Simple-var / simple-arith returns
//!   (add_capped `s`, sum_to `acc`), explicit `&`-param derefs, and bare
//!   `&`-value returns now match.
//! * Field-path `Assign` (`x.f = e`) is rejected (tag `assign-field-path`).
//!
//! # Vocabulary versioning
//!
//! Cert files are only meaningful against the `tactus-core` build they
//! target. Each header records a content hash of the vendored vocabulary
//! (`$TACTUS_CORE_VOCAB`, when set). The bridge (W2/W3) hard-errors on a
//! mismatch — never a stale pass. N3a turn-1 uses a dependency-free FNV-1a
//! digest as a placeholder for the SHA-256 the §6 vendoring will bring.

use std::collections::{BTreeMap, HashMap};
use std::io::Write as _;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;

use vir::ast::{
    AssertQueryMode,
    ArithOp, BinaryOp, CallTarget, Constant, Dt, Expr as VirExpr, ExprX, InequalityOp, IntRange,
    KrateX, PatternX, Place, PlaceX, Typ, TypDecoration, TypX, UnaryOp, UnaryOpr, VarIdent,
};
use vir::sst::{BndX, CallFun, Exp, ExpX, FuncCheckSst, FunctionSst, LoopInv, Stm, StmX};

use crate::lean_ast::{
    AssertKind, BinOp as LBinOp, Expr as LExpr, ExprNode, GoalShape, GoalSpine, ObligationKind,
    Pattern as LPattern, Theorem, UnOp as LUnOp,
};
use crate::lean_pp::pp_expr;
use crate::to_lean_type::{lean_name, param_binder_typ, sanitize, short_name, typ_to_expr};

/// The emitted `tactus-core` namespace. The crate compiled from
/// `tactus-core/lib.rs` has crate name `lib`, so its inductives emit as
/// `lib.StmData`, `lib.LeafList`, … (see `tactus-core/out/lib/`). One
/// constant so a future vendored-rename to `TactusCore` is a one-line
/// change.
const NS: &str = "lib";

/// The emitted `tactus-core` namespace (`NS`), for cross-module callers
/// that assemble bridge terms (`generate::run_bridge_step`, W4a). Keeps
/// the vendored-rename a one-line change here, not several.
pub fn cert_ns() -> &'static str {
    NS
}

/// The Lean module cert files import to bring the vocabulary into scope
/// (the real emitted root module, built from `tactus-core/lib.rs`). §6's
/// vendored-olean plumbing points `LEAN_PATH` at it.
const CERT_IMPORT: &str = "TactusDefs_lib_exec";

// ── Flag ────────────────────────────────────────────────────────────

static CERT_EMIT_ENABLED: AtomicBool = AtomicBool::new(false);

/// Called once from the verifier with `args.tactus_emit_cert`. Mirrors
/// `generate::set_package_enabled`.
pub fn set_cert_emit_enabled(on: bool) {
    CERT_EMIT_ENABLED.store(on, Ordering::SeqCst);
}
pub fn cert_emit_enabled() -> bool {
    CERT_EMIT_ENABLED.load(Ordering::SeqCst)
}

// ── Census (also serves the N4 deliverable) ─────────────────────────

static CERT_CERTIFIED: AtomicU64 = AtomicU64::new(0);
static CERT_TOTAL: AtomicU64 = AtomicU64::new(0);

/// construct tag → number of fns rejected for it. `BTreeMap` for a
/// deterministic report ordering (no HashMap iteration order in output).
static CERT_REJECTIONS: Mutex<BTreeMap<String, u64>> = Mutex::new(BTreeMap::new());

fn census_note_certified() {
    CERT_CERTIFIED.fetch_add(1, Ordering::SeqCst);
    CERT_TOTAL.fetch_add(1, Ordering::SeqCst);
}

fn census_note_rejected(tag: &str) {
    CERT_TOTAL.fetch_add(1, Ordering::SeqCst);
    if let Ok(mut m) = CERT_REJECTIONS.lock() {
        *m.entry(tag.to_string()).or_insert(0) += 1;
    }
}

/// The crate-end `certified M/N fns` summary + ranked per-construct
/// rejection table. Empty when nothing was seen (flag off / no exec fns),
/// so the caller can skip printing.
pub fn census_report() -> String {
    let total = CERT_TOTAL.load(Ordering::SeqCst);
    if total == 0 {
        return String::new();
    }
    let certified = CERT_CERTIFIED.load(Ordering::SeqCst);
    let mut out = format!("tactus: cert: certified {}/{} fns", certified, total);
    if let Ok(m) = CERT_REJECTIONS.lock() {
        if !m.is_empty() {
            let mut rows: Vec<(&String, &u64)> = m.iter().collect();
            // Rank by count desc, then tag asc (deterministic).
            rows.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
            for (tag, n) in rows {
                out.push_str(&format!("\n  {:>5}  {}", n, tag));
            }
        }
    }
    out
}

/// Reset counters (used by acceptance harnesses that emit twice).
pub fn census_reset() {
    CERT_CERTIFIED.store(0, Ordering::SeqCst);
    CERT_TOTAL.store(0, Ordering::SeqCst);
    if let Ok(mut m) = CERT_REJECTIONS.lock() {
        m.clear();
    }
}

/// The W4c trust-inventory segment (b68): (census-excluded fn count,
/// one-line "tag×n, …" breakdown, tag-asc for determinism). The gate
/// note's bridge line appends it — the per-run trust inventory the
/// flip exists to print.
pub fn census_excluded_summary() -> (u64, String) {
    if let Ok(m) = CERT_REJECTIONS.lock() {
        let total: u64 = m.values().sum();
        let tags = m
            .iter()
            .map(|(t, n)| format!("{}×{}", t, n))
            .collect::<Vec<_>>()
            .join(", ");
        (total, tags)
    } else {
        (0, String::new())
    }
}

/// W4c red-path pin (b68): `TACTUS_BRIDGE_PERTURB=<substring>` marks
/// matching fns for a deliberate two-goal swap at emission — the only
/// way to exercise the bridge-fail channel in-harness (the gate
/// re-emits certs from SST every run, so an on-disk cert edit never
/// reaches the bridge). Loud when it matches; test-only hook, never
/// set in production. Living in the trusted serializer is acceptable
/// because the hook is ONE-DIRECTIONAL: it injects drift, which can
/// only force the bridge RED — it cannot manufacture a false pass.
fn bridge_perturb_matches(fn_short: &str) -> bool {
    static KNOB: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    let knob = KNOB.get_or_init(|| {
        std::env::var("TACTUS_BRIDGE_PERTURB").ok().filter(|v| !v.is_empty())
    });
    match knob {
        Some(pat) if fn_short.contains(pat.as_str()) => {
            eprintln!(
                "tactus: TACTUS_BRIDGE_PERTURB active — perturbing emitted goals of `{fn_short}` (test-only hook)"
            );
            true
        }
        _ => false,
    }
}

// ── Leaf interner ───────────────────────────────────────────────────

/// Insertion-ordered text → id table. Ids are assigned in
/// first-appearance order (walk order: params, requires, body pre-order,
/// ensures). Identical text ⇒ same id. Determinism: `texts` preserves
/// insertion order for emission; `index` is only a dedup lookup, never
/// iterated in an output path.
#[derive(Default)]
struct LeafTable {
    texts: Vec<String>,
    index: HashMap<String, u64>,
}

impl LeafTable {
    fn intern(&mut self, text: String) -> u64 {
        if let Some(&id) = self.index.get(&text) {
            return id;
        }
        let id = self.texts.len() as u64;
        self.index.insert(text.clone(), id);
        self.texts.push(text);
        id
    }
}

// ── The serializer ──────────────────────────────────────────────────

/// `Err(construct-tag)` from any walk step is the fail-loud signal: the
/// fn is not serialized, `construct-tag` names the offending SST shape,
/// and the crate run continues (the census records it).
type Sr<T> = Result<T, String>;

#[derive(Default)]
struct Serializer<'a> {
    leaves: LeafTable,
    /// The fn's ANNOTATED ensures obligation SLOTS (deep `RawExp` literals —
    /// span_mark'd, the `Return` goal, finding-1's Ret-annotation), set once
    /// before walking the body so the statement recursion stays a plain
    /// `&Stm → String`. Production renders each ensures at the return site as
    /// a `Postcondition` `SpanMark` (`WpCtx::new`); `oblig_slot`/`oblig_leaf`
    /// byte-match it so the goal-side postcondition leaf cancels. W6d.2b: each
    /// slot is `oblig_slot`'s output — a deep `RawExp.Span(loc, raw)` when the
    /// ensures is coverable (id recorded in `deep_ids`), else `atom_ob(id)`.
    pending_ens_oblig: Vec<String>,
    /// The span_mark'd ensures obligation LExprs behind
    /// `pending_ens_oblig` (bootstrap-79): the Ret arm re-renders them
    /// with a dest-collision rename applied (production freshens a
    /// taken return binder and renders the ensures with the rename in
    /// effect — copy_word's `out` → `out_hoist1`).
    pending_ens_marked: Vec<LExpr>,
    /// W6d.2b emit gate — the obligation leaf ids that went DEEP on the
    /// reference (SST) side: `oblig_slot`'s `raw_exp` succeeded, so the slot
    /// emitted `RawExp.Span(loc, raw)` instead of `atom_ob(id)`. The goal walk
    /// (`goal_data`, run AFTER the whole stm walk) consults this: it deepens a
    /// goal's leaf via `lexpr_to_exprdata` ONLY when the leaf's id is here AND
    /// the goal transcription succeeds — else it falls back to `Atom(id)`.
    /// "ob-drives" coordination: forced-atom obligation slots (Call reqs,
    /// Loop decrease, if-cond hyps) never enter this set, so their goals
    /// auto-stay atom (both sides match by id). A ref-deep/goal-atom mismatch
    /// (`raw_exp` ok but `lexpr_to_exprdata` fails) leaves the ob side deep +
    /// the goal atom → that fn's bridge fails (non-bridging, sound — never a
    /// silent pass). Fresh (empty) per fn (`Serializer::default`).
    deep_ids: std::collections::HashSet<u64>,
    /// The `sanitize(ret_name)` leaf for the return-value binding
    /// (finding-4), or `None` for a unit return (no declared `-> (r:T)`).
    /// The `Return` arm pairs it with the rendered return expression to
    /// emit `RetBind.RetLet <name> <val>`.
    pending_ret_name: Option<u64>,
    /// `VarIdent → Typ` for the fn's local declarations (finding-3),
    /// cloned from `check.local_decls` before the body walk. Mirrors
    /// production's `WpCtx.type_map` (built the SAME way,
    /// `sst_to_lean.rs`): `build_wp_loop` looks up each modified-local's
    /// typ here rather than trusting `StmX::Loop.modified_vars` (which is
    /// `None` at this SST stage). The `Loop` arm re-derives the havoc set
    /// via `collect_modifications(body)` and filters by this map, exactly
    /// as production does.
    local_typs: HashMap<VarIdent, Typ>,
    /// `VarIdent → Typ` for the fn's value params at their body-shadow
    /// Lean typ (bootstrap-18), built EXACTLY as production's
    /// `caller_param_typs` (`sst_to_lean::exec_fn_theorems_to_ast`): strip
    /// one outer ref decoration for `&mut`-style params, else as-declared.
    /// Threaded into `render_ctx()` so obligation / RetBind-value leaf
    /// rendering derefs `&`-params (`*p → p.deref`) the SAME way
    /// production's `WpCtx` postcondition `RenderCtx` (`with_binder_typs`)
    /// does — closing the head_exec / clone leaf-render divergences.
    caller_param_typs: HashMap<VarIdent, Typ>,
    /// The fn_map (callee resolution) threaded into `render_ctx()`
    /// alongside `caller_param_typs`, mirroring production's postcondition
    /// ctx (`WpCtx::new`, `with_fn_map(&fn_map)`). Load-bearing for the
    /// `&`-param deref at CALL-ARG positions: a plain-spec-fn call whose
    /// callee is in the map takes the migrated B5a typed-arg path
    /// (`exp_to_typed`), which bridges each `&`-param arg to the callee's
    /// declared param typ and so inserts the `.deref` (head_exec's
    /// `tree_head(*t)`). Absent the map the call falls off that path and
    /// the arg renders bare. Borrows the krate; empty (`Default`) until
    /// set in `serialize()`.
    fn_map: crate::expr_shared::RenderFnMap<'a>,
    /// The fn's declared return typ (bootstrap-18), derived EXACTLY as
    /// production's `WpCtx.ret_typ` (`sst_to_lean.rs:524`): the
    /// `post_condition.dest` VarIdent looked up in `local_typs` (=
    /// production's `type_map` = `check.local_decls`). `None` for unit
    /// returns or a dest with no decl entry. Threaded into the RetBind
    /// value render so the return value coerces from its own Exp typ to
    /// this — mirroring production's per-leaf return-typ coercion
    /// (`lift_if_value_coerced` base case, `coerce_leaf`). This inserts a
    /// `.deref` for a `&`-value return (`fn clone(self: &S) -> S` returns
    /// bare `Var(self) : &S` coerced to `S` → `self.deref`), closing the
    /// clone RetBind-value divergence that `binder_typs` alone can't (a
    /// bare Var read carries no explicit `*self` for `binder_typs` to
    /// deref). For a return whose Exp typ already equals this (u64→u64,
    /// arith returns, generic `T`) the coercion is a no-op, so no
    /// regression on the closing fixtures.
    ret_typ: Option<Typ>,
    /// G4/W6e — whether EVERY ensures obligation slot went DEEP
    /// (`oblig_slot` emitted `RawExp.Span`, not `atom_ob`). The Return-lift
    /// recompute conjoins `pending_ens_oblig` into the branch-folded leaf's
    /// `let r := …; (ens0 ∧ ens1)` tail; that fold is only faithful when
    /// every ensures is a real `Span`-deep slot (an `atom_ob` conjunct would
    /// render to `Atom` and diverge from the goal side's `SpanMark`). Set at
    /// setup, gated by the recompute — else it falls through to the current
    /// (opaque, still-honest-failing) Return path.
    pending_ens_all_deep: bool,
    /// G4/W6e — count of Return statements whose if-valued return LIFTED and
    /// was successfully recomputed into branch-folded `Ret([impl…], RetNone)`
    /// obligations. Zero ⇒ no lift happened ⇒ the post-stm-walk `deep_ids`
    /// seeding pass is a no-op (verdict-neutral). `>0` ⇒ the goal walk should
    /// deepen the matching `Implies`-topped goal-shape leaves (their ids are
    /// seeded from the actual production goal shapes, so they match by
    /// construction). Non-lift returns never touch this.
    lifted_return_recomputes: u64,
    /// N1-hoist mirror (bootstrap-74 slice 2): the 1-based ordinal of the
    /// LAST Hyp frame pushed on the current walk path — production's
    /// `hyp_counter` in `hoist_all`. Incremented at every FHyp-producing
    /// site (`next_hyp_name`); snapshotted/restored around If branches
    /// (each branch resumes from the pre-If count, its cond/neg-cond hyp
    /// taking the pre-If ordinal + 1 — count_down evidence: cond is
    /// `_h_hoist_1` in BOTH branches) and around AssertQueryNl scopes
    /// (production's `new_scope` drops hyps — the sub-walk numbers
    /// independently from 0, mul_bound evidence).
    hyp_ordinal: u64,
    /// Emitter-counter mirror (bootstrap-78 S1, card E5): production's
    /// `ObligationEmitter.counter` replayed in walk order. The counter
    /// feeds the `_tactus_mut_post_<id>` / `_tactus_ret_<id>` gensyms
    /// whose NAMES enter cert leaf texts at call sites — the per-call
    /// shell-emitter-from-0 was matching production only by accident of
    /// single-consumer fns (fill_zeros evidence: `_5`/`_6`). Consumption
    /// table (the faithfulness-contract rows; fill_zeros id sequence
    /// 2026-07-24 pins every row): Assert/AssertCompute theorem +1;
    /// AssertQueryTactus theorem +1; loop entry invariants +|invs|
    /// BEFORE the body walk; loop maintain + decrease +|invs|+1 AFTER;
    /// each Ret's obligation list +len (plain = |enss|, G4-folded =
    /// |branch impls|, fork = per-branch Ret each +|enss|); each call
    /// consumes inside `cert_call_leaves` (mut_post gensyms + fresh_ret
    /// ALWAYS + precondition theorem iff requires non-empty), threaded
    /// via `&mut` so multi-call fns accumulate. UNLIKE `hyp_ordinal`
    /// there is NO branch save/restore — theorem names are fn-unique
    /// and production never resets (head_exec `_1`/`_2` sequential
    /// across fork arms). NOT a trusted predicate (S1 review): the
    /// serializer-minted gensym names land in cert leaf/binder ids
    /// while production's goals carry production's own names, so any
    /// drift is a structurally LOUD bridge red — and the
    /// `predicted_theorem_ids` cross-check below catches table drift
    /// even earlier, at emission time.
    emit_ordinal: u64,
    /// Emission-time cross-check companion (bootstrap-78 S1 review):
    /// the predicted id of every THEOREM consumption, in walk order
    /// (gensym consumptions advance `emit_ordinal` without a
    /// prediction). Production's theorem names carry their consumed
    /// ids (`build_theorem_name`'s trailing `_<id>`), so after the
    /// goal walk the predictions are compared element-wise against the
    /// ids parsed from `goal_names` — a mis-counted site or an
    /// unmodeled consumer rejects the cert with a sharp
    /// `emit-counter-drift` tag instead of surfacing later as an
    /// opaque leaf diff. This validates the whole consumption table
    /// (including the loop rows and wrap-mode walk-order timing) on
    /// EVERY emitted cert, not only on fns whose gensym names print.
    predicted_theorem_ids: Vec<u64>,
    /// The caller's `&mut`-local names (sanitize-keyed mut-ref pars +
    /// BorrowMut decls) — `cert_call_leaves`' mut-target extraction
    /// consults it for bare-Var pass-along args (bootstrap-78 S3).
    /// Built in `serialize()` exactly as production's
    /// `mut_param_names` (exec_fn_theorems_to_ast).
    mut_ref_locals: std::collections::HashSet<String>,
    /// Names of residue (Bool-typed) lets in scope on the current walk
    /// path — the poison-check domain (bootstrap-74 slice 2). A hyp prop
    /// or let-equation mentioning one of these forces whole-goal wrap
    /// (the FHyp poison bit / the FLetH→FLet collapse), mirroring
    /// `hoist_all`'s bail check. Residue lets keep their source names
    /// (goal-position lets shadow textually), so a name stays
    /// poison-relevant for the rest of the walk.
    residue_names: Vec<String>,
    /// F4 (bootstrap-80 stage 2): the poison-derivation side table —
    /// (prop leaf id, deep `RawExp` text) for every poison-CHECKED prop
    /// registered while residue names are in scope. The reference derives
    /// the poison set from this table (`poisoned_props`) instead of
    /// trusting the emitted bit (endgame P1). Entries are skipped for
    /// props walked BEFORE any residue let exists (a prop can only
    /// mention names that exist at its walk point, and `residue_names`
    /// is monotone — the reference derives 0 for those, which is
    /// correct); with residues in scope, a transcription failure rejects
    /// loud when the prop's bit is 1 (`prop-deep-uncoverable`) and
    /// registers the opaque-atom fallback when 0 (guaranteed
    /// mention-free). One entry per prop id (the Assert/Assume pair
    /// shares a leaf).
    prop_deeps: Vec<(u64, String)>,
    /// Wrap-mode mirror (endgame A2): true when the fn's closer is
    /// NON-default (`!sst_to_lean::closer_is_default` — a fn-level
    /// `tactus_tactic` or a `proof { tac }` prefix). Production's
    /// `emit_leaf_theorem` NEVER hoists such fns' goals (the user
    /// tactic is positional against the wrap shape) and the Return
    /// keeps the legacy goal-position let — so every let classifies
    /// PLAIN here (Assign/FLet/RetLet, forcing refWp's wrap gate),
    /// never AssignH/FLetH/RetLetH.
    wrap_mode: bool,
    /// ATTR-ONLY closer bit (bootstrap-77 proof_block_fn evidence): a
    /// fn-level `tactus_tactic` sets `obl.closer` to the user tactic for
    /// EVERY goal — those wrap. A proof-block PREFIX does NOT touch
    /// `obl.closer` (it composes into the tactic AFTER the hoist
    /// decision), so a prefix-only fn's goals still HOIST — only its
    /// Return ROUTE flips to the legacy fold (`wrap_mode` above, the
    /// `closer_is_default` DFS). The FnCtxData `closer_default` seed and
    /// the freshening/loop gates key on THIS bit; route decisions (G4,
    /// ret_fork, RetLetH) key on `wrap_mode`.
    attr_user_closer: bool,
    /// `LocalDeclKind::AssertByVar` locals (assert-forall skolems),
    /// mirroring `WpCtx.assert_by_var_typs` — a DeadEnd scope
    /// referencing any of these ∀-binds them in production's goal
    /// telescope (`Wp::Scope.scope_vars`), which stage A cannot
    /// express: census-reject loud (`assert-forall`, endgame
    /// A6-short). The real quantifier-binder arm is planned post-flip
    /// (endgame table row 11b).
    assert_by_var_typs: std::collections::HashMap<&'a vir::ast::VarIdent, &'a Typ>,
    /// The declared return var's NAME text (`sanitize`d, finding-4's
    /// `pending_ret_name` companion) — the eq-leaf pair for the hoisted
    /// return binding (`RetBind::RetLetH`, bootstrap-74 slice 2) renders
    /// `_h_<ret>_hoist1` and `<ret> = <value>` from it.
    pending_ret_lname: Option<String>,
    /// Local let-binder typs (Lean-level), mirroring production's
    /// `OblCtx.let_binder_typs`: populated at call-dest lets with the
    /// instantiated callee ret typ and trust `true` (the Phase-5 site,
    /// sst_to_lean.rs:4304) so a downstream Var read of a Ref-typed
    /// call result coerces with `.deref` — the `r = tmp__1.deref`
    /// RetLet equation in vec_read. (Assign lets are NOT recorded yet —
    /// no current fixture diverges on it; add the walk_let mirror if
    /// one shows up.)
    let_binder_typs: im::HashMap<crate::lean_name::LeanName, (Typ, bool)>,
    /// N1-hoist shadow mirror (bootstrap-74 slice 2 Round D): every
    /// name bound so far on the current walk path — seeded with the
    /// fn's param / bound-hyp / req names, extended by every let dest,
    /// hyp name, and binder name. Production's `hoist_all` freshens a
    /// later binding of a taken name (`i` → `i_hoist1`) — but ONLY in a
    /// HOISTED goal: wrap-mode goals keep source names (goal-position
    /// lets shadow textually). So freshening is gated on `wrap_forced`
    /// (below): freshen iff the current prefix is wrap-free. (The MIX
    /// case — wrap-free at the shadow, a wrap-forcer later — would
    /// emit the freshened name into wrap goals that production renders
    /// plain: DETECTED at the wrap-forcer sites (`mark_flet_forced` /
    /// `mark_poison_forced`) and census-rejected loud,
    /// `hoist-mixed-shadow`, endgame P2/b68.)
    bound_names: std::collections::HashSet<String>,
    /// The active shadow renames (source name → freshened name), from
    /// `fresh_let_name` on a taken let dest. Applied to every
    /// subsequently rendered LExpr (hyp props, assign rhs, conds, ret
    /// values, the re-close invariant obligations — the `i_hoist1 ≤ n`
    /// evidence), mirroring production's `rename_frame_vars`. Cleared of
    /// a loop's mod-var names at loop exit (the use telescope re-binds
    /// the source names — `r = acc`, not `r = acc_hoist1`).
    rename_env: HashMap<String, crate::lean_name::LeanName>,
    /// Declared datatypes by path (bootstrap-77 A5), built EXACTLY as
    /// `WpCtx::new`'s `datatypes` map — the N2 ctor-frame mirror
    /// (`ctor_fork_frames`) reads variant field lists here.
    dt_map: std::collections::HashMap<&'a vir::ast::Path, &'a vir::ast::DatatypeX>,
    /// Wrap-forcing state, split by source (the AssertQueryNl scope
    /// strips hyps but keeps lets):
    /// * `flet_forced` — a plain FLet went out (typ-less or
    ///   poison-collapsed let). Persists through query scopes.
    /// * `poison_forced` — a poisoned hyp went out. Stripped by query
    ///   scopes (the query drops outer hyps).
    /// Either forces whole-goal wrap from that point on; both are
    /// monotone along a walk path and snapshot per If-branch.
    flet_forced: bool,
    poison_forced: bool,
    /// W4c red-path pin (b68): set when `TACTUS_BRIDGE_PERTURB` matches
    /// this fn — `goal_list` swaps the first two goals so the emitted
    /// cert provably drifts from refWp and the bridge fails. Test-only.
    perturb_goals: bool,
}

impl<'a> Serializer<'a> {
    // ── Leaf rendering ──────────────────────────────────────────────

    fn exp_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let lexpr = crate::to_lean_sst_expr::sst_exp_to_ast_checked(e)
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        Ok(self.leaves.intern(pp_expr(&lexpr)))
    }

    /// The binder-aware `RenderCtx` for rendering THIS fn's obligation and
    /// RetBind-value leaves (bootstrap-18). Byte-for-byte production's
    /// `WpCtx` postcondition ctx (`sst_to_lean.rs:511`,
    /// `RenderCtx::with_fn_map(&fn_map).with_binder_typs(&caller_param_typs)`)
    /// so a `&`-param deref (`*p`) renders as `p.deref`, matching the
    /// goal-side leaf. BOTH ingredients are load-bearing: `binder_typs`
    /// gives the Var read its `&T` actual typ; `fn_map` puts a
    /// plain-spec-fn call on the migrated typed-arg path that bridges (and
    /// so derefs) that arg. For a fn with no ref params both are inert, so
    /// this is bit-for-bit the old empty-ctx render there (no regression on
    /// the closing fixtures).
    fn render_ctx(&self) -> crate::expr_shared::RenderCtx<'_> {
        crate::expr_shared::RenderCtx::with_fn_map(&self.fn_map)
            .with_binder_typs(&self.caller_param_typs)
    }

    /// Render an obligation as an ANNOTATED leaf, byte-matching
    /// production's goal leaf (finding-1). Production wraps every
    /// obligation's rendered prop in a `SpanMark`
    /// (`sst_to_lean::walk_obligations`); its pp is
    /// `/- @rust:<loc> -/ <bare prop>`, where `<loc>` is
    /// `format_rust_loc(&span)` and `<bare prop>` is the SAME render the
    /// bare hyp leaf uses. We reconstruct via the identical
    /// `sst_exp_to_ast_checked` → `span_mark` → `pp_expr` path, so the
    /// interned text equals the goal-side leaf (`goal_data` interns the
    /// production `SpanMark` the same way) and the two cancel across the
    /// W2 bridge. `kind` never reaches the pp output (only `rust_loc` +
    /// `inner` do — see `lean_pp`), so `Plain` suffices for byte-match.
    fn oblig_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let marked = self.marked_oblig_lexpr(e)?;
        Ok(self.leaves.intern(pp_expr(&marked)))
    }

    /// The span_mark'd obligation LExpr (no intern) — kept so the Ret
    /// arm can apply a dest-collision rename and re-intern
    /// (bootstrap-79, `ret_terminal_opt`).
    fn marked_oblig_lexpr(&mut self, e: &Exp) -> Sr<LExpr> {
        // Render through the binder-aware ctx (bootstrap-18) so a `&`-param
        // deref matches production's postcondition leaf. The ctx's `&self`
        // borrow ends with this statement (`inner` is owned), before
        // `intern` takes `&mut self`. The shadow renames (Round D) apply
        // to the obligation too — production renames annotated obligation
        // texts identically to hyps (`0 ≤ acc + i_hoist1 ∧ …`, sum_to).
        let inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let inner = self.apply_renames(&inner_raw);
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        Ok(LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            inner,
        ))
    }

    /// W6d.2b emit gate — the deep-or-atom obligation SLOT for one raw SST
    /// obligation `e`. Returns `(id, slot)` where `id` is the interned
    /// span_mark'd leaf id (== the goal-side leaf id, the atom-fallback match
    /// key) and `slot` is the `RawExp` literal that fills a `StmData`
    /// obligation field.
    ///
    /// The "ob-drives" rule: attempt the reference transcription `raw_exp(e)`.
    /// On success the obligation is coverable — emit the DEEP
    /// `RawExp.Span(loc, raw)` (the raw SST has no SpanMark node — bootstrap-22
    /// — so the `Span` wrapper is added HERE, matching production's outermost
    /// `SpanMark` that the goal side transcribes; `loc` interns
    /// `format_rust_loc(&e.span)`, the SAME text `oblig_leaf`'s span_mark
    /// carries, so the two `Span`/`SpanMark` locs share an id). Record `id` in
    /// `deep_ids` so the goal walk deepens the matching leaf too. On failure
    /// (a non-cast-class shape, or a `typ_data`/arity/range sub-fail) fall back
    /// to the opaque `atom_ob(id)` — the SAME id the goal side will atom-match
    /// (verdict-neutral, exactly the W6d.2a behavior). The whole fn still
    /// serializes; only THIS obligation stays shallow.
    ///
    /// `render_exp(RawExp.Span(loc, render(raw)))` = `ExprData.SpanMark(loc,
    /// render(raw))`, and the goal side emits `ExprData.SpanMark(loc,
    /// lexpr_to_exprdata(inner))` — so the bridge `decide`s
    /// `expr_eq(render(raw), lexpr(inner))`, the Friction-2 catcher.
    fn oblig_slot(&mut self, e: &Exp) -> Sr<(u64, String)> {
        let id = self.oblig_leaf(e)?;
        let slot = match self.raw_exp(e) {
            Ok(raw) => {
                let loc = self.text_leaf(&crate::obligation_naming::format_rust_loc(&e.span));
                self.deep_ids.insert(id);
                format!("({}.RawExp.Span {} {})", NS, loc, box_raw(&raw))
            }
            Err(_) => atom_ob_lit(id),
        };
        Ok((id, slot))
    }

    /// Render `¬<annotated e>` as a leaf, byte-matching production's
    /// loop-exit hypothesis (finding-3). The `use` telescope pushes
    /// `LExpr::not(cond_marked(&c))` (`sst_to_lean::walk_loop`), i.e. the
    /// NEGATION wraps the span_mark'd cond (NOT the bare prop).
    /// Reconstructed via the identical
    /// `span_mark` → `not` → `pp_expr` path, so the interned text equals
    /// the goal-side `neg_cond_ann` leaf and the two cancel across the
    /// bridge. `kind` never reaches the pp (see `oblig_leaf`), so `Plain`
    /// suffices even though production marks the cond `LoopCondition`.
    fn neg_oblig_leaf(&mut self, e: &Exp) -> Sr<u64> {
        // Binder-aware render (bootstrap-18) — see `oblig_leaf`. Shadow
        // renames apply identically (Round D).
        let inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let inner = self.apply_renames(&inner_raw);
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        let marked = LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            inner,
        );
        Ok(self.leaves.intern(pp_expr(&LExpr::not(marked))))
    }

    /// Render `¬(/- @rust:…-/ ¬<e>)` as a leaf (bootstrap-79) — the
    /// normalized If's ELSE-guard hypothesis on the maintain path.
    /// `loop_normalize` synthesizes `if !exp { break; }` whose cond is
    /// the span_mark'd `¬exp`; the else branch's guard is that marked
    /// negation wrapped in ONE more (unmarked) `not` —
    /// `LExpr::not(span_mark(loc, LExpr::not(render(e))))` — so the
    /// @rust comment sits INSIDE the outer ¬, around the inner one
    /// (count_to_len maintain goal evidence). NOT
    /// `LExpr::not(LExpr::not(span_mark(…)))` — that puts the comment
    /// on the bare cond and diverges from production.
    fn neg_neg_oblig_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let inner = self.apply_renames(&inner_raw);
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        let marked_neg = LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            LExpr::not(inner),
        );
        Ok(self.leaves.intern(pp_expr(&LExpr::not(marked_neg))))
    }

    /// Render `/- @rust:…-/ ¬<e>` — the span_mark'd NEGATION (bootstrap-79,
    /// the exit-reclose telescope's If-then-guard hyp): production's
    /// walk_if marks the synthesized `¬exp` itself, so the @rust comment
    /// sits OUTSIDE the negation (unlike `neg_oblig_leaf`'s
    /// `¬(/- …-/ …)`).
    fn marked_neg_cond_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let inner = self.apply_renames(&inner_raw);
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        let marked = LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            LExpr::not(inner),
        );
        Ok(self.leaves.intern(pp_expr(&marked)))
    }

    /// Render BARE `¬<e>` (bootstrap-79, the post-loop continuation's
    /// exit-fact hyp): production's `build_wp_loop` exit_wrap pushes
    /// `LExpr::not(lower_validated(cond))` with NO span_mark.
    fn bare_neg_cond_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let inner = self.apply_renames(&inner_raw);
        Ok(self.leaves.intern(pp_expr(&LExpr::not(inner))))
    }

    /// The invariant texts with the CURRENT shadow renames applied —
    /// the re-close obligations at whatever walk point we're at
    /// (bootstrap-79, factored out of `loop_stm`): post-SETUP for the
    /// exit-reclose family (`inv_obligs_break`), post-BODY for the
    /// maintain-reclose family (`inv_obligs_exit`). Slot discipline
    /// (production's ob-drives, sum_to evidence): a renamed text whose
    /// id is ALREADY deep (the renames were a no-op — same interned id
    /// as the init's deep leaf) keeps the init's deep `RawExp.Span`
    /// slot; a genuinely renamed text (a NEW id, not in `deep_ids`) is
    /// the opaque `atom_ob` fallback — matching the production goal
    /// side exactly.
    fn renamed_inv_slots(&mut self, invs: &[LoopInv], init_slots: &[String]) -> Sr<Vec<String>> {
        let mut slots: Vec<String> = Vec::new();
        for (i, li) in invs.iter().enumerate() {
            let inner = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                &li.inv,
                &self.render_ctx(),
            )
            .map_err(|reason| format!("leaf-render: {}", reason))?;
            let renamed = self.apply_renames(&inner);
            let loc = crate::obligation_naming::format_rust_loc(&li.inv.span);
            let marked = LExpr::span_mark(
                loc,
                Some(li.inv.span.clone()),
                AssertKind::Obligation(ObligationKind::Plain),
                renamed,
            );
            let id = self.leaves.intern(pp_expr(&marked));
            if self.deep_ids.contains(&id) {
                // The renames were a no-op on this invariant: the init's
                // deep slot (same id) is the correct re-close slot too.
                slots.push(init_slots[i].clone());
            } else {
                slots.push(atom_ob_lit(id));
            }
        }
        Ok(slots)
    }

    /// Render the single-level loop decrease obligation as an ANNOTATED
    /// leaf, byte-matching production's `decrease_marked` (finding-3).
    /// Production (`sst_to_lean::lex_decrease_obligation` +
    /// `build_wp_loop`) builds, for a one-level `decreases D`:
    ///   `span_mark(loc, LoopDecrease, (0 ≤ D) ∧ (D < _tactus_d_old_<id>_0))`
    /// where `D = lower_validated(&decrease[0])` (empty `RenderCtx`, so
    /// identical to `exp_leaf`'s `sst_exp_to_ast_checked`) and the `old`
    /// snapshot is a synthetic Var of the per-loop d_old name. `kind`
    /// (`LoopDecrease`) is byte-irrelevant; the loc is `decrease[0].span`.
    fn decrease_oblig_leaf(&mut self, d: &Exp, loop_id: u64) -> Sr<u64> {
        // The shadow renames apply to the measure (Round D evidence:
        // `0 ≤ n - i_hoist1 ∧ n - i_hoist1 < _tactus_d_old_0_0` — the
        // decrease is evaluated at body END, after the body's rebinds;
        // the d_old VALUE is the loop-entry one and stays unrenamed).
        let cur_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked(d)
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let cur = self.apply_renames(&cur_raw);
        let old = LExpr::var_synthetic(format!("_tactus_d_old_{}_0", loop_id));
        let inner = LExpr::and(
            LExpr::le(LExpr::lit_int("0"), cur.clone()),
            LExpr::lt(cur, old),
        );
        let loc = crate::obligation_naming::format_rust_loc(&d.span);
        let marked = LExpr::span_mark(
            loc,
            Some(d.span.clone()),
            AssertKind::Obligation(ObligationKind::LoopDecrease),
            inner,
        );
        Ok(self.leaves.intern(pp_expr(&marked)))
    }

    fn typ_leaf(&mut self, typ: &Typ) -> u64 {
        self.leaves.intern(pp_expr(&typ_to_expr(typ)))
    }

    fn param_typ_leaf(&mut self, typ: &Typ, is_mut: bool) -> u64 {
        self.leaves.intern(pp_expr(&param_binder_typ(typ, is_mut)))
    }

    fn text_leaf(&mut self, text: &str) -> u64 {
        self.leaves.intern(text.to_string())
    }

    /// Binder id for a `VarIdent` = the interned leaf id of its rendered
    /// name (see the module doc's binder-id caveat).
    fn binder_id(&mut self, vid: &VarIdent) -> u64 {
        let name = crate::lean_name::LeanName::from_var_ident(vid);
        self.text_leaf(name.as_str())
    }

    // ── N1-hoist mirror helpers (bootstrap-74 slice 2) ───────────────

    /// Intern the NEXT hyp name `_h_hoist_{ordinal}` and bump the walk
    /// counter — production's `hyp_counter` in `hoist_all` (each Hyp
    /// frame's 1-based ordinal among Hyp frames on the goal's path).
    fn next_hyp_name(&mut self) -> u64 {
        self.hyp_ordinal += 1;
        self.text_leaf(&format!("_h_hoist_{}", self.hyp_ordinal))
    }

    /// Counter mirror: consume `n` production THEOREM ids, recording
    /// each predicted id for the emission-time cross-check. (Gensym
    /// consumption — call sites, inside `cert_call_leaves` — advances
    /// `emit_ordinal` without predictions.)
    fn consume_theorem_ids(&mut self, n: u64) {
        for _ in 0..n {
            self.emit_ordinal += 1;
            self.predicted_theorem_ids.push(self.emit_ordinal);
        }
    }

    /// The shadow mirror's freshening (Round D) — production's `fresh()`
    /// in `hoist_all`: a later binding of a taken name gets
    /// `{base}_hoist{N}` (first free N) — but ONLY when the goal hoists:
    /// wrap-forced prefixes keep source names (production's wrap-mode
    /// textual shadowing). Records the rename in `rename_env` (applied
    /// to all subsequently rendered leaves) and claims the chosen name.
    /// Returns the CHOSEN name (the base itself when free or
    /// wrap-forced).
    fn fresh_let_name(&mut self, base: &str) -> String {
        if self.flet_forced || self.poison_forced || !self.bound_names.contains(base) {
            self.bound_names.insert(base.to_string());
            return base.to_string();
        }
        let mut i = 1usize;
        loop {
            let cand = format!("{}_hoist{}", base, i);
            if !self.bound_names.contains(&cand) {
                self.bound_names.insert(cand.clone());
                self.rename_env.insert(
                    base.to_string(),
                    crate::lean_name::LeanName::synthetic(cand.clone()),
                );
                return cand;
            }
            i += 1;
        }
    }

    /// Mark the walk prefix as wrap-forcing from a plain FLet (typ-less
    /// or poison-collapsed let): persists through query scopes.
    ///
    /// MIX detector (endgame P2, b68): if a freshened shadow is live on
    /// this path (`rename_env` non-empty — a taken name was re-bound
    /// while wrap-free), production renders LATER wrap-mode goals with
    /// the SOURCE name (textual shadowing) while this mirror's
    /// `apply_renames` emits the freshened one — the documented
    /// `hoist-mixed-shadow` honest-fail. Reject loud so the census
    /// names the class instead of an unclassified bridge drift (O7).
    fn mark_flet_forced(&mut self) -> Sr<()> {
        if !self.rename_env.is_empty() {
            return Err("hoist-mixed-shadow".to_string());
        }
        self.flet_forced = true;
        Ok(())
    }

    /// Mark the walk prefix as wrap-forcing from a poisoned hyp:
    /// stripped by query scopes (they drop outer hyps). Same MIX
    /// detector as `mark_flet_forced`.
    fn mark_poison_forced(&mut self) -> Sr<()> {
        if !self.rename_env.is_empty() {
            return Err("hoist-mixed-shadow".to_string());
        }
        self.poison_forced = true;
        Ok(())
    }

    /// Snapshot/restore discipline for branchy walks (If arms,
    /// AssertQueryNl): the per-path state that must not leak across
    /// branches. The hyp ORDINAL has its own snapshot rule (each branch
    /// resumes from the pre-If count); this bundles the rest.
    fn branch_state(&self) -> (std::collections::HashSet<String>, HashMap<String, crate::lean_name::LeanName>, bool, bool) {
        (self.bound_names.clone(), self.rename_env.clone(), self.flet_forced, self.poison_forced)
    }

    fn restore_branch(&mut self, state: (std::collections::HashSet<String>, HashMap<String, crate::lean_name::LeanName>, bool, bool)) {
        self.bound_names = state.0;
        self.rename_env = state.1;
        self.flet_forced = state.2;
        self.poison_forced = state.3;
    }

    /// Apply the active shadow renames to a rendered LExpr
    /// (production's `rename_frame_vars` — capture-respecting).
    fn apply_renames(&self, lx: &LExpr) -> LExpr {
        crate::sst_to_lean::rename_frame_vars(lx, &self.rename_env)
    }

    /// Poison check: does the rendered prop mention any in-scope
    /// residue-let name? Mirrors `hoist_all`'s bail check
    /// (`lexpr_mentions_var` over the hoisted binders' types) — a
    /// poisoned hyp forces the WHOLE goal into wrap mode, and a
    /// poisoned let-equation collapses its FLetH to a plain FLet
    /// (lossless: wrap mode discards the hoist payload).
    /// F4 (bootstrap-80 stage 2): the bit this computes is era-1
    /// cross-check data — refWp derives the mark reference-side from
    /// `prop_deeps` (`register_prop_deep` below); the serializer's copy
    /// rides along UNREAD until era 2 deletes the slots. It also serves
    /// as the emission-time guard at sites that CANNOT register a deep
    /// (Call.post props): a real mention there rejects the cert loud
    /// (`prop-deep-uncoverable`) rather than silently mis-deriving.
    fn hyp_poison(&self, e: &LExpr) -> u64 {
        if self.residue_names.iter().any(|n| crate::sst_to_lean::lexpr_mentions_var(e, n)) {
            1
        } else {
            0
        }
    }

    /// F4: register a prop's deep transcription in the `prop_deeps` side
    /// table. `leaf_id` is the FHyp / eq-prop leaf the reference looks
    /// up; `e` is the SST exp the prop was rendered from; `hp` is the
    /// prop's era-1 poison bit (the caller just computed it). The
    /// transcription is the dumb faithful `raw_exp` copy — renames and
    /// the Span/Not/eq wrappers around it don't change the Var-atom set
    /// the mention check reads (an eq prop's deep transcribes the RHS:
    /// the dest binder is a non-Bool let / synthetic ret name, never a
    /// residue name). Skipped when no residue name is in scope (a prop
    /// can only mention names that exist at its walk point). On a
    /// transcription failure (a shape outside `raw_exp`'s coverage,
    /// e.g. a `usize` HasType range): bit 1 rejects LOUD (genuinely
    /// underivable — `prop-deep-uncoverable`); bit 0 registers the opaque-atom
    /// constant deep — the derived 0 is GUARANTEED correct by the bit
    /// the caller just computed, and the bridge backstops even a buggy
    /// bit (a wrong 0 hoists where production wrapped → red).
    fn register_prop_deep(&mut self, leaf_id: u64, e: &Exp, hp: u64) -> Sr<()> {
        if self.residue_names.is_empty() {
            return Ok(());
        }
        // One entry per prop id (keep first): the Assert forward hyp and
        // its following Assume carry the SAME prop leaf (FINDINGS-b74
        // §3's duplicated pair) — without dedup the table holds the same
        // transcription twice, cert-noise with no semantic content.
        if self.prop_deeps.iter().any(|(id, _)| *id == leaf_id) {
            return Ok(());
        }
        match self.raw_exp(e) {
            Ok(raw) => {
                self.prop_deeps.push((leaf_id, raw));
                Ok(())
            }
            Err(reason) => {
                if hp == 1 {
                    Err(format!("prop-deep-uncoverable: {}", reason))
                } else {
                    // The OPAQUE-ATOM fallback (the `atom_ob` idiom used
                    // for uncoverable obligations): honest about being a
                    // non-transcription, and mention-safe — the prop's own
                    // leaf id can coincide with a residue name only when
                    // the prop text IS the bare residue var, and bare-Var
                    // transcriptions never fail, so that case can't reach
                    // here. The derived 0 is guaranteed correct by the
                    // caller's bit; the bridge backstops even a buggy bit.
                    self.prop_deeps.push((
                        leaf_id,
                        format!("({}.RawExp.Var {} ({}.TypData.TyBool))", NS, leaf_id, NS),
                    ));
                    Ok(())
                }
            }
        }
    }

    /// F4 guard for poison-check sites whose prop has NO SST source to
    /// transcribe (the Call.post FHyp props + dest-let eq props — callee
    /// ensures / ret-eq values built LExpr-side): the reference derives
    /// 0 for the (absent) entry, so a REAL mention would silently
    /// mis-derive — reject instead. Zero population corpus-wide (the 68
    /// vendored Call.post FHyp literals all carry bit 0); a subject that
    /// trips this is a new coverage arm, not a silent pass.
    fn guard_no_poison(&self, hp: u64, what: &str) -> Sr<()> {
        if hp == 1 {
            Err(format!("prop-deep-uncoverable: {} mentions a residue (no SST source for the deep)", what))
        } else {
            Ok(())
        }
    }

    /// The hoisted-let equation pair `(eq-name leaf, eq-prop leaf)` for
    /// binder `lname` with rendered rhs `rhs`. The eq prop is
    /// production's `LExpr::eq(LExpr::var(chosen), v2)` pp'd through the
    /// SAME pp path (byte-for-byte the binder's equation hypothesis);
    /// the eq name is `_h_{x}_hoist1` — production's `fresh()` first
    /// try. (Taken-name freshening — a user binder literally named
    /// `_h_{x}_hoist1` — is the documented `hoist-name-collision`
    /// census caveat, not mirrored: the bridge honest-fails on it.)
    fn eq_leaves(&mut self, lname: &crate::lean_name::LeanName, rhs: &LExpr) -> (u64, u64) {
        let ep = self.leaves.intern(pp_expr(&LExpr::eq(LExpr::var(lname.clone()), rhs.clone())));
        let en = self.text_leaf(&format!("_h_{}_hoist1", lname.as_str()));
        (en, ep)
    }

    // (The A2-era `wrap_guard` / `user-closer-hoistless` reject is
    // RETIRED by R1: the seeded `FUserCloser` marker force-wraps every
    // goal of a wrap-mode fn reference-side, pre-let goals included.)

    /// A5 (bootstrap-77): mirror of production's `walk_let` value-position
    /// FORK on the default Return route (`Wp::Let(ret, e, Done(ens))`).
    /// Recursively:
    /// * peels single-binder `Bind(Let)` chains into assign statements —
    ///   walk_let's Bind arm renders binder RHSs OPAQUE (no fork inside
    ///   them: the probe_if_assign evidence, b77 E1);
    /// * FORKS a peeled `ExpX::If`: the branch hyps are the BARE
    ///   ctx-rendered cond / ¬cond — walk_let pushes them UNMARKED
    ///   (probe_if_ret leaf evidence), unlike the statement-If's
    ///   span-marked Branch hyps — with the positive side N2-upgraded to
    ///   `IfCtor` ctor frames when the shared detector fires;
    /// * terminates in the shared `Ret(ens, RetBind)` builder
    ///   (`ret_terminal`) — each branch value coerces with its OWN typ
    ///   to the declared ret typ, exactly like the plain path.
    /// Hyp ordinals / branch state mirror the statement-If arm: the
    /// branch hyp is `_h_hoist_{save+1}` in BOTH branches; Return
    /// diverges, so no continuation consumes the post-fork counter.
    fn ret_fork(&mut self, e: &Exp) -> Sr<String> {
        if let ExpX::Bind(bnd, body) = &e.x {
            if let Some((lname, rhs, inner)) =
                crate::sst_to_lean::match_single_let_bind(bnd, body)
            {
                let rhs_lx_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked(rhs)
                    .map_err(|reason| format!("leaf-render: {}", reason))?;
                let rhs_lx = self.apply_renames(&rhs_lx_raw);
                let rhs_leaf = self.leaves.intern(pp_expr(&rhs_lx));
                let dest = self.text_leaf(lname.as_str());
                let term = self.assign_let_term(
                    &lname,
                    dest,
                    Some(rhs.typ.clone()),
                    &rhs_lx,
                    rhs_leaf,
                    rhs,
                )?;
                let rest = self.ret_fork(inner)?;
                return Ok(format!("({}.StmData.Seq {} {})", NS, box_(&term), box_(&rest)));
            }
        }
        let peeled = crate::sst_to_lean::peel_value_position(e);
        let ExpX::If(cond, then_e, else_e) = &peeled.x else {
            return self.ret_terminal(e);
        };
        // The branch cond, ctx-rendered + renamed, UNMARKED (walk_let's
        // `c_ast` — binder-aware ctx WITH the let-binder env).
        let c_lx_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
            cond,
            &self.render_ctx().with_let_binder_typs(&self.let_binder_typs),
        )
        .map_err(|reason| format!("leaf-render: {}", reason))?;
        let c_lx = self.apply_renames(&c_lx_raw);
        let cp = self.hyp_poison(&c_lx);
        if cp == 1 {
            self.mark_poison_forced()?;
        }
        let nc = self.leaves.intern(pp_expr(&LExpr::not(c_lx.clone())));
        // F4: register the ¬cond prop's deep (the eq prop's deep is
        // registered in `ctor_fork_frames`; the plain-If path's `c`
        // registers below).
        self.register_prop_deep(nc, cond, cp)?;
        let save = self.hyp_ordinal;
        let bstate = self.branch_state();
        let hyp_name = format!("_h_hoist_{}", save + 1);
        match self.ctor_fork_frames(cond)? {
            Some((pos_binders, eq_prop)) => {
                let eq_name = self.text_leaf(&hyp_name);
                self.hyp_ordinal = save + 1;
                let t = self.ret_fork(then_e)?;
                self.restore_branch(bstate.clone());
                self.hyp_ordinal = save + 1;
                let el = self.ret_fork(else_e)?;
                self.restore_branch(bstate);
                self.hyp_ordinal = save;
                Ok(format!(
                    "({}.StmData.IfCtor {} {} {} {} {} {} {})",
                    NS,
                    box_(&pos_binders),
                    eq_name,
                    eq_prop,
                    eq_name,
                    nc,
                    box_(&t),
                    box_(&el)
                ))
            }
            None => {
                let c = self.leaves.intern(pp_expr(&c_lx));
                // F4: register the cond prop's deep.
                self.register_prop_deep(c, cond, cp)?;
                let cn = self.text_leaf(&hyp_name);
                self.hyp_ordinal = save + 1;
                let t = self.ret_fork(then_e)?;
                self.restore_branch(bstate.clone());
                self.hyp_ordinal = save + 1;
                let el = self.ret_fork(else_e)?;
                self.restore_branch(bstate);
                self.hyp_ordinal = save;
                Ok(format!(
                    "({}.StmData.If {} {} {} {} {} {})",
                    NS, c, cn, nc, cn, box_(&t), box_(&el)
                ))
            }
        }
    }

    /// N2 ctor-frame mirror (bootstrap-77 A5): the shared DETECTOR
    /// (`branch_isvariant_of` — single-source like `closer_is_default`)
    /// plus the same krate-data gates as production's
    /// `branch_ctor_frames` (positive test on a plain-Var scrutinee, dt
    /// in map, multi-variant, typ args exposed); the FRAMES — field
    /// binders `(scrut_field : T)` + the span-marked ctor equation
    /// `scrut(.deref…) = Dt.Variant fs` — are assembled HERE. Returns
    /// `(pos_binders BinderList term, eq-prop leaf, eq-poison)`; `None`
    /// keeps the plain cond hyp, exactly like production. NOTE the N2
    /// gate's default-closer condition is implied at the call site (the
    /// fork only runs on the default Return route).
    fn ctor_fork_frames(&mut self, cond: &Exp) -> Sr<Option<(String, u64)>> {
        let Some(p) = crate::sst_to_lean::branch_isvariant_of(cond, true) else {
            return Ok(None);
        };
        if !p.positive {
            return Ok(None);
        }
        let Some(dx) = self.dt_map.get(p.dt_path).copied() else {
            return Ok(None);
        };
        let short = crate::to_lean_type::short_name(p.dt_path);
        if dx.variants.len() == 1 && dx.variants[0].name.as_str() == short {
            return Ok(None);
        }
        let Some(variant) = dx.variants.iter().find(|v| v.name.as_str() == p.variant) else {
            return Ok(None);
        };
        // Instantiated typ args + wrapper derefs (production's loop,
        // byte-for-byte the same wrapper classification).
        let mut sty: &Typ = p.scrut_typ;
        let mut derefs: usize = 0;
        let typ_args = loop {
            match &**sty {
                vir::ast::TypX::Decorate(deco, _, t) => {
                    use vir::ast::TypDecoration::*;
                    match deco {
                        Ref | MutRef | Box | Rc | Arc => derefs += 1,
                        Ghost | Tracked | Never | ConstPtr => {}
                    }
                    sty = t;
                }
                vir::ast::TypX::Boxed(t) => sty = t,
                vir::ast::TypX::Datatype(vir::ast::Dt::Path(sp), args, _) if sp == p.dt_path => {
                    break args;
                }
                _ => return Ok(None),
            }
        };
        let dt_lean = crate::to_lean_type::lean_name(p.dt_path);
        let var_san = crate::to_lean_type::sanitize(p.variant);
        let mut entries: Vec<(u64, u64)> = Vec::new();
        let mut args: Vec<LExpr> = Vec::new();
        for f in variant.fields.iter() {
            let fty = vir::sst_util::subst_typ_for_datatype(&dx.typ_params, typ_args, &f.a.0);
            let fname = format!(
                "{}_{}",
                p.scrut.as_str(),
                crate::to_lean_fn::field_name(&f.name)
            );
            let id = self.text_leaf(&fname);
            let ty = self.typ_leaf(&fty);
            entries.push((id, ty));
            args.push(LExpr::var_synthetic(fname));
        }
        let ctor = LExpr::var_synthetic(format!("{}.{}", dt_lean, var_san));
        let app = if args.is_empty() { ctor } else { LExpr::app(ctor, args) };
        let lhs_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
            p.inner,
            &self.render_ctx().with_let_binder_typs(&self.let_binder_typs),
        )
        .map_err(|reason| format!("leaf-render: {}", reason))?;
        let mut lhs = self.apply_renames(&lhs_raw);
        for _ in 0..derefs {
            lhs = LExpr::field_proj(lhs, "deref");
        }
        let eq_inner = LExpr::eq(lhs, app);
        let eq_poison = self.hyp_poison(&eq_inner);
        if eq_poison == 1 {
            self.mark_poison_forced()?;
        }
        let loc = crate::obligation_naming::format_rust_loc(&cond.span);
        let marked = LExpr::span_mark(
            loc,
            Some(cond.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            eq_inner,
        );
        let eq_prop = self.leaves.intern(pp_expr(&marked));
        // F4: register the eq prop's deep — MENTION-EQUIVALENT via the
        // scrutinee transcription: the synthetic side (ctor name, fresh
        // field names) carries no residue names by construction, so the
        // eq prop's residue mentions are exactly the scrutinee's.
        self.register_prop_deep(eq_prop, p.inner, eq_poison)?;
        let pos_binders = self.binder_list(&entries);
        Ok(Some((pos_binders, eq_prop)))
    }

    /// The N1-hoist classification for a plain let statement
    /// (bootstrap-74 slice 2), mirroring `hoist_all`'s per-let decision:
    /// typ known + non-Bool → `AssignH` (the hoisted binder pair); Bool
    /// → `AssignR` (residue — registering the name so later hyps poison
    /// on it); typ-less → plain `Assign` (production's `hoist_all` None
    /// case, forces wrap). F4 (bootstrap-80 stage 2): the poison collapse
    /// moved REFERENCE-SIDE — a typed let emits `AssignH` even when its
    /// equation mentions a residue name; the eq prop's deep is
    /// registered and refWp derives the lossless collapse to plain FLet
    /// (wrap mode discards the hoist payload either way, so the emitted
    /// goals are unchanged). The poison check still runs here: it drives
    /// `mark_flet_forced` (production's forced-state mirror, consulted
    /// at branch joins) and the era-1 bit cross-check.
    /// Shared by the `Assign` arm (typ from `local_typs`) and the
    /// Return-arm Bnd-let peel (typ from the binder's rhs exp).
    fn assign_let_term(
        &mut self,
        lname: &crate::lean_name::LeanName,
        dest: u64,
        typ: Option<Typ>,
        rhs_lx: &LExpr,
        rhs_leaf: u64,
        rhs_exp: &Exp,
    ) -> Sr<String> {
        // R1 (bootstrap-77): wrap-mode fns no longer collapse lets to
        // plain — classification is HONEST everywhere and the seeded
        // `FUserCloser` marker (FnCtxData.closer_default = 0) trips
        // refWp's wrap gate instead. Wrap rendering of FLetH/FLetR is
        // `Let(x, v)`, identical to FLet, so emitted goals are
        // unchanged. (Freshening stays off in wrap fns via the init
        // `mark_flet_forced` — production renames only inside
        // `hoist_all`.)
        match typ {
            Some(typ) if matches!(&*typ, vir::ast::TypX::Bool) => {
                self.residue_names.push(lname.as_str().to_string());
                Ok(format!("({}.StmData.AssignR {} {})", NS, dest, rhs_leaf))
            }
            Some(typ) => {
                let eq_lx = LExpr::eq(LExpr::var(lname.clone()), rhs_lx.clone());
                let hp = self.hyp_poison(&eq_lx);
                if hp == 1 {
                    // Poison forces wrap from here (production collapses;
                    // the reference DERIVES the collapse from the deep).
                    self.mark_flet_forced()?;
                }
                let ty_leaf = self.typ_leaf(&typ);
                let (en, ep) = self.eq_leaves(lname, rhs_lx);
                // F4: register the eq prop's deep (the RHS transcription
                // is mention-equivalent — the dest binder is a non-Bool
                // let, never a residue name).
                self.register_prop_deep(ep, rhs_exp, hp)?;
                Ok(format!(
                    "({}.StmData.AssignH {} {} {} {} {})",
                    NS, dest, ty_leaf, rhs_leaf, en, ep
                ))
            }
            None => {
                // Typ-less let: plain FLet — forces wrap from here.
                self.mark_flet_forced()?;
                Ok(format!("({}.StmData.Assign {} {})", NS, dest, rhs_leaf))
            }
        }
    }

    /// The dest-let frame for a call (bootstrap-74 slice 2 N1
    /// classification), shared by both post paths: FLetH when the dest
    /// typ is known non-Bool; FLetR for a Bool dest (registering the
    /// residue name for later poison checks); plain FLet when the typ
    /// is Bool-irrelevant-but-missing. F4: the poison collapse moved
    /// reference-side (always-FLetH, as `assign_let_term`) — but the eq
    /// value here is the callee's ret-eq RHS, built LExpr-side with NO
    /// SST source to transcribe, so no deep can be registered: a real
    /// residue mention rejects loud (`guard_no_poison`; zero population
    /// corpus-wide). `tail` is the already-built inner frame.
    fn dest_let_frame(        &mut self,
        dest_id: u64,
        dest_name: &crate::lean_name::LeanName,
        dest_typ: &Typ,
        dv_lx_raw: &LExpr,
        tail: String,
    ) -> Sr<String> {
        let dv_lx = &self.apply_renames(dv_lx_raw);
        let dv = self.leaves.intern(pp_expr(dv_lx));
        // R1 (bootstrap-77): honest classification in wrap-mode fns too
        // (see `assign_let_term` — the seeded FUserCloser carries the
        // wrap force; FLetH/FLetR wrap-render as Let, goals unchanged).
        if matches!(&**dest_typ, vir::ast::TypX::Bool) {
            self.residue_names.push(dest_name.as_str().to_string());
            Ok(format!("({}.FrameList.FLetR {} {} {})", NS, dest_id, dv, box_(&tail)))
        } else {
            let eq_lx = LExpr::eq(LExpr::var(dest_name.clone()), dv_lx.clone());
            let hp = self.hyp_poison(&eq_lx);
            if hp == 1 {
                self.mark_flet_forced()?;
            }
            self.guard_no_poison(hp, "call dest-let eq prop")?;
            let ty_leaf = self.typ_leaf(dest_typ);
            let (en, ep) = self.eq_leaves(dest_name, dv_lx);
            Ok(format!(
                "({}.FrameList.FLetH {} {} {} {} {} {})",
                NS, dest_id, ty_leaf, dv, en, ep, box_(&tail)
            ))
        }
    }

    // ── W6c: raw-SST → RawExp transcription (the reference-side input) ─
    // The NEW, INDEPENDENT input (DESIGN-W6-stageB.md §4.2, D2 diversity):
    // mirror the RAW SST expression tree to `lib.RawExp` text, reading each
    // node's `typ` for the `TypData` tags — NOT rendered through
    // production's `to_lean_sst_expr`. The landed `render_exp` (W6b) then
    // re-derives the cast/coercion decisions from those tags in Lean, so a
    // production emitter that inserts an `Int.toNat` inconsistently
    // (Friction 2) diverges → the bridge `decide` fails.
    //
    // Atom-id consistency invariant (load-bearing): atoms (var reads, call
    // heads) intern their rendered text via `self.leaves`, EXACTLY as the
    // production `LExpr→ExprData` side will — so `expr_eq(prod, ref)` matches
    // on atoms and the diversity is confined to the structural cast layer.
    //
    // Not yet called by the emit path (that is W6d); `#[allow(dead_code)]`
    // keeps it verdict-neutral until then.

    /// Map a source `Typ` to `lib.TypData` mirror text. The cast decision
    /// only needs the Int-vs-Nat distinction; datatypes/params collapse to
    /// `TyNamed`, `&T`/`&mut T` to `TyRef`. Peels SMT `Decorate`/`Boxed`
    /// wrappers. `TyNamed`/`TyRef` ids reuse `typ_leaf`'s interning so the
    /// reference and production sides agree by construction. Fails loud
    /// (census tag `typ-<k>`) on shapes stage B does not yet mirror.
    fn typ_data(&mut self, typ: &Typ) -> Sr<String> {
        match &**typ {
            TypX::Bool => Ok(format!("{}.TypData.TyBool", NS)),
            // Mirror `to_lean_type`'s int-range mapping EXACTLY
            // (to_lean_type.rs:92-110): `nat`, `usize`, and `char` lower to
            // Lean `Nat`; unbounded `int`, signed fixed-width, `isize`, AND
            // unsigned fixed-width (`u8`..`u64`) lower to `Int`. The
            // datatype-field bridge over the tgt slice (bootstrap-37, real
            // `RuntimeSymbol { Gen(usize), Inv(usize) }`) caught this: the
            // emitter renders a `usize` field as `(val0 : Nat)`, so production's
            // transcriber reads `TyNat`; the reference MUST agree, not `TyInt`.
            TypX::Int(IntRange::Nat | IntRange::USize | IntRange::Char) => {
                Ok(format!("{}.TypData.TyNat", NS))
            }
            TypX::Int(_) => Ok(format!("{}.TypData.TyInt", NS)),
            TypX::Datatype(..) => {
                let id = self.typ_leaf(typ);
                Ok(format!("({}.TypData.TyNamed {})", NS, id))
            }
            // `&T` / `&mut T` present the pointee, tagged `TyRef` so the
            // reference `deref_type` (W6b) resolves the `.deref`.
            TypX::Decorate(TypDecoration::Ref, _, inner)
            | TypX::Decorate(TypDecoration::MutRef, _, inner) => {
                let id = self.typ_leaf(inner);
                Ok(format!("({}.TypData.TyRef {})", NS, id))
            }
            // Other decorations (Box/Rc/Arc/Ghost/Tracked/…) are SMT-only
            // wrappers — peel and recurse.
            TypX::Decorate(_, _, inner) => self.typ_data(inner),
            TypX::Boxed(inner) => self.typ_data(inner),
            _ => Err(format!("typ-{}", typ_construct_tag(typ))),
        }
    }

    /// `ExpX → lib.RawExp` for the cast class (Var/Lit/Clip/BinOp/App). The
    /// 2nd `BinOp` slot is the op's RESULT type (`e.typ`), which is what
    /// `render_exp` reads to decide operand coercion. Everything outside the
    /// class fails loud (`raw-<k>`).
    fn raw_exp(&mut self, e: &Exp) -> Sr<String> {
        match &e.x {
            // G0 (W6d.2b) — peel the SMT coercion wrappers FIRST. `Box(_)` /
            // `Unbox(_)` are semantic-identity `int↔Boxed` casts the solver
            // needs but that carry no expression content (the W6d.0 dump found
            // them wrapping every boxed value — spec-fn args, datatype args,
            // field results, tuple elements). Recurse into the inner and drop
            // the wrapper, exactly as `typ_data` peels `Boxed`/`Decorate` at
            // the type level; the inner node's own `typ` drives its tag. This
            // is the #1 unlock — without it even `tri (1)` (a `Box[Nat] 1`
            // arg) fails, so nothing downstream is reachable.
            ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => self.raw_exp(inner),
            ExpX::Const(Constant::Int(n)) => {
                let ty = self.typ_data(&e.typ)?;
                Ok(format!("({}.RawExp.Lit {} {})", NS, n, paren(&ty)))
            }
            // G1 (W6d.2b) — a source bool literal (`ensures true`, find_square).
            // `RawExp::LitBool` carries the nat encoding (0/1), NOT a `bool`:
            // the tactus Lean backend renders a spec `bool` as `Prop`, whose
            // equality sticks `decide` (W6d.1a design deviation 1). `render_exp`
            // passes it straight through to `ExprData::LitBool`.
            ExpX::Const(Constant::Bool(b)) => {
                Ok(format!("({}.RawExp.LitBool {})", NS, if *b { 1 } else { 0 }))
            }
            // G7 (W6d.2b) — a pre-state param read (`VarAt(vid, Pre)`), which
            // ensures/decrease leaves use instead of a plain `Var`. Production's
            // renderer collapses `VarAt(x, _)` to a bare `Var(x)`
            // (`vir_expr_to_ast`), so mirror it identically to the `Var` arm:
            // intern the SAME `binder_id`, read `e.typ`. (For an `&mut` param an
            // ensures `VarAt` renders `x_at_pre_tactus`, not bare `x` — a
            // divergence the W6d.2b emit-gate catches by falling both sides back
            // to atom; the fixture's coverable fns take non-mut params, where
            // the bare-`x` collapse matches.)
            ExpX::Var(vid) | ExpX::VarAt(vid, _) => {
                // Shadow mirror (Round D): a variable captured by a
                // shadowed let resolves to its freshened name
                // (`i_hoist1`), exactly as `rename_frame_vars` renames
                // the LExpr-side renders — the deep reference RawExp
                // must carry the same id the production goal leaf
                // deepens to.
                let name = crate::lean_name::LeanName::from_var_ident(vid);
                let fresh = self.rename_env.get(name.as_str()).cloned();
                let id = match fresh {
                    Some(fresh) => self.text_leaf(fresh.as_str()),
                    None => self.text_leaf(name.as_str()),
                };
                let ty = self.typ_data(&e.typ)?;
                Ok(format!("({}.RawExp.Var {} {})", NS, id, paren(&ty)))
            }
            // Explicit `as` cast: the clip's RANGE is the target type the
            // reference materializes against (`type_of (Clip target _) =
            // target`). `Nat` range → `TyNat`, uN/int range → `TyInt`.
            ExpX::Unary(UnaryOp::Clip { range, .. }, inner) => {
                let target = match range {
                    IntRange::Nat => format!("{}.TypData.TyNat", NS),
                    _ => format!("{}.TypData.TyInt", NS),
                };
                let sub = self.raw_exp(inner)?;
                Ok(format!("({}.RawExp.Clip {} {})", NS, paren(&target), box_raw(&sub)))
            }
            ExpX::Binary(op, l, r) => {
                let opc = binop_opcode(op)?;
                let ty = self.typ_data(&e.typ)?;
                let ls = self.raw_exp(l)?;
                let rs = self.raw_exp(r)?;
                // B1 (bootstrap-48): emit the operands BARE. The structural-binop
                // `&`-deref min-balance (production `to_lean_sst_expr.rs:1157-1161`)
                // now lives in the TCB reference `render_exp`'s BinOp arm
                // (`tactus-core/lib.rs`), which derives the peel INDEPENDENTLY from
                // the operand TypData — so the bridge checks production's
                // deref-count against the reference's rather than sharing
                // `count_ref_decorations` (B2's common-mode gap). Reverts 6ea3030.
                Ok(format!(
                    "({}.RawExp.BinOp {} {} {} {})",
                    NS,
                    opc,
                    paren(&ty),
                    box_raw(&ls),
                    box_raw(&rs)
                ))
            }
            // Single-argument spec-fn application (`lib.tri (…)`). The fn id
            // interns the callee name text (atom-id bucket); ret ty = the
            // call node's typ; the 4th slot = the callee's EXPECTED param
            // typ (A7 — see `expected_arg_typ`).
            //
            // W7 (bootstrap-34): multi-arg (`args.len() >= 2`) widens to
            // `RawExp::CallN(fn, ret, RawList[args])` — the flat-arg spine
            // `render_exp` maps to `ExprData::AppN` (lib.rs L944).
            // A7 (bootstrap-80 F3): each RawList element pairs the arg with
            // its expected param typ. The W7-era claim that Verus
            // materializes EVERY call-arg coercion as a `Clip` inside the
            // arg is falsified by vec_read (`Int.ofNat i` on the
            // `Seq.index` arg appears in production with NO Clip in the
            // SST — production inserts it at render time from the callee
            // signature), which is exactly why the expected typs must be
            // carried. `len == 0` (a genuine no-dummy nullary call) stays
            // census-rejected as before.
            ExpX::Call(CallFun::Fun(fun, _), typs, args) => {
                let fn_id = self.call_fun_id(fun);
                let ret = self.typ_data(&e.typ)?;
                if args.len() == 1 {
                    let arg = &args[0];
                    // A7 (bootstrap-80 F3): the 4th slot is the callee's
                    // EXPECTED param typ (was: the arg's own typ) — what
                    // `reconcile_arg` reconciles against reference-side.
                    let arg_ty = self.expected_arg_typ(fun, typs, 0, arg)?;
                    let arg_s = self.raw_exp(arg)?;
                    Ok(format!(
                        "({}.RawExp.Call {} {} {} {})",
                        NS,
                        fn_id,
                        paren(&ret),
                        box_raw(&arg_s),
                        paren(&arg_ty)
                    ))
                } else if args.len() >= 2 {
                    let mut arg_list = format!("{}.RawList.Nil", NS);
                    for (i, arg) in args.iter().enumerate().rev() {
                        let expected = self.expected_arg_typ(fun, typs, i, arg)?;
                        let a = self.raw_exp(arg)?;
                        arg_list = format!(
                            "({}.RawList.Cons {} {} {})",
                            NS,
                            box_raw(&a),
                            paren(&expected),
                            box_raw(&arg_list)
                        );
                    }
                    Ok(format!(
                        "({}.RawExp.CallN {} {} {})",
                        NS,
                        fn_id,
                        paren(&ret),
                        box_raw(&arg_list)
                    ))
                } else {
                    Err("raw-call-arity".to_string())
                }
            }
            // G6 (W6d.2b) — an unsigned-overflow refinement `HasType(U(n))(e)`,
            // which production EXPANDS to `0 ≤ e ∧ e < 2^n`
            // (`type_bound_predicate`). Carry the width `n` as a first-class
            // `RawExp::HasType`; `render_exp` reproduces that exact expansion
            // (option (i), Danielle 2026-07-14) so the width stays observable
            // and the `2^n` bound is re-derived INDEPENDENTLY of production's
            // `two_pow_lit` (a divergence surfaces as a bridge mismatch, never a
            // silent pass). Only fixed-width UNSIGNED ranges are carried;
            // signed / usize / char / int / nat refinements fail loud
            // (`hastype-range`) — none appear in the fixture's coverable set.
            ExpX::UnaryOpr(UnaryOpr::HasType(t), inner) => {
                let width = uint_bound_width(t)?;
                let sub = self.raw_exp(inner)?;
                Ok(format!("({}.RawExp.HasType {} {})", NS, width, box_raw(&sub)))
            }
            // G3 (W6d.2b) — struct/tuple field projection. Reuse production's
            // exact accessor-naming (`field_access_name`) so the reference field
            // id and the goal-side `FieldProj.field` (which production ALSO
            // derived via `field_access_name`) intern the IDENTICAL string — the
            // atom-id consistency invariant holds by construction, rather than
            // by re-deriving the tuple 1-indexed shift here. A 1-tuple's field-0
            // access is the identity (production emits no projection); mirror the
            // bare base. The field's own `typ` is the result type
            // (`type_of (Field …) = fty`). NB: a `&`-decorated base needs the
            // `.deref` chain production inserts (`apply_deref_chain`) that this
            // arm does NOT reproduce — such a base DIVERGES and the W6d.2b
            // emit-gate keeps it fail-loud (never silent-passes).
            ExpX::UnaryOpr(UnaryOpr::Field(fop), inner) => {
                let base = self.raw_exp(inner)?;
                match crate::expr_shared::field_access_name(fop) {
                    None => Ok(base),
                    Some(accessor) => {
                        let fid = self.text_leaf(&accessor);
                        let fty = self.typ_data(&e.typ)?;
                        Ok(format!(
                            "({}.RawExp.Field {} {} {})",
                            NS,
                            fid,
                            paren(&fty),
                            box_raw(&base)
                        ))
                    }
                }
            }
            // W7c (bootstrap-28) — first-class `if c { t } else { e }` in a
            // spec-fn BODY (`tri(n) = if n == 0 { 0 } else { … }`, the Ite
            // exemplar). The If node's OWN type (`e.typ`) is the branch RESULT
            // type carried in the leading slot — `render_exp` reads it to decide
            // per-branch Int→Nat coercion (Friction-2, exactly like a `BinOp`'s
            // result-type slot). Cond is bool (never coerced); both branches
            // transcribe recursively. Distinct from `lift_if_raw`, which peels a
            // RETURN-VALUE if into per-branch implications — this is the body if.
            ExpX::If(cond, then_e, else_e) => {
                let ty = self.typ_data(&e.typ)?;
                let c = self.raw_exp(cond)?;
                let t = self.raw_exp(then_e)?;
                let el = self.raw_exp(else_e)?;
                Ok(format!(
                    "({}.RawExp.Ite {} {} {} {})",
                    NS,
                    paren(&ty),
                    box_raw(&c),
                    box_raw(&t),
                    box_raw(&el)
                ))
            }
            _ => Err(format!("raw-{}", exp_construct_tag(&e.x))),
        }
    }

    // ── G4/W6e: the value-if-lift recompute (reference side) ──────────
    // Production lifts a fall-through `if` in a return VALUE into each
    // ensures leaf, so the Return goal is a branch-folded implication
    // `c → (let r := (let m := v; …); ens0 ∧ ens1)` per branch, split off
    // the top `And` (`lift_if_value_coerced` → `emit_done_or_split`). The
    // frozen `refWp` only bridges if the reference SST carries THOSE
    // obligations, not the ensures-split `Ret([ens…], RetLet)` the plain
    // path emits. `lift_if_raw` mirrors `lift_if_value_coerced` at the
    // `RawExp`-text level (the "recompute-not-copy" TCB step), so a
    // divergence is a bridge mismatch, never a silent pass. Pinned end-to-
    // end through the real `ref_wp`/`render_exp` by probe14 (bootstrap-24).

    /// The lifted return-obligation tree, before the top-level `And` split.
    /// A small typed mirror of `lift_if_value_coerced`'s output so the split
    /// is structural (not text-parsing). `Leaf`/`Implies` carry pre-rendered
    /// `RawExp` text; `And` only ever appears at nodes the split descends.
    fn lift_if_raw(&mut self, e: &Exp, wraps: &[RawLet]) -> Sr<LiftedRaw> {
        let peeled = crate::sst_to_lean::peel_value_position(e);
        match &peeled.x {
            // `if c { t } else { e }` → `(c → lift t) ∧ (¬c → lift e)`.
            // Both branches are return values → same `wraps`.
            ExpX::If(cond, then_e, else_e) => {
                let c = self.raw_exp(cond)?;
                let then_t = self.lift_if_raw(then_e, wraps)?;
                let else_t = self.lift_if_raw(else_e, wraps)?;
                let not_c = format!("({}.RawExp.Not {})", NS, box_raw(&c));
                Ok(LiftedRaw::And(
                    Box::new(LiftedRaw::Implies(c, Box::new(then_t))),
                    Box::new(LiftedRaw::Implies(not_c, Box::new(else_t))),
                ))
            }
            // `let name := rhs; body` — lift `rhs`, re-threading `body` as the
            // innermost wrap. Only the fixture's shape (single binder, body
            // rendered as-is) is mirrored; a nested let-chain rhs or a
            // multi-binder let fails loud (fall-through to the honest-failing
            // plain path), never a silent pass.
            ExpX::Bind(bnd, body) => {
                let Some((name, rhs, inner_body)) =
                    crate::sst_to_lean::match_single_let_bind(bnd, body)
                else {
                    return Err("liftraw-bind".to_string());
                };
                let peeled_inner = crate::sst_to_lean::peel_value_position(inner_body);
                if matches!(&peeled_inner.x, ExpX::Bind(b, _) if matches!(&b.x, BndX::Let(_))) {
                    return Err("liftraw-letchain".to_string());
                }
                let name_id = self.text_leaf(name.as_str());
                let body_raw = self.raw_exp(inner_body)?;
                let mut new_wraps = wraps.to_vec();
                new_wraps.push(RawLet { name: name_id, body: body_raw });
                self.lift_if_raw(rhs, &new_wraps)
            }
            // Leaf return value → fold the wrap-stack around it (innermost
            // first), ending in the conjoined-ensures tail carried by the
            // outermost `let r` wrap. Production renders the ORIGINAL `e` here
            // (`sst_exp_to_ast_checked`); `raw_exp` peels its own transparent
            // wrappers, so a bare-var branch value renders identically.
            _ => {
                let v = self.raw_exp(e)?;
                Ok(LiftedRaw::Leaf(apply_raw_wraps(wraps, &v)))
            }
        }
    }

    /// Interned id of a callee spec-fn's rendered name (atom-id bucket, so a
    /// production `App{head: Var(name)}` interns the SAME id). Production
    /// renders the head as `LeanName::from_path(&fun.path)`
    /// (`to_lean_sst_expr.rs:1229`), so match that exactly.
    fn call_fun_id(&mut self, fun: &vir::ast::Fun) -> u64 {
        let name = crate::lean_name::LeanName::from_path(&fun.path);
        self.text_leaf(name.as_str())
    }

    /// A7 (bootstrap-80 F3): the callee's param typ at position `idx`,
    /// instantiated with the call's typ args — read through production's
    /// OWN `fn_param_typs` logic (`expr_shared::fn_param_typs_of`, single
    /// source) over the SAME fn_map the render ctx consults, then mirrored
    /// to `TypData`. This is DATA transcription (the same VIR the
    /// production renderer reads), not a decision: `reconcile_arg` derives
    /// the coercion reference-side from the (actual, expected) pair.
    /// Fallbacks, both mirroring production's own behavior:
    ///   * unknown signature → the arg's own typ (production's
    ///     `into_slot(&a.typ)` fallback = passthrough);
    ///   * a param typ the mirror cannot transcribe (`typ_data` failure =
    ///     an inner-type `coerce_lexpr` also passes through) → the arg's
    ///     own typ.
    fn expected_arg_typ(
        &mut self,
        fun: &vir::ast::Fun,
        typs: &[vir::ast::Typ],
        idx: usize,
        arg: &vir::sst::Exp,
    ) -> Sr<String> {
        let expected = crate::expr_shared::fn_param_typs_of(&self.fn_map, fun, typs)
            .and_then(|ts| ts.get(idx).cloned());
        match expected {
            Some(t) => match self.typ_data(&t) {
                Ok(td) => Ok(td),
                Err(_) => self.typ_data(&arg.typ),
            },
            None => self.typ_data(&arg.typ),
        }
    }

    /// VIR-surface sibling of [`Self::expected_arg_typ`] for the def-body
    /// transcriber (`raw_vir_exp`): same lookup, VIR arg node.
    fn expected_arg_typ_vir(
        &mut self,
        fun: &vir::ast::Fun,
        typs: &[vir::ast::Typ],
        idx: usize,
        arg: &vir::ast::Expr,
    ) -> Sr<String> {
        let expected = crate::expr_shared::fn_param_typs_of(&self.fn_map, fun, typs)
            .and_then(|ts| ts.get(idx).cloned());
        match expected {
            Some(t) => match self.typ_data(&t) {
                Ok(td) => Ok(td),
                Err(_) => self.typ_data(&arg.typ),
            },
            None => self.typ_data(&arg.typ),
        }
    }

    // ── W7c-ref (bootstrap-29): VIR `ExprX` → RawExp (the DEF-BODY reference) ─
    //
    // Spec-fn *bodies* live on the VIR `vir::ast::Expr` surface, NOT the SST
    // `vir::sst::Exp` surface `raw_exp` above operates on. The distinction is
    // load-bearing: a spec-fn `match` body is a native `ExprX::Match` on VIR
    // (production emits `match t with | …` from it, verified against the
    // emitted fixture def `lib.tree_head`), but AST→SST lowering DESUGARS that
    // same match into `if t.isVariant …` (which is why the SST `raw_exp` never
    // needed a Match arm, and why the obligation-side `head_exec` goal reads
    // `if tmp__.deref.isLeaf …`). So the def-body REFERENCE transcriber must
    // read VIR, keeping `Match`/`Ite` first-class (DESIGN-W7-defslayer.md §2 —
    // the independent second lowering that gives the bridge teeth).
    //
    // Reuses the RawExp emitter infra + `typ_data`/`binop_opcode`/`text_leaf`/
    // `binder_id`/`call_fun_id` (all surface-agnostic — `typ_data` already
    // takes a `&Typ`). Mirrors the production VIR reading in
    // `to_lean_expr::expr_to_node`. Census-gated, fail-loud (`rawvir-<k>`) on
    // shapes outside the fixture-reachable set (`sq`/`tri`/`tree_head`);
    // quantifiers + multi-arg `Call` are tgt-slice-only and stay fail-loud
    // until a tgt def forces them. `#[allow(dead_code)]` until W7d wires the
    // def-body entry point — verdict-neutral by construction (a NEW function,
    // never on the emit path).

    /// `vir::ast::Expr` (`ExprX`) → `lib.RawExp` text for the def-body class.
    /// Structurally parallel to `raw_exp` (SST), but on the VIR surface where
    /// `If`/`Match`/`Ctor`/`Quant` are first-class. Result-type slots
    /// (`Ite`/`MatchR` `ty`) carry `e.typ` so `render_exp` re-derives per-branch
    /// / per-arm Int→Nat coercion (the Friction-2 site).
    #[allow(dead_code)]
    fn raw_vir_exp(&mut self, e: &VirExpr) -> Sr<String> {
        match &e.x {
            // Peel SMT `Box`/`Unbox` coercion wrappers first (as SST `raw_exp`
            // does) — semantic-identity casts with no expression content; the
            // inner node's own `typ` drives its tag.
            ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), inner) => self.raw_vir_exp(inner),
            ExprX::Const(Constant::Int(n)) => {
                let ty = self.typ_data(&e.typ)?;
                Ok(format!("({}.RawExp.Lit {} {})", NS, n, paren(&ty)))
            }
            ExprX::Const(Constant::Bool(b)) => {
                Ok(format!("({}.RawExp.LitBool {})", NS, if *b { 1 } else { 0 }))
            }
            // A var read: bare `Var`, a `VarAt` (production collapses to bare
            // `Var`), or a `ReadPlace(Local)` (the new-mut-refs var-read shape
            // production also collapses to the var — `expr_to_node`'s ReadPlace
            // + Var arms both resolve to `Var(from_var_ident(v))`). All intern
            // the SAME `binder_id` + read `e.typ`, matching production's atom.
            ExprX::Var(vid) | ExprX::VarAt(vid, _) => {
                let id = self.binder_id(vid);
                let ty = self.typ_data(&e.typ)?;
                Ok(format!("({}.RawExp.Var {} {})", NS, id, paren(&ty)))
            }
            ExprX::ReadPlace(place, _) => match &place.x {
                PlaceX::Local(vid) => {
                    let id = self.binder_id(vid);
                    let ty = self.typ_data(&e.typ)?;
                    Ok(format!("({}.RawExp.Var {} {})", NS, id, paren(&ty)))
                }
                _ => Err("rawvir-readplace-nonlocal".to_string()),
            },
            // Explicit `as` cast — the clip RANGE is the materialization target
            // (identical to SST `raw_exp`).
            ExprX::Unary(UnaryOp::Clip { range, .. }, inner) => {
                let target = match range {
                    IntRange::Nat => format!("{}.TypData.TyNat", NS),
                    _ => format!("{}.TypData.TyInt", NS),
                };
                let sub = self.raw_vir_exp(inner)?;
                Ok(format!("({}.RawExp.Clip {} {})", NS, paren(&target), box_raw(&sub)))
            }
            ExprX::Binary(op, l, r) => {
                let opc = binop_opcode(op)?;
                let ty = self.typ_data(&e.typ)?;
                let ls = self.raw_vir_exp(l)?;
                let rs = self.raw_vir_exp(r)?;
                Ok(format!(
                    "({}.RawExp.BinOp {} {} {} {})",
                    NS,
                    opc,
                    paren(&ty),
                    box_raw(&ls),
                    box_raw(&rs)
                ))
            }
            // Single-argument spec-fn application (`lib.tri (…)`, `lib.sum_tree
            // (…)`). VIR's callee is `CallTarget::Fun` (not SST's `CallFun`);
            // extract the `Fun` for the atom-id bucket. Non-`Fun` targets fail
            // loud (tgt-slice-only — §7 Q3).
            //
            // W7 (bootstrap-34): multi-arg (`args.len() >= 2`) widens to
            // `RawExp::CallN` exactly as the SST `raw_exp` arm above — same
            // flat, no-per-arg-`TypData` spine, co-designed so `def_eq` agrees
            // with the production `AppN` by construction. `len == 0` stays
            // census-rejected.
            ExprX::Call(CallTarget::Fun(_, fun, typs, ..), args, _post) => {
                let fn_id = self.call_fun_id(fun);
                let ret = self.typ_data(&e.typ)?;
                if args.len() == 1 {
                    let arg = &args[0];
                    // A7 (bootstrap-80 F3): 4th slot = the callee's
                    // EXPECTED param typ (same as the SST arm).
                    let arg_ty = self.expected_arg_typ_vir(fun, typs, 0, arg)?;
                    let arg_s = self.raw_vir_exp(arg)?;
                    Ok(format!(
                        "({}.RawExp.Call {} {} {} {})",
                        NS,
                        fn_id,
                        paren(&ret),
                        box_raw(&arg_s),
                        paren(&arg_ty)
                    ))
                } else if args.len() >= 2 {
                    let mut arg_list = format!("{}.RawList.Nil", NS);
                    for (i, arg) in args.iter().enumerate().rev() {
                        let expected = self.expected_arg_typ_vir(fun, typs, i, arg)?;
                        let a = self.raw_vir_exp(arg)?;
                        arg_list = format!(
                            "({}.RawList.Cons {} {} {})",
                            NS,
                            box_raw(&a),
                            paren(&expected),
                            box_raw(&arg_list)
                        );
                    }
                    Ok(format!(
                        "({}.RawExp.CallN {} {} {})",
                        NS,
                        fn_id,
                        paren(&ret),
                        box_raw(&arg_list)
                    ))
                } else {
                    Err("rawvir-call-arity".to_string())
                }
            }
            // Struct/tuple field projection — reuse production's accessor naming
            // (`field_access_name`) so the field id interns identically (as SST
            // `raw_exp`). A field with no accessor (1-tuple field-0) is the
            // identity — mirror the bare base.
            ExprX::UnaryOpr(UnaryOpr::Field(fop), inner) => {
                let base = self.raw_vir_exp(inner)?;
                match crate::expr_shared::field_access_name(fop) {
                    None => Ok(base),
                    Some(accessor) => {
                        let fid = self.text_leaf(&accessor);
                        let fty = self.typ_data(&e.typ)?;
                        Ok(format!(
                            "({}.RawExp.Field {} {} {})",
                            NS,
                            fid,
                            paren(&fty),
                            box_raw(&base)
                        ))
                    }
                }
            }
            // First-class `if c { t } else { e }` in a def body (the `tri`
            // exemplar). VIR `If`'s else is OPTIONAL; an else-less `if` can't be
            // a value-position def body → fail loud. `e.typ` is the branch
            // RESULT type carried for per-branch coercion (like SST `raw_exp`).
            ExprX::If(cond, then_e, Some(else_e)) => {
                let ty = self.typ_data(&e.typ)?;
                let c = self.raw_vir_exp(cond)?;
                let t = self.raw_vir_exp(then_e)?;
                let el = self.raw_vir_exp(else_e)?;
                Ok(format!(
                    "({}.RawExp.Ite {} {} {} {})",
                    NS,
                    paren(&ty),
                    box_raw(&c),
                    box_raw(&t),
                    box_raw(&el)
                ))
            }
            // `match scrut { Ctor pats => body, … }` — THE fixture-forced arm
            // (`tree_head`/`sum_tree`). The scrutinee is a `Place` (production
            // renders it via `render_place_with_derefs`). Guards are DROPPED by
            // production (`expr_to_node`'s Match arm ignores `arm.guard`); mirror
            // that only for a trivially-true guard — a real guard would be a
            // silent production mistranslation the bridge must not paper over,
            // so fail loud. Arms fold right-to-left into the inlined
            // `RawArmList::Cons(ctor_id, binder_ids, body, tail)` (W7b froze the
            // inlined list, not a named `MatchArm`). `e.typ` is the arm-body
            // result type (flows into `render_arms` for per-arm coercion).
            ExprX::Match(place, arms) => {
                let scrut = self.raw_vir_place(place)?;
                let ty = self.typ_data(&e.typ)?;
                let mut arm_list = format!("{}.RawArmList.Nil", NS);
                for arm in arms.iter().rev() {
                    if !matches!(&arm.x.guard.x, ExprX::Const(Constant::Bool(true))) {
                        return Err("rawvir-match-guard".to_string());
                    }
                    let (ctor_id, binds) = self.pattern_ctor_binds(&arm.x.pattern.x)?;
                    let body = self.raw_vir_exp(&arm.x.body)?;
                    arm_list = format!(
                        "({}.RawArmList.Cons {} {} {} {})",
                        NS,
                        ctor_id,
                        paren(&binds),
                        box_raw(&body),
                        box_raw(&arm_list)
                    );
                }
                Ok(format!(
                    "({}.RawExp.MatchR {} {} {})",
                    NS,
                    box_raw(&scrut),
                    box_raw(&arm_list),
                    paren(&ty)
                ))
            }
            // W7c (bootstrap-29): a quantifier body `∀/∃ (b : bty), body`. VIR
            // carries ALL binders of one quantifier in a single `Quant`; nest
            // them right-to-left into single-binder `ForallR`/`ExistsR` (the
            // W7b vocab is single-binder) — `∀ x y, P` ⟶ `ForallR x (ForallR y
            // P)`. Production's `ExprNode::Forall{binders, body}` arm does the
            // IDENTICAL right-to-left nesting over the SAME `q_binders.iter()`
            // order (`vir_var_binders_to_ast` preserves it), so `def_eq` agrees
            // by construction. Binder-NAME ids intern via `binder_id` (=
            // production's `from_var_ident`); binder-TYPE via `typ_data` (the
            // same `TypData` production's `ltyp_to_typdata` recognizer
            // re-derives from the rendered binder type). An empty binder list
            // can't occur for a real quantifier → fail loud; a binder type
            // `typ_data` can't map (e.g. a bare type param) fails loud there.
            ExprX::Quant(quant, q_binders, body) => {
                if q_binders.is_empty() {
                    return Err("rawvir-quant-empty".to_string());
                }
                let ctor = match quant.quant {
                    air::ast::Quant::Forall => "ForallR",
                    air::ast::Quant::Exists => "ExistsR",
                };
                let mut acc = self.raw_vir_exp(body)?;
                for b in q_binders.iter().rev() {
                    let bid = self.binder_id(&b.name);
                    let bty = self.typ_data(&b.a)?;
                    acc = format!(
                        "({}.RawExp.{} {} {} {})",
                        NS,
                        ctor,
                        bid,
                        paren(&bty),
                        box_raw(&acc)
                    );
                }
                Ok(acc)
            }
            // A spec-fn body arrives wrapped in the frontend's statement-less
            // block-expr `Block([], Some(tail))` (the `tri`/`sq`/`tree_head`
            // shape — the hand-built unit tests fed a bare tail, so this was
            // first hit only on the live emit path, W7d). Production's
            // `block_to_node` peels an empty block straight to
            // `expr_to_ast(tail)` (to_lean_expr.rs:1107-1113), so the DefData
            // body is the lowered tail; peel identically here so the reference
            // `ExprData` matches. A block WITH statements (a `let` in a spec
            // fn) lowers production-side to `let`/`match` nesting — outside the
            // fixture-reachable set, and mirroring it needs the reference `Let`
            // arm production's `block_to_node` builds — so fail loud until a def
            // forces it (falls through to `rawvir-block`).
            ExprX::Block(stmts, Some(tail)) if stmts.is_empty() => self.raw_vir_exp(tail),
            _ => Err(format!("rawvir-{}", vir_expr_construct_tag(&e.x))),
        }
    }

    /// A match SCRUTINEE `Place` → `RawExp` text. Only `Local(v)` (a bare var
    /// read, the fixture's `match t`) is mirrored; deeper places (Field/
    /// DerefMut/Index/Temporary) fail loud — production renders them via
    /// `render_place_with_derefs`, an as-yet-unmirrored surface.
    #[allow(dead_code)]
    fn raw_vir_place(&mut self, place: &Place) -> Sr<String> {
        match &place.x {
            PlaceX::Local(vid) => {
                let id = self.binder_id(vid);
                let ty = self.typ_data(&place.typ)?;
                Ok(format!("({}.RawExp.Var {} {})", NS, id, paren(&ty)))
            }
            _ => Err("rawvir-place".to_string()),
        }
    }

    /// A ctor match pattern `Ctor(dt, variant, fields)` → its `(ctor_id,
    /// BinderIdList-text)`. The ctor id interns the SAME string production's
    /// `pattern_to_ast` builds — via the shared `ctor_pattern_name` helper, so
    /// the two can't drift (§7 Q1). Field binder ids are the positional pattern
    /// bindings, in the SAME `fields.iter()` order production reads them (both
    /// walk the identical VIR `fields` Vec → identical order, no sort). Tuple
    /// ctors (no named Lean ctor) fail loud.
    #[allow(dead_code)]
    fn pattern_ctor_binds(&mut self, pat: &PatternX) -> Sr<(u64, String)> {
        match pat {
            PatternX::Constructor(dt, variant, fields) => {
                let name = crate::to_lean_expr::ctor_pattern_name(dt, variant)
                    .ok_or_else(|| "rawvir-match-tuplector".to_string())?;
                let ctor_id = self.text_leaf(&name);
                let mut binds = format!("{}.BinderIdList.Nil", NS);
                for f in fields.iter().rev() {
                    let bid = self.pattern_binder_id(&f.a.x)?;
                    binds = format!("({}.BinderIdList.Cons {} {})", NS, bid, box_raw(&binds));
                }
                Ok((ctor_id, binds))
            }
            _ => Err("rawvir-arm-pat".to_string()),
        }
    }

    /// A ctor-FIELD pattern → its bound-var binder id. Only a `Var` binding (the
    /// fixture's `Leaf(v)` / `Node(_l, _r)` — `_l`/`_r` are named vars, not bare
    /// `_`) is mirrored, interning the SAME `binder_id` production's
    /// `pattern_to_ast` emits as `LPattern::Var(from_var_ident(name))`.
    /// Wildcards / nested / ref-ergonomics patterns fail loud (none appear in a
    /// by-value def-body match).
    #[allow(dead_code)]
    fn pattern_binder_id(&mut self, pat: &PatternX) -> Sr<u64> {
        match pat {
            PatternX::Var(binding) => Ok(self.binder_id(&binding.name)),
            _ => Err("rawvir-field-pat".to_string()),
        }
    }

    // ── W7c (bootstrap-30): VIR def HEADER → RawDef (the def-header reference) ─
    //
    // `raw_vir_exp` covers only the body; a full `RawDef` also needs the header
    // (name + typed value params + ret type). Transcribed straight from the VIR
    // `FunctionX` fields, DECOMPOSED into args (name / typ_params / value params
    // / ret / body) so this + its tests stay independent of the 33-field
    // `FunctionX`. W7d passes `&f.name`, `&f.typ_params`, `&f.params`,
    // `&f.ret.x.typ`, and the body `Expr`.
    //
    // Id agreement with the production `ldef_to_defdata`, all by construction:
    //   - name — `call_fun_id` interns `LeanName::from_path(&fun.path)`, which
    //     IS production's `def.name = lean_name(&f.name.path)` (`from_path`
    //     delegates to `lean_name`); same string ⟹ same interned id.
    //   - value params — read the SAME `params` sequence (no `%` filter, no
    //     sort) production's `fn_binders_without_bound_hyps` reads; per-param id
    //     via `binder_id` (= `from_var_ident`, production's binder name), type
    //     via `typ_data`. The value-param TYPE agreement is the SAME
    //     `typ_data`↔`ltyp_to_typdata` inversion the quantifier binder types use
    //     (production's `param_binder_typ(non-mut)` IS `typ_to_expr`, which
    //     `ltyp_to_typdata` inverts to the identical `TypData`).
    //
    // POLY GATE (tgt-slice deferral, like AppN): production's `Def.binders`
    // PREPENDS type-param (`{A : Type}`) + trait-bound binders before the value
    // params, but `TypData` has no universe/`Type` variant to mirror a
    // `{A : Type}` binder — so a polymorphic def would give production leading
    // params the reference can't match. Fail loud on non-empty `typ_params`
    // (needs a `TypData::TySort` addition — a batched `tactus-core` turn); the
    // fixture defs (`tri`/`tree_head`) are monomorphic so the gate never trips.
    // The REFERENCE is the gate: W7d bridges only when BOTH sides succeed, so a
    // polymorphic def's extra production params are never observed.
    //
    // `#[allow(dead_code)]` until W7d wires the def entry point —
    // verdict-neutral by construction (a NEW fn, never on the emit path; no
    // `tactus-core` edit).

    /// VIR def header + body → `lib.RawDef` text. Fails loud (`rawvir-def-<k>`)
    /// on polymorphic / `&mut`-param / uncovered-body-constructor defs.
    #[allow(dead_code)]
    fn raw_vir_def(
        &mut self,
        name: &vir::ast::Fun,
        typ_params: &vir::ast::Idents,
        params: &vir::ast::Params,
        ret: &Typ,
        body: &VirExpr,
    ) -> Sr<String> {
        if !typ_params.is_empty() {
            return Err("rawvir-def-poly".to_string());
        }
        // Intern FORWARD (declaration order, like the FnCtxData seed walk) so
        // the ids are stable + predictable; format the `ParamList` reversed.
        let name_id = self.call_fun_id(name);
        let mut params_txt: Vec<(u64, String)> = Vec::new();
        for p in params.iter() {
            // `&mut` spec params don't occur (spec fns are pure); defer rather
            // than risk the `typ_data`/`param_binder_typ` mut-wrap agreement.
            if p.x.is_mut {
                return Err("rawvir-def-mutparam".to_string());
            }
            let pid = self.binder_id(&p.x.name);
            let pty = self.typ_data(&p.x.typ)?;
            params_txt.push((pid, pty));
        }
        let ret_ty = self.typ_data(ret)?;
        let body_raw = self.raw_vir_exp(body)?;
        let mut plist = format!("{}.ParamList.Nil", NS);
        for (pid, pty) in params_txt.iter().rev() {
            plist = format!("{}.ParamList.Cons {} {} {}", NS, pid, paren(pty), box_(&plist));
        }
        Ok(format!(
            "({}.RawDef.mk {} {} {} {})",
            NS,
            name_id,
            paren(&plist),
            paren(&ret_ty),
            paren(&body_raw)
        ))
    }

    // ── W7c (bootstrap-31): VIR datatype decl → RawDt (the datatype reference) ─
    //
    // The datatype `inductive` decls the def bodies (and obligation goals) are
    // stated over — trust-inventory row 4's other half. A datatype has no body to
    // lower, so this transcription's teeth are the VIR-vs-LExpr diversity: the
    // reference reads the VIR `DatatypeX` (name / variant names / positional field
    // TYPES) while production `ldt_to_dtdata` reads the already-rendered
    // `lean_ast::Datatype`; a wrong-transcribed ctor name or field type makes
    // `dt_eq` (tactus-core) `decide` to 0.
    //
    // THE BOX SUBTLETY (W7a §7 Q4, the one real technical wrinkle): a datatype
    // FIELD keeps its `Box` — the recursion in `Node(Box<Tree>, Box<Tree>)` goes
    // THROUGH the box, so `typ_data`'s SMT-wrapper peel (which drops Box for a
    // value-position expression type) is WRONG here. Production agrees: it renders
    // the field via `typ_to_expr`, which maps `Box<T>` to `Tactus.Box T` (NOT
    // peeled). So the field-type transcriber `dt_field_typ_data` maps
    // `Decorate(Box) → TyBox(pointee id)` — distinct from `TyRef` (Box≠Ref;
    // conflating them would mask a field-kind bug) — and the production
    // `ldt_field_typdata` recognizes `Tactus.Box T` back to the SAME `TyBox` id.
    //
    // Id agreement with production `ldt_to_dtdata`, all by construction:
    //   - datatype name — `lean_name(path)`, = production's `Datatype.name`.
    //   - ctor name — `sanitize(&v.name)`, EXACTLY production's
    //     `Variant { name: sanitize(&v.name) }` (to_lean_fn's datatype builder).
    //   - field types — positional (no accessor names, W7a §7 Q4), read in the
    //     SAME `.iter()` order (no sort either side); `TyBox` pointee /
    //     `TyNamed`/`TyInt` ids reuse `typ_leaf`'s interning off the SHARED
    //     `self.leaves` table, which production's `typ_to_expr`-rendered field
    //     `Expr` re-interns to the same id (the `ltyp_to_typdata` invariant).
    //
    // GATES (fail loud, census `rawvir-dt-<k>`, tgt-slice deferrals):
    //   - polymorphic (`typ_params` non-empty) — like `raw_vir_def`, production's
    //     `(A : Type)` params have no `TypData` mirror; fixture `Tree` is monomorphic.
    //   - single-variant struct (variant name == type short name) — production
    //     emits a `structure` (ctor = type name, no variant list), a genuinely
    //     different transcription; `Tree` is a multi-variant `inductive`.
    //   - tuple datatype (`Dt::Tuple`) — synthetic, no user decl to certify.
    // The REFERENCE is the gate: W7d bridges only when both sides succeed.
    //
    // `#[allow(dead_code)]` until W7d wires the datatype entry point —
    // verdict-neutral by construction (a NEW fn, never on the emit path; NO
    // `tactus-core` edit — `RawDt`/`DtData`/`CtorList`/`TypList` all landed in W7b).

    /// A datatype FIELD type → `lib.TypData` text, KEEPING the `Box` (unlike
    /// `typ_data`, which peels it as an SMT wrapper). `Box<T> → TyBox(pointee)`;
    /// everything else delegates to `typ_data` (Int/Bool/Nat/named/`&T`).
    /// KNOWN GAP (documented, not unsound): a non-Box owned wrapper field
    /// (`Rc<T>`/`Arc<T>`) would delegate to `typ_data`, which PEELS it to the
    /// pointee while production keeps `Tactus.Rc T` — a peel-vs-keep mismatch that
    /// SPURIOUSLY fails the bridge (uncertifiable, never wrongly passes). None
    /// appear in the fixture (`Tree` fields are `u64` / `Box<Tree>`).
    #[allow(dead_code)]
    fn dt_field_typ_data(&mut self, typ: &Typ) -> Sr<String> {
        match &**typ {
            TypX::Decorate(TypDecoration::Box, _, inner) => {
                let id = self.typ_leaf(inner);
                Ok(format!("({}.TypData.TyBox {})", NS, id))
            }
            _ => self.typ_data(typ),
        }
    }

    /// VIR datatype decl → `lib.RawDt` text. Fails loud (`rawvir-dt-<k>`) on
    /// polymorphic / single-variant-struct / tuple datatypes.
    #[allow(dead_code)]
    fn raw_vir_dt(
        &mut self,
        name: &Dt,
        typ_params: &vir::ast::TypPositives,
        variants: &vir::ast::Variants,
    ) -> Sr<String> {
        if !typ_params.is_empty() {
            return Err("rawvir-dt-poly".to_string());
        }
        let path = match name {
            Dt::Path(p) => p,
            Dt::Tuple(_) => return Err("rawvir-dt-tuple".to_string()),
        };
        // Production emits a single-variant struct whose variant name == the type
        // short name as a `structure` (ctor = type name, no variant list) — a
        // different transcription. Fail loud; `Tree` is multi-variant.
        if variants.len() == 1 && variants[0].name.as_str() == short_name(path) {
            return Err("rawvir-dt-struct".to_string());
        }
        // Intern FORWARD (name, then per-variant ctor names + field-type ids in
        // declaration order) so the ids are stable + predictable; format both the
        // `CtorList` and each `TypList` reversed (the boxed self-recursive tails).
        let name_id = self.text_leaf(&lean_name(path));
        let mut ctors_txt: Vec<(u64, String)> = Vec::new();
        for v in variants.iter() {
            let ctor_id = self.text_leaf(&sanitize(&v.name));
            let mut flds_txt: Vec<String> = Vec::new();
            for f in v.fields.iter() {
                flds_txt.push(self.dt_field_typ_data(&f.a.0)?);
            }
            let mut tylist = format!("{}.TypList.Nil", NS);
            for ft in flds_txt.iter().rev() {
                tylist = format!("{}.TypList.Cons {} {}", NS, paren(ft), box_(&tylist));
            }
            ctors_txt.push((ctor_id, tylist));
        }
        let mut clist = format!("{}.CtorList.Nil", NS);
        for (cid, tylist) in ctors_txt.iter().rev() {
            clist = format!("{}.CtorList.Cons {} {} {}", NS, cid, paren(tylist), box_(&clist));
        }
        Ok(format!("({}.RawDt.mk {} {})", NS, name_id, paren(&clist)))
    }

    // ── W6c: production `lean_ast::Expr` → ExprData (the prod-side input) ─
    // The BORING 1:1 side (DESIGN-W6-stageB.md §4.2 / bootstrap-22). The
    // production renderer (`to_lean_sst_expr`) has ALREADY materialized every
    // cast decision into the `lean_ast::Expr` tree — `Int.toNat`/`Int.ofNat`
    // as `App { head: Var("Int.toNat"), .. }`, `*p` as `FieldProj { field:
    // "deref" }`. We transcribe that tree VERBATIM into `lib.ExprData` text;
    // no cast decision is re-made here (that is `render_exp`'s job on the ref
    // side). The bridge then `decide`s `expr_eq(prod, render_exp(ref))`, so a
    // production emitter that inserts an `Int.toNat` inconsistently (Friction
    // 2) diverges from the reference's uniform derivation → the `decide`
    // fails.
    //
    // Atom-id consistency (the load-bearing invariant): terminal atoms — var
    // reads, spec-fn App heads, non-`deref` field names — intern their
    // rendered text via `self.leaves`, the SAME table the reference
    // `raw_exp`/`render_exp` atoms use. A `Var(name)` here interns
    // `name.as_str()`; the reference `RawExp::Var` interned
    // `LeanName::from_var_ident(vid).as_str()` — and production renders a var
    // read as exactly `Var(LeanName::from_var_ident(vid))`, so the two ids are
    // equal by construction. Likewise an App head `Var(LeanName::from_path(&
    // fun.path))` matches the reference `call_fun_id`. So `expr_eq` matches on
    // atoms and the diversity is confined to the structural cast layer.
    //
    // Structural binops map through `lean_binop_opcode` into the SAME
    // canonical opcode table `raw_exp` maps into (`binop_opcode`); the
    // `binop_opcode_alignment` test pins that the two tables agree through
    // `binop_to_ast`. Everything outside the cast class fails loud (`ed-<k>`),
    // same census discipline as the stm walk. Not yet called by the emit path
    // (that is W6d); `#[allow(dead_code)]` keeps it verdict-neutral until then.

    /// `lean_ast::Expr → lib.ExprData` mirror text. Recognizes the cast class
    /// (Var/Lit/`Int.toNat`|`Int.ofNat` Cast/App/BinOp) plus the unambiguous
    /// FieldProj/SpanMark structural nodes; fails loud (`ed-<k>`) on anything
    /// else.
    fn lexpr_to_exprdata(&mut self, e: &LExpr) -> Sr<String> {
        match &e.node {
            // Terminal atom: a var read or a bare spec-fn / type name. Interns
            // its rendered text (atom-id bucket) — matches the reference side.
            ExprNode::Var(name) => {
                let id = self.text_leaf(name.as_str());
                Ok(format!("({}.ExprData.Atom {})", NS, id))
            }
            // Integer literal. `ExprNode::Lit` holds the pre-formatted decimal
            // (or hex) text; the mirror `Lit` carries an `int`. Emitted raw,
            // exactly as the reference `raw_exp` emits the BigInt — a negative
            // literal would need parenthesizing on BOTH sides (none arises in
            // the cast class; shared open item).
            ExprNode::Lit(s) => Ok(format!("({}.ExprData.Lit {})", NS, s)),
            // G1 (W6d.2b) — a bool-literal leaf (`ensures true`, find_square; or
            // a builder-synthesized `∧ False` decrease disjunct). Maps to
            // `ExprData::LitBool` with the 0/1 nat encoding, matching the
            // reference `RawExp::LitBool` after `render_exp` (which passes it
            // straight through). The nat encoding (not a `bool`) is required —
            // a spec `bool` renders as Lean `Prop` and sticks `decide`
            // (W6d.1a design deviation 1).
            ExprNode::LitBool(b) => {
                Ok(format!("({}.ExprData.LitBool {})", NS, if *b { 1 } else { 0 }))
            }
            // Materialized `as`-cast: production emits `Int.toNat x` /
            // `Int.ofNat x` as a single-arg App with a literal head (see
            // `coerce_lexpr` / `wrap_int_measure`). Map to the `Cast` node the
            // reference `render_exp` DERIVES — so the two agree only when the
            // production cast decision matched the reference's uniform one.
            ExprNode::App { head, args }
                if is_var_named(head, "Int.toNat") && args.len() == 1 =>
            {
                let sub = self.lexpr_to_exprdata(&args[0])?;
                Ok(format!(
                    "({}.ExprData.Cast {}.CastKind.IntToNat {})",
                    NS,
                    NS,
                    box_ed(&sub)
                ))
            }
            ExprNode::App { head, args }
                if is_var_named(head, "Int.ofNat") && args.len() == 1 =>
            {
                let sub = self.lexpr_to_exprdata(&args[0])?;
                Ok(format!(
                    "({}.ExprData.Cast {}.CastKind.NatToInt {})",
                    NS,
                    NS,
                    box_ed(&sub)
                ))
            }
            // A7 (bootstrap-80 F3): the `Tactus.Ref.mk e` / `Tactus.Box.mk e`
            // wrapper constructions `coerce_lexpr` inserts — first-class
            // nodes, NOT an `App` on an interned fn-name leaf: the
            // reference DERIVES these via `reconcile_arg` and cannot mint
            // the per-cert interned id. Head may carry a typ-arg layer
            // (same peeling as the generic App arms).
            ExprNode::App { head, args }
                if args.len() == 1 && app_head_fn_name(head) == Some("Tactus.Ref.mk") =>
            {
                let sub = self.lexpr_to_exprdata(&args[0])?;
                Ok(format!("({}.ExprData.RefMk {})", NS, box_ed(&sub)))
            }
            ExprNode::App { head, args }
                if args.len() == 1 && app_head_fn_name(head) == Some("Tactus.Box.mk") =>
            {
                let sub = self.lexpr_to_exprdata(&args[0])?;
                Ok(format!("({}.ExprData.BoxMk {})", NS, box_ed(&sub)))
            }
            // Single-value-arg spec-fn application (`lib.tri x`). The head is a
            // bare `Var(name)` (nullary-generic callee, e.g. `tri`) or a
            // type-arg application `App { head: Var(name), .. }` — production
            // applies the fn name to its type args FIRST, then to the value
            // arg. The reference `RawExp::Call` carries NO type args (it drops
            // `_typs`), so drop them here too and key on the fn name; the two
            // sides stay identical on generic calls (both mirror only the head
            // + value arg). Multi-value-arg / non-Var-head apps fail loud.
            ExprNode::App { head, args } if args.len() == 1 => match app_head_fn_name(head) {
                Some(name) => {
                    let fn_id = self.text_leaf(name);
                    let arg = self.lexpr_to_exprdata(&args[0])?;
                    Ok(format!("({}.ExprData.App {} {})", NS, fn_id, box_ed(&arg)))
                }
                None => Err("ed-app-head".to_string()),
            },
            // W7 (bootstrap-34): multi-value-arg spec-fn application. Production
            // builds these FLAT — `LExpr::app(head, [v0..vn])` with the type-arg
            // layer already folded into `head` (`to_lean_sst_expr.rs` L1228 +
            // `to_lean_expr` twin), so `app_head_fn_name` peels the SAME
            // `Var(name)` / `App{Var(name), typeargs}` head shapes as the
            // single-arg arm. Map to `ExprData::AppN(fn, ExprList[args])`, the
            // production twin of the reference `RawExp::CallN` (which
            // `render_exp` lowers to the identical `AppN` — lib.rs L944), keying
            // the fn id on the SAME interned name so `def_eq` agrees by
            // construction. A non-fn head (e.g. a `CallLambda` closure) fails
            // loud, mirroring the reference (whose `raw_*_exp` has no
            // `CallLambda` arm → census-rejects). `LExpr::app` collapses empty
            // args to the head, so this arm only sees `len >= 2`.
            ExprNode::App { head, args } => match app_head_fn_name(head) {
                Some(name) => {
                    let fn_id = self.text_leaf(name);
                    let mut arg_list = format!("{}.ExprList.Nil", NS);
                    for arg in args.iter().rev() {
                        let a = self.lexpr_to_exprdata(arg)?;
                        arg_list =
                            format!("({}.ExprList.Cons {} {})", NS, box_ed(&a), box_ed(&arg_list));
                    }
                    Ok(format!("({}.ExprData.AppN {} {})", NS, fn_id, box_ed(&arg_list)))
                }
                None => Err("ed-app-head".to_string()),
            },
            // Structural binary op — reconcile into the canonical opcode table.
            ExprNode::BinOp { op, lhs, rhs } => {
                let opc = lean_binop_opcode(op)?;
                let l = self.lexpr_to_exprdata(lhs)?;
                let r = self.lexpr_to_exprdata(rhs)?;
                Ok(format!(
                    "({}.ExprData.BinOp {} {} {})",
                    NS,
                    opc,
                    box_ed(&l),
                    box_ed(&r)
                ))
            }
            // Field projection. A `.deref` (the `&`-param dereference
            // production inserts) uses the reference `deref_field()` id (0);
            // any real field name interns its text (atom-id bucket), matching
            // a reference FieldProj on the same field.
            ExprNode::FieldProj { expr, field } => {
                let sub = self.lexpr_to_exprdata(expr)?;
                let fid = if field == "deref" { 0 } else { self.text_leaf(field) };
                Ok(format!("({}.ExprData.FieldProj {} {})", NS, box_ed(&sub), fid))
            }
            // Source-span obligation wrapper. Production's `rust_loc` string is
            // `format_rust_loc(&span)`; the reference wraps the obligation in
            // `RawExp::Span` at the `oblig_leaf` level (W6d) with the SAME
            // interned loc, so the two SpanMark loc ids agree.
            ExprNode::SpanMark { rust_loc, inner, .. } => {
                let loc = self.text_leaf(rust_loc);
                let sub = self.lexpr_to_exprdata(inner)?;
                Ok(format!("({}.ExprData.SpanMark {} {})", NS, loc, box_ed(&sub)))
            }
            // Type ascription `(e : T)` (bootstrap-74 slice 2 §3c) —
            // ERASED. The reference `RawExp` mirror never carries
            // ascriptions (SST typ erasure; `render_exp` re-derives the
            // coercions from the `TypData` tags), so the goal side drops
            // them too — both sides then agree on the un-annotated shape
            // (vec_read's `((lib.view.View.view (v : Tactus.Ref …)) :
            // lib.seq.Seq Int)` → the plain view AppN + Atom). This is
            // stage-A-safe: ascription TYPE content is leaf rendering
            // (stage B), not the assembly the bridge certifies.
            ExprNode::TypeAnnot { expr, .. } => self.lexpr_to_exprdata(expr),
            // G4 (W6e) — the value-if-lift's `let`/`¬` scaffolding. Production
            // folds a fall-through `if` INTO each ensures leaf as a
            // branch-folded implication `c → (let r := (let m := v; …); ens)`
            // (`lift_if_value_coerced`); the goal leaf carries `Let` and `Not`
            // nodes that the cast-class arms above never produce. Transcribe
            // them structurally — the binder NAME interns its rendered text
            // (atom-id bucket), the SAME text the reference `RawExp::Let` binder
            // interns (`sanitize(ret)` for the return `r`, `from_var_ident` for
            // an inner let `m`), so the two ids agree by construction. `render_exp`
            // passes both nodes straight through (no coercion at the Let/Not
            // node), so the bridge `decide`s the sub-expressions.
            ExprNode::Let { name, value, body } => {
                let nid = self.text_leaf(name.as_str());
                let v = self.lexpr_to_exprdata(value)?;
                let b = self.lexpr_to_exprdata(body)?;
                Ok(format!(
                    "({}.ExprData.Let {} {} {})",
                    NS,
                    nid,
                    box_ed(&v),
                    box_ed(&b)
                ))
            }
            ExprNode::UnOp { op: LUnOp::Not, arg } => {
                let sub = self.lexpr_to_exprdata(arg)?;
                Ok(format!("({}.ExprData.Not {})", NS, box_ed(&sub)))
            }
            // W7c (bootstrap-28) — first-class if in a spec-fn body. Production
            // materializes any branch coercion INTO the branch (an `Int.toNat`
            // App the `Cast` arm above already transcribes), so this arm is a
            // structural VERBATIM transcription — cond/then/else recurse — and
            // matches the reference `render_exp`'s `Ite(cond, then, else)`. An
            // else-less `if` cannot occupy value position in a body → fail loud
            // (`ed-if-noelse`, census-tracked, never a silent pass).
            ExprNode::If { cond, then_, else_: Some(else_) } => {
                let c = self.lexpr_to_exprdata(cond)?;
                let t = self.lexpr_to_exprdata(then_)?;
                let e2 = self.lexpr_to_exprdata(else_)?;
                Ok(format!(
                    "({}.ExprData.Ite {} {} {})",
                    NS,
                    box_ed(&c),
                    box_ed(&t),
                    box_ed(&e2)
                ))
            }
            ExprNode::If { else_: None, .. } => Err("ed-if-noelse".to_string()),
            // W7c (bootstrap-28) — first-class `match` in a spec-fn body (the
            // `tree_head`/`sum_tree` exemplars). Production's `vir_expr_to_ast`
            // Match arm PRESERVES `match` in def bodies (unlike the obligation
            // surface, where AST→SST desugars it to `if`-chains) — so this
            // ExprNode only reaches the def-body entry point (W7d), never an
            // obligation goal → the arm is verdict-neutral on the current emit
            // path (the surface-fork finding, bootstrap-28). Structural twin of
            // the reference `raw_vir_exp` `MatchR` arm: scrutinee recurses, arms
            // fold right-to-left into the inlined `ArmList::Cons(ctor_id,
            // binder_ids, body, tail)` (W7b froze the inlined list). Ctor/binder
            // ids intern identically to the reference by construction — see
            // `lpattern_ctor_binds` (§7 Q1). Arm-body coercion lives on the
            // reference `render_arms` side; production transcribes each body
            // VERBATIM (any branch cast is already an `Int.toNat` App the `Cast`
            // arm handles), matching `render_arms`' per-arm materialization.
            // Guards are ABSENT from `lean_ast::MatchArm` (production's
            // `expr_to_node` dropped them upstream); the reference side is the
            // one that fails loud on a non-trivial guard, so there is nothing to
            // re-check here.
            ExprNode::Match { scrutinee, arms } => {
                let scrut = self.lexpr_to_exprdata(scrutinee)?;
                let mut arm_list = format!("{}.ArmList.Nil", NS);
                for arm in arms.iter().rev() {
                    let (ctor_id, binds) = self.lpattern_ctor_binds(&arm.pattern)?;
                    let body = self.lexpr_to_exprdata(&arm.body)?;
                    arm_list = format!(
                        "({}.ArmList.Cons {} {} {} {})",
                        NS,
                        ctor_id,
                        paren(&binds),
                        box_ed(&body),
                        box_ed(&arm_list)
                    );
                }
                Ok(format!(
                    "({}.ExprData.Match {} {})",
                    NS,
                    box_ed(&scrut),
                    box_(&arm_list)
                ))
            }
            // W7c (bootstrap-29): a quantifier body `∀/∃ (b : bty), body`.
            // Production emits ONE `Forall`/`Exists` node carrying ALL binders;
            // `lquant_to_exprdata` nests them right-to-left into single-binder
            // `ExprData::Forall`/`Exists` — the identical nesting the reference
            // `raw_vir_exp` `Quant` arm does over the SAME binder order, so
            // `def_eq` agrees by construction. Verdict-neutral on the current
            // emit path: a goal leaf reaches `lexpr_to_exprdata` only via the
            // `deep_ids` gate (`goal_data`), which requires the reference SST
            // `raw_exp` to have gone deep on the matching obligation — but
            // `raw_exp` has NO quantifier arm (`ExpX::Bind` ⟶ `raw-bind`
            // fail-loud), so a quantifier-cored obligation never enters
            // `deep_ids`. The arm activates only at the W7d def-body entry point.
            ExprNode::Forall { binders, body } => self.lquant_to_exprdata("Forall", binders, body),
            ExprNode::Exists { binders, body } => self.lquant_to_exprdata("Exists", binders, body),
            _ => Err(format!("ed-{}", lexpr_construct_tag(&e.node))),
        }
    }

    /// A production match-arm pattern (`lean_ast::Pattern`) → its `(ctor_id,
    /// BinderIdList-text)` — the production twin of the reference
    /// `pattern_ctor_binds`. The ctor id interns the SAME string the reference
    /// does: production's `pattern_to_ast` built `Pattern::Ctor { name }` from
    /// the SHARED `ctor_pattern_name(dt, variant)` helper, and the reference
    /// interns `text_leaf(ctor_pattern_name(..))`, so `text_leaf(name)` here is
    /// equal by construction (§7 Q1, no drift). Field binder ids are the
    /// positional `Pattern::Var(LeanName)` args in the SAME `args.iter()` order
    /// the reference reads the VIR `fields` — and production built each LeanName
    /// via `LeanName::from_var_ident(&binding.name)`, so `text_leaf(name)` here
    /// equals the reference `binder_id(&binding.name)`. Non-ctor patterns
    /// (Wildcard/Tuple/Or/Binding/Lit at the arm head) fail loud — a def-body
    /// match on a datatype presents ctor patterns; the reference twin likewise
    /// fails loud (`rawvir-arm-pat`), so the two agree on rejection.
    fn lpattern_ctor_binds(&mut self, pat: &LPattern) -> Sr<(u64, String)> {
        match pat {
            LPattern::Ctor { name, args } => {
                let ctor_id = self.text_leaf(name);
                let mut binds = format!("{}.BinderIdList.Nil", NS);
                for a in args.iter().rev() {
                    let bid = self.lpattern_binder_id(a)?;
                    binds = format!("({}.BinderIdList.Cons {} {})", NS, bid, box_raw(&binds));
                }
                Ok((ctor_id, binds))
            }
            _ => Err("ed-arm-pat".to_string()),
        }
    }

    /// A production ctor-FIELD pattern → its bound-var binder id — the twin of
    /// the reference `pattern_binder_id`. Only a `Pattern::Var(LeanName)` (the
    /// fixture's `Leaf(v)` / `Node(_l, _r)` — `_l`/`_r` are NAMED vars, not bare
    /// `_`) is mirrored, interning the LeanName text. That equals the reference
    /// `binder_id(&binding.name)` because production built the LeanName via
    /// `LeanName::from_var_ident(&binding.name)` (= what `binder_id` interns).
    /// Wildcards / nested patterns fail loud, matching the reference twin.
    fn lpattern_binder_id(&mut self, pat: &LPattern) -> Sr<u64> {
        match pat {
            LPattern::Var(name) => Ok(self.text_leaf(name.as_str())),
            _ => Err("ed-field-pat".to_string()),
        }
    }

    /// Fold a production quantifier node (`Forall`/`Exists`, which carries ALL
    /// its binders in one `Vec<Binder>`) into the nested single-binder
    /// `ExprData::Forall`/`Exists` mirror — right-to-left, so `∀ x y, P` ⟶
    /// `Forall x (Forall y P)`, matching the reference `raw_vir_exp` `Quant`
    /// arm's identical nesting over the SAME binder order. Binder-NAME ids
    /// intern via `text_leaf(from_var_ident)` (= the reference `binder_id`);
    /// binder-TYPE via `ltyp_to_typdata`. A nameless (instance-bracket) binder
    /// can't be a quantifier var → fail loud (`ed-quant-noname`); an empty
    /// binder list likewise (`ed-quant-empty`).
    fn lquant_to_exprdata(
        &mut self,
        ctor: &str,
        binders: &[crate::lean_ast::Binder],
        body: &LExpr,
    ) -> Sr<String> {
        if binders.is_empty() {
            return Err("ed-quant-empty".to_string());
        }
        let mut acc = self.lexpr_to_exprdata(body)?;
        for b in binders.iter().rev() {
            let name = b.name.as_ref().ok_or_else(|| "ed-quant-noname".to_string())?;
            let bid = self.text_leaf(name.as_str());
            let bty = self.ltyp_to_typdata(&b.ty)?;
            acc = format!(
                "({}.ExprData.{} {} {} {})",
                NS,
                ctor,
                bid,
                paren(&bty),
                box_ed(&acc)
            );
        }
        Ok(acc)
    }

    /// Recognize a production quantifier binder's RENDERED type-`Expr` (built by
    /// `typ_to_expr`) back to the `lib.TypData` text the reference `typ_data`
    /// emits from the same VIR `Typ` — the inverse that makes the two sides'
    /// quantifier binder types agree for `def_eq`. Primitive heads map by name
    /// (`Prop`→TyBool, `Int`→TyInt, `Nat`→TyNat); a `Tactus.Ref`/`Tactus.MutRef`
    /// application → `TyRef(intern(pp(inner)))`; any other head (a named
    /// datatype, bare or applied) → `TyNamed(intern(pp(whole-ty)))`. The interned
    /// ids agree by construction: production's binder `ty` IS `typ_to_expr(vir)`,
    /// and the reference's `typ_leaf`/`TyRef`/`TyNamed` id is
    /// `intern(pp(typ_to_expr(vir)))` off the SAME `self.leaves` table (`typ_leaf`
    /// = `intern(pp_expr(typ_to_expr(typ)))`; `typ_to_expr` peels Box/Decorate
    /// transparently, exactly like `typ_data`).
    ///
    /// KNOWN GAP (documented, not unsound): `typ_to_expr` collapses BOTH `nat`
    /// and `usize`/`char` to `Var("Nat")`, but the reference `typ_data` maps only
    /// true `nat` to `TyNat` (`usize`/`char` → `TyInt`). So a `nat` binder
    /// certifies; a `usize`/`char` binder yields prod `TyNat` vs ref `TyInt` → the
    /// bridge SPURIOUSLY fails (uncertifiable, never wrongly passes). Similarly a
    /// bare type-PARAM binder (`Var("T")`) is indistinguishable from a nullary
    /// datatype here → maps to `TyNamed`, while the reference `typ_data` fails
    /// loud on `TypParam`; the reference is the gate (W7d bridges only when BOTH
    /// sides succeed), so production's extra `TyNamed` is simply unused.
    /// Disambiguating either would require a `typ_to_expr` change (its own turn).
    fn ltyp_to_typdata(&mut self, ty: &LExpr) -> Sr<String> {
        match &ty.node {
            ExprNode::Var(n) => match n.as_str() {
                "Prop" => Ok(format!("{}.TypData.TyBool", NS)),
                "Nat" => Ok(format!("{}.TypData.TyNat", NS)),
                "Int" => Ok(format!("{}.TypData.TyInt", NS)),
                _ => {
                    let id = self.leaves.intern(pp_expr(ty));
                    Ok(format!("({}.TypData.TyNamed {})", NS, id))
                }
            },
            ExprNode::App { head, args } => {
                if let ExprNode::Var(h) = &head.node {
                    if (h.as_str() == "Tactus.Ref" || h.as_str() == "Tactus.MutRef")
                        && args.len() == 1
                    {
                        let id = self.leaves.intern(pp_expr(&args[0]));
                        return Ok(format!("({}.TypData.TyRef {})", NS, id));
                    }
                }
                let id = self.leaves.intern(pp_expr(ty));
                Ok(format!("({}.TypData.TyNamed {})", NS, id))
            }
            _ => Err("ed-quant-bty".to_string()),
        }
    }

    // ── W7c (bootstrap-30): production `lean_ast::Def` → DefData (prod header) ─
    //
    // The boring 1:1 header transcription paired with the VIR-side
    // `raw_vir_def`. Name/binder/type ids agree with the reference BY
    // CONSTRUCTION: `def.name` = `lean_name(path)` = the reference `call_fun_id`
    // string; each value-param binder name = `from_var_ident` = the reference
    // `binder_id`; `binder.ty`/`ret_ty` are `typ_to_expr(vir)`, which
    // `ltyp_to_typdata` inverts to the same `TypData` the reference `typ_data`
    // emits from the VIR `Typ`.
    //
    // The REFERENCE is the poly gate (fails loud on `typ_params`), so a
    // polymorphic def's leading `{A : Type}` / trait-bound binders here — which
    // `ltyp_to_typdata` would spuriously map to `TyNamed` — are never observed by
    // the bridge (W7d bridges only when both sides succeed). For a monomorphic
    // def, `def.binders` IS exactly the value params, matching the reference.
    // `#[allow(dead_code)]` until W7d wires the def entry point (verdict-neutral).

    /// `lean_ast::Def` (a `@[reducible] def`) → `lib.DefData` text. Fails loud
    /// (`ed-def-<k>`) on an anonymous binder / an uncovered body or param type.
    #[allow(dead_code)]
    fn ldef_to_defdata(&mut self, def: &crate::lean_ast::Def) -> Sr<String> {
        // Intern FORWARD (name, then params in declaration order) so the ids
        // match the reference `raw_vir_def`'s forward interning; format the
        // `ParamList` reversed.
        let name_id = self.text_leaf(&def.name);
        let mut params_txt: Vec<(u64, String)> = Vec::new();
        for b in def.binders.iter() {
            let bname = b.name.as_ref().ok_or_else(|| "ed-def-noname".to_string())?;
            let pid = self.text_leaf(bname.as_str());
            let pty = self.ltyp_to_typdata(&b.ty)?;
            params_txt.push((pid, pty));
        }
        let ret_ty = self.ltyp_to_typdata(&def.ret_ty)?;
        let body = self.lexpr_to_exprdata(&def.body)?;
        let mut plist = format!("{}.ParamList.Nil", NS);
        for (pid, pty) in params_txt.iter().rev() {
            plist = format!("{}.ParamList.Cons {} {} {}", NS, pid, paren(pty), box_(&plist));
        }
        Ok(format!(
            "({}.DefData.mk {} {} {} {})",
            NS,
            name_id,
            paren(&plist),
            paren(&ret_ty),
            paren(&body)
        ))
    }

    // ── W7c (bootstrap-31): production `lean_ast::Datatype` → DtData (prod dt) ─
    //
    // The boring 1:1 datatype transcription paired with the VIR-side `raw_vir_dt`.
    // Name / ctor-name / field-type ids agree with the reference BY CONSTRUCTION:
    // `Datatype.name` = `lean_name(path)` = the reference `raw_vir_dt` name string;
    // each `Variant.name` was built as `sanitize(&v.name)` (to_lean_fn's datatype
    // builder) = the reference `sanitize(&v.name)`; each `Field.ty` is
    // `typ_to_expr(vir_field_typ)`, which `ldt_field_typdata` inverts to the same
    // `TypData` the reference `dt_field_typ_data` emits — INCLUDING the `Box`:
    // `typ_to_expr` renders `Box<T>` as `Tactus.Box T` (kept, not peeled), which
    // `ldt_field_typdata` recognizes back to `TyBox(pointee)`.
    //
    // Only the multi-variant `Inductive`/`IndexedInductive` kinds are handled
    // (they share the ctor-list shape); a single-variant `Structure` fails loud
    // (`ed-dt-struct`) — the reference gates it out symmetrically. `#[allow(dead_code)]`
    // until W7d wires the datatype entry point (verdict-neutral).

    /// A datatype FIELD type `Expr` → `lib.TypData` text, recognizing the KEPT
    /// `Box`: `Tactus.Box T → TyBox(intern(pp(T)))`, matching the reference
    /// `dt_field_typ_data`'s `typ_leaf(inner)`. Everything else delegates to the
    /// shared header recognizer `ltyp_to_typdata` (Int/Nat/named/`Tactus.Ref`).
    #[allow(dead_code)]
    fn ldt_field_typdata(&mut self, ty: &LExpr) -> Sr<String> {
        if let ExprNode::App { head, args } = &ty.node {
            if let ExprNode::Var(h) = &head.node {
                if h.as_str() == "Tactus.Box" && args.len() == 1 {
                    let id = self.leaves.intern(pp_expr(&args[0]));
                    return Ok(format!("({}.TypData.TyBox {})", NS, id));
                }
            }
        }
        self.ltyp_to_typdata(ty)
    }

    /// `lean_ast::Datatype` (an `inductive`) → `lib.DtData` text. Fails loud
    /// (`ed-dt-<k>`) on a single-variant `Structure` / an uncovered field type.
    #[allow(dead_code)]
    fn ldt_to_dtdata(&mut self, dt: &crate::lean_ast::Datatype) -> Sr<String> {
        use crate::lean_ast::DatatypeKind;
        let variants = match &dt.kind {
            DatatypeKind::Inductive { variants } | DatatypeKind::IndexedInductive { variants } => {
                variants
            }
            DatatypeKind::Structure { .. } => return Err("ed-dt-struct".to_string()),
        };
        // Intern FORWARD (name, then per-variant ctor names + field-type ids in
        // declaration order) to match the reference `raw_vir_dt`; format the
        // `CtorList` / `TypList` reversed.
        let name_id = self.text_leaf(&dt.name);
        let mut ctors_txt: Vec<(u64, String)> = Vec::new();
        for v in variants.iter() {
            let ctor_id = self.text_leaf(&v.name);
            let mut flds_txt: Vec<String> = Vec::new();
            for f in v.fields.iter() {
                flds_txt.push(self.ldt_field_typdata(&f.ty)?);
            }
            let mut tylist = format!("{}.TypList.Nil", NS);
            for ft in flds_txt.iter().rev() {
                tylist = format!("{}.TypList.Cons {} {}", NS, paren(ft), box_(&tylist));
            }
            ctors_txt.push((ctor_id, tylist));
        }
        let mut clist = format!("{}.CtorList.Nil", NS);
        for (cid, tylist) in ctors_txt.iter().rev() {
            clist = format!("{}.CtorList.Cons {} {} {}", NS, cid, paren(tylist), box_(&clist));
        }
        Ok(format!("({}.DtData.mk {} {})", NS, name_id, paren(&clist)))
    }

    // ── Statement walk (StmData literal) ────────────────────────────

    fn stm(&mut self, stm: &Stm) -> Sr<String> {
        match &stm.x {
            StmX::Block(stms) => self.block(&stms[..]),

            // AssertCompute dispatches identically to Assert in the
            // walker; fold it here. Two-role emission (finding-1): the
            // ANNOTATED obligation leaf drives the goal (production
            // span_mark's it); the BARE prop leaf drives the forward hyp
            // the assert adds for the rest of the body. Intern the bare
            // hyp first (keeps it in body pre-order), then the annotated
            // obligation — the goal walk (N3b) reuses whichever id.
            StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => {
                // Counter mirror: one production theorem per assert.
                self.consume_theorem_ids(1);
                // Intern the BARE hyp first (keeps it in body pre-order), then
                // the obligation slot (`oblig_slot` interns the span_mark'd
                // leaf + the deep `raw_exp` atoms after it). The hyp render
                // is kept as an LExpr first so the N1-hoist poison check
                // (bootstrap-74 slice 2) sees the exact interned term: a
                // prop mentioning an in-scope residue let poisons the frame
                // (whole-goal wrap, mirroring hoist_all's bail).
                // Binder-aware ctx (bootstrap-77, the bootstrap-18 class):
                // production renders assert/assume hyps through the walk's
                // render ctx — a `&`-param mention (`*s` → `s.deref`) must
                // match (apply_hom_symbol evidence).
                let hyp_lx_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                    e,
                    &self.render_ctx().with_let_binder_typs(&self.let_binder_typs),
                )
                .map_err(|reason| format!("leaf-render: {}", reason))?;
                let hyp_lx = self.apply_renames(&hyp_lx_raw);
                let hp = self.hyp_poison(&hyp_lx);
                if hp == 1 {
                    // A poisoned hyp forces whole-goal wrap from here.
                    self.mark_poison_forced()?;
                }
                let hyp = self.leaves.intern(pp_expr(&hyp_lx));
                // F4: register the prop's deep for the poison derivation.
                self.register_prop_deep(hyp, e, hp)?;
                // The forward hyp's `_h_hoist_i` name (bump AFTER the prop
                // interns so the name leaf follows the prop in the table).
                let hn = self.next_hyp_name();
                // W6d.2b: the obligation slot is a DEEP `RawExp` when the assert
                // condition is coverable (`raw_exp` succeeds → `RawExp.Span(loc,
                // raw)`, id → `deep_ids`); else the opaque `atom_ob(id)` fallback
                // (same interned id the goal side atom-matches — the W6d.2a
                // verdict-neutral behavior).
                let (_id, slot) = self.oblig_slot(e)?;
                Ok(format!("({}.StmData.Assert {} {} {})", NS, slot, hn, hyp))
            }

            StmX::Assume(e) => {
                // Mirror the walker: drop synthetic resolution-tracking
                // assumes (HasResolved / closure-spec), which don't render
                // to Prop and carry no information the mirror models.
                if crate::sst_to_lean::is_synthetic_assume_to_drop(e) {
                    return Ok(self.skip());
                }
                // Binder-aware ctx — see the Assert arm (bootstrap-77).
                let e_lx_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                    e,
                    &self.render_ctx().with_let_binder_typs(&self.let_binder_typs),
                )
                .map_err(|reason| format!("leaf-render: {}", reason))?;
                let e_lx = self.apply_renames(&e_lx_raw);
                let hp = self.hyp_poison(&e_lx);
                if hp == 1 {
                    self.mark_poison_forced()?;
                }
                let id = self.leaves.intern(pp_expr(&e_lx));
                // F4: register the prop's deep for the poison derivation.
                self.register_prop_deep(id, e, hp)?;
                let hn = self.next_hyp_name();
                Ok(format!("({}.StmData.Assume {} {})", NS, hn, id))
            }

            StmX::Assign { lhs, rhs } => {
                // Simple `x = e` only. Field-path `x.f = e` becomes a
                // functional update in the walker — not modeled by the
                // flat Assign mirror.
                let Some(vid) = crate::sst_to_lean::extract_simple_var_ident(&lhs.dest) else {
                    return Err("assign-field-path".to_string());
                };
                // Render + COERCE the rhs exactly as production's
                // `walk_let` (sst_to_lean.rs:5704-5712): the typed spine
                // with the binder-aware ctx, bridged into the DEST's
                // declared typ via `into_slot` — a ref-typed value bound
                // into a bare-typed local gets its `.deref`
                // (find_cancellation_exec's cond-setup `tmp__6 := w`:
                // production's hoisted eq is `tmp__6 = w.deref`, the
                // bare-Var transcription diverged). Identity when
                // val.typ == dest_typ (the common case; production's
                // comment). The empty-ctx → binder-ctx switch is
                // byte-neutral on the closing corpus: the ctx only
                // affects class-method-call coercion inside the rhs,
                // which no closing subject carries in an Assign (any
                // that did would already diverge from production, which
                // renders with the binder ctx). The value leaf, the
                // hoist equation prop, and the poison check all read the
                // coerced form. The rhs is scoped to the PREVIOUS
                // binding, so the shadow renames apply BEFORE this
                // dest's own freshening (`i := i + 1` keeps plain `i`;
                // the next use is `i_hoist1`).
                let dest_typ = self.local_typs.get(vid).cloned();
                let rctx = self.render_ctx().with_let_binder_typs(&self.let_binder_typs);
                let rhs_typed = crate::to_lean_sst_expr::sst_exp_to_typed(rhs, &rctx)
                    .map_err(|reason| format!("leaf-render: {}", reason))?;
                let rhs_coerced = match &dest_typ {
                    Some(t) => rhs_typed.into_slot(t),
                    None => rhs_typed.into_untyped(),
                };
                let rhs_lx = self.apply_renames(&rhs_coerced);
                let rhs_leaf = self.leaves.intern(pp_expr(&rhs_lx));
                // N1-hoist classification (bootstrap-74 slice 2), mirroring
                // hoist_all's per-let decision (see `assign_let_term`).
                // Shadow mirror (Round D): a re-binding of a taken name
                // freshens (`i` → `i_hoist1`) and renames downstream.
                let src_name = crate::lean_name::LeanName::from_var_ident(vid);
                let chosen = self.fresh_let_name(src_name.as_str());
                let lname = crate::lean_name::LeanName::synthetic(chosen);
                let dest = self.text_leaf(lname.as_str());
                Ok(self.assign_let_term(&lname, dest, dest_typ, &rhs_lx, rhs_leaf, rhs)?)
            }

            StmX::Return { ret_exp, .. } => {
                // Bnd-let peel (bootstrap-74 slice 2): Ghost/spec lets
                // lower to `ExpX::Bind(BndX::Let, …)` INSIDE the return
                // expression (use_multiarg's `let _g2: Ghost<nat> =
                // Ghost(…)`). Production's walk pushes each as its own
                // frame let (`walk_let`) BEFORE the return binding —
                // mirror them as AssignH-class statements Seq'd ahead
                // of the Ret. Only single-binder Let chains peel;
                // anything else stays inside the value render (the
                // plain path, which honest-fails on divergence).
                // Route bit first (bootstrap-77): the peel below and the
                // fork are DEFAULT-route mirrors (`Wp::Let` → `walk_let`
                // peels Bind-chains into frame lets). The LEGACY route
                // (`fn_closer_is_default` false, or no declared ret
                // name/typ) keeps the WHOLE chain inside the `Done` leaf
                // — `lift_if_value`'s Bind arm renders it as-is
                // (is_inverse_pair evidence: `let out := let tmp__ :=
                // (s1, s2); if …` as ONE leaf) — so it must NOT peel.
                // EXACTLY production's Return-arm gate (two conditions):
                // `ctx.ret_name` ↦ `pending_ret_name` (both from
                // `post_condition.dest`) and `ctx.ret_typ` ↦ `ret_typ`
                // (the same `type_map` lookup, sst_to_lean.rs:524).
                // `pending_ret_lname` needs no separate check — it maps
                // off the SAME `dest` Option as `pending_ret_name`
                // (serialize() setup), so they are Some/None together.
                let default_route = !self.wrap_mode
                    && self.pending_ret_name.is_some()
                    && self.ret_typ.is_some();
                let mut peel_terms: Vec<String> = Vec::new();
                let mut cur: Option<&Exp> = ret_exp.as_ref();
                while let (true, Some(e)) = (default_route, cur) {
                    let ExpX::Bind(bnd, body) = &e.x else { break };
                    let Some((lname, rhs, inner)) =
                        crate::sst_to_lean::match_single_let_bind(bnd, body)
                    else {
                        break;
                    };
                    let rhs_lx = crate::to_lean_sst_expr::sst_exp_to_ast_checked(rhs)
                        .map_err(|reason| format!("leaf-render: {}", reason))?;
                    let rhs_leaf = self.leaves.intern(pp_expr(&rhs_lx));
                    let dest = self.text_leaf(lname.as_str());
                    // The let's typ is the rhs exp's SST typ
                    // (production's `walk_let`: `Some(b.a.typ)`) —
                    // Ghost lets declare no local, so `local_typs` has
                    // no entry; the rhs typ is the same source.
                    let term = self.assign_let_term(
                        &lname,
                        dest,
                        Some(rhs.typ.clone()),
                        &rhs_lx,
                        rhs_leaf,
                        rhs,
                    )?;
                    peel_terms.push(term);
                    cur = Some(inner);
                }
                let ret_exp: Option<&Exp> = cur;
                // A5 (bootstrap-77): the DEFAULT Return route
                // (`fn_closer_is_default` + declared ret name AND typ —
                // sst_to_lean's Return-arm gate) goes `Wp::Let(ret, e,
                // Done(ens))` → `walk_let`, which FORKS a spine-position
                // value-if into per-branch walks. Mirror the fork; a
                // failure inside propagates as a loud census tag (P2 —
                // a silently-diverging cert is worse than a reject).
                if default_route {
                    if let Some(e) = ret_exp {
                        if matches!(
                            &crate::sst_to_lean::peel_value_position(e).x,
                            ExpX::If(..)
                        ) {
                            let mut term = self.ret_fork(e)?;
                            for pt in peel_terms.into_iter().rev() {
                                term = format!(
                                    "({}.StmData.Seq {} {})",
                                    NS,
                                    box_(&pt),
                                    box_(&term)
                                );
                            }
                            return Ok(term);
                        }
                    }
                }
                // G4/W6e — the value-if-lift path, mirroring
                // `lift_if_value_coerced`. Since the Return→Wp::Let route
                // landed production-side, the legacy lift only runs on
                // NON-default routes (wrap-mode fns / no declared ret) —
                // gating G4 to match (bootstrap-77) fixes the
                // probe_if_ret-class divergence (a default fn's forked
                // goals vs a folded cert). When the fold applies: the
                // branch-folded implication obligations `Ret([impl…],
                // RetNone)` — the `let r` is folded INTO each obligation,
                // so `RetNone` (NOT `RetLet`) — refWp must not re-fold it.
                // On any recompute failure fall through to the plain path
                // (unchanged, still-honest-failing — never a silent pass).
                // The counter drives the post-stm-walk `deep_ids` seeding
                // so the goal side deepens the matching `Implies` leaves.
                // Pinned by probe14.
                if let (Some(rname), Some(e)) = (self.pending_ret_name, ret_exp) {
                    if !default_route
                        && peel_terms.is_empty()
                        && self.pending_ens_all_deep
                        && !self.pending_ens_oblig.is_empty()
                        && value_lifts(e)
                    {
                        let ens_and = conjoin_raw(&self.pending_ens_oblig);
                        let base = [RawLet { name: rname, body: ens_and }];
                        if let Ok(tree) = self.lift_if_raw(e, &base) {
                            let mut impls: Vec<String> = Vec::new();
                            split_lifted(tree, &mut impls);
                            // Only take the branch-folded path when the lift
                            // actually SPLIT (≥2 obligations) — a degenerate
                            // 1-leaf result is a non-lift the plain path handles
                            // identically (and would mis-conjoin the ensures).
                            if impls.len() >= 2 {
                                self.lifted_return_recomputes += 1;
                                // Counter mirror: one production theorem
                                // per branch-folded implication obligation.
                                self.consume_theorem_ids(impls.len() as u64);
                                let list = raw_exp_list(&impls);
                                return Ok(format!(
                                    "({}.StmData.Ret {} {}.RetBind.RetNone)",
                                    NS, box_(&list), NS
                                ));
                            }
                        }
                    }
                }
                let ret_term = self.ret_terminal_opt(ret_exp)?;
                // Wrap the Bnd-let peels ahead of the Ret (source order:
                // the first peeled let is outermost).
                let mut term = ret_term;
                for p in peel_terms.into_iter().rev() {
                    term = format!("({}.StmData.Seq {} {})", NS, box_(&p), box_(&term));
                }
                return Ok(term);
            }

            // (ret_terminal_opt — the shared Ret/RetBind tail — is
            // defined below, after this match; bootstrap-77 extraction.)
            

            StmX::If(cond, then_stm, else_stm) => {
                // The branch hyps are the ANNOTATED cond / ¬cond, byte-matching
                // production's `Wp::Branch`: it pushes `cond_marked =
                // span_mark(loc, Hypothesis(BranchCondition), lower(cond))` as
                // the then-branch hyp and `not(cond_marked)` as the else-branch
                // hyp (`sst_to_lean::walk_obligations`). `oblig_leaf` /
                // `neg_oblig_leaf` reconstruct the SAME span_mark → pp text
                // (the `AssertKind` never reaches the pp — see `oblig_leaf`),
                // so the If node's cond/¬cond leaves reuse the goal-side branch
                // hyp ids and refWp's `Imp c`/`Imp nc` cancel across the bridge
                // (bootstrap-17). The BARE cond is never an obligation and is
                // used nowhere, so we do not intern it.
                let c = self.oblig_leaf(cond)?;
                let nc = self.neg_oblig_leaf(cond)?;
                // N1-hoist (bootstrap-74 slice 2): the cond/neg-cond hyps
                // are each branch's FIRST pushed hyp, so both take the
                // pre-If ordinal + 1 (the SAME name leaf — count_down
                // evidence: `_h_hoist_1` in both branches). Each branch
                // walk resumes from that ordinal; the post-If counter
                // restores the pre-If value (the two-way join is the
                // documented unmodeled case). The cond poison covers
                // both hyps (c and ¬c mention the same names).
                let cond_inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                    cond,
                    &self.render_ctx(),
                )
                .map_err(|reason| format!("leaf-render: {}", reason))?;
                let cond_inner = self.apply_renames(&cond_inner_raw);
                let cp = self.hyp_poison(&cond_inner);
                if cp == 1 {
                    self.mark_poison_forced()?;
                }
                // F4: register both cond props' deeps for the poison
                // derivation (c and ¬c share the mention set).
                self.register_prop_deep(c, cond, cp)?;
                self.register_prop_deep(nc, cond, cp)?;
                let save = self.hyp_ordinal;
                // Each branch is a separate walk path: the cond hyp is
                // `_h_hoist_{save+1}` in BOTH, and branch-local shadows /
                // wrap-forcing must not leak across (count_down's tmp__3
                // is a FIRST binding in each branch).
                let bstate = self.branch_state();
                let cn = self.text_leaf(&format!("_h_hoist_{}", save + 1));
                let ncn = cn;
                self.hyp_ordinal = save + 1;
                let t = self.stm(then_stm)?;
                let then_forced = (self.flet_forced, self.poison_forced);
                self.restore_branch(bstate.clone());
                self.hyp_ordinal = save + 1;
                let e = match else_stm {
                    Some(s) => self.stm(s)?,
                    None => self.skip(),
                };
                let else_forced = (self.flet_forced, self.poison_forced);
                self.restore_branch(bstate.clone());
                // Forced-state leak (bootstrap-78 review): a FALL-THROUGH
                // branch that trips a wrap-forcer (mut-call rebind,
                // field-assign LetRaw, poison) leaks its classification
                // state into everything serialized AFTER this If (the
                // outer block's continuation, the fn's Ret) — production
                // renders the surviving path under that branch's frames
                // while the serializer restored to pre-If state.
                // Undiagnosed CLOSE-BROKE without the tag; population 0
                // (diverging branches are exempt — nothing survives
                // them). Sharp reject until a subject pins the modeling.
                let base_forced = (bstate.2, bstate.3);
                if (!stm_diverges(then_stm) && then_forced != base_forced)
                    || (else_stm.as_ref().map_or(false, |s| !stm_diverges(s))
                        && else_forced != base_forced)
                {
                    return Err("branch-forced-state-leak".to_string());
                }
                // After: the two-way join is the documented unmodeled
                // case (counter restores to the pre-If value). The
                // FALL-THROUGH case (`frame_after` forwards the ¬cond
                // hyp when then diverges and else is Skip) DID push a
                // hyp on the continuation path — the counter resumes
                // past it.
                let fallthrough = stm_diverges(then_stm) && e == self.skip();
                self.hyp_ordinal = if fallthrough { save + 1 } else { save };
                Ok(format!("({}.StmData.If {} {} {} {} {} {})", NS, c, cn, nc, ncn, box_(&t), box_(&e)))
            }

            StmX::Loop {
                cond,
                original_cond,
                body,
                invs,
                decrease,
                // (wrap-mode loops reject below — see the guard at the
                // arm body's head)
                id,
                ..
            } => {
                // Wrap-mode fns with loops: the mirror telescope
                // (FLetH d_old pair, named inv/cond hyps) is
                // hoist-shaped; production wrap-renders it all
                // goal-position. Unmodeled — reject loud (endgame A2;
                // vocabulary follow-up with the A3/A5 churn).
                if self.attr_user_closer {
                    return Err("user-closer-loop".to_string());
                }
                // finding-3: `modified_vars` is IGNORED (it's `None` at
                // this SST stage — production's `build_wp` spells it `_`
                // and RE-DERIVES the havoc set in `build_wp_loop` via
                // `collect_modifications(body)` + `type_map`). `loop_stm`
                // mirrors that path. `id` names the `_tactus_d_old`
                // snapshot; `decrease` is the termination measure.
                self.loop_stm(cond, original_cond, body, invs, decrease, *id)
            }

            StmX::DeadEnd(inner) => {
                // Assert-forall skolems (endgame A6-short): production
                // ∀-binds referenced AssertByVar locals in this scope's
                // goal telescope — the stage-A arm lands in era 2
                // (bootstrap-81); reject loud until then (SAME detection
                // as production's `collect_assert_by_vars`). Era 1: the
                // vocabulary slots exist (`Nil`/`Nil` here — no skolems
                // reach this arm, so both are always empty).
                if !crate::sst_to_lean::collect_assert_by_vars_in(
                    inner,
                    &self.assert_by_var_typs,
                )
                .is_empty()
                {
                    return Err("assert-forall".to_string());
                }
                let b = self.stm(inner)?;
                Ok(format!(
                    "({}.StmData.DeadEnd {} {} {})",
                    NS,
                    self.binder_list(&[]),
                    self.param_bound_list(&[]),
                    box_(&b)
                ))
            }

            // Transparent passthrough — the walker returns `after`
            // unchanged. Elide (⇒ Skip in a Seq position).
            StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(self.skip()),

            // Call (bootstrap-02b): the one place the serializer does
            // non-transcription work — it INSTANTIATES the callee's
            // requires/ensures at this call's actual args. The leaf
            // RENDERING (opaque, uncertified — DESIGN §2.5) reuses
            // production's exact path via `cert_call_leaves` so the text
            // byte-matches the goal side; the frame STRUCTURE (the
            // certified content) is assembled HERE, independently of
            // `push_post_call_frames`, so the W2 `decide` bridge validates
            // it (Option 1, DESIGN-W2-refwp.md §2.6). Restricted subset:
            // Static + same-crate + no-`&mut` + no-generic + ret-eq; every
            // other shape fails loud from `cert_call_leaves` (sharp tags:
            // call-trait / call-crosscrate / call-mut / call-generic /
            // call-unit-dest / call-dynamic-resolved / call-trait-default)
            // or here (`call-forall-path`).
            StmX::Call {
                fun,
                resolved_method,
                is_trait_default,
                typ_args,
                args,
                dest,
                ..
            } => {
                let leaves = crate::sst_to_lean::cert_call_leaves(
                    fun,
                    resolved_method,
                    is_trait_default,
                    typ_args,
                    args,
                    dest.as_ref(),
                    &stm.span,
                    &self.fn_map,
                    &self.caller_param_typs,
                    &self.let_binder_typs,
                    &self.mut_ref_locals,
                    // Counter mirror (bootstrap-78 S1): the shell emitter
                    // mints this call's gensyms from the WALK-ORDER
                    // counter, and the consumed ids (mut_posts + fresh_ret
                    // + precondition theorem) advance it in place.
                    &mut self.emit_ordinal,
                )?;
                // Cross-check prediction: the precondition THEOREM's id was
                // the last consumed in the advance (after the gensyms), so
                // it equals the counter's current value. Gensyms predict
                // nothing (they never name a theorem).
                if leaves.precondition.is_some() {
                    self.predicted_theorem_ids.push(self.emit_ordinal);
                }
                self.call_stm(leaves)
            }
            // Fail-loud stage-A exclusions.
            StmX::AssertBitVector { .. } => Err("assert-bitvector".to_string()),
            // NonLinear `assert … by(nonlinear_arith)`: an isolated
            // query — the body's obligations under a Hyp-stripped scope
            // (`OblCtx::new_scope` keeps Let/Binder, drops Hyp), no
            // frame delta for the continuation. Mirrors
            // `StmData::AssertQueryNl` / `strip_hyps` in tactus-core.
            // Tactus-tactic mode has a DIFFERENT goal structure (the
            // `have := by <tactic>` render, not an isolated goal list)
            // — sharper tag, still fail-loud.
            StmX::AssertQuery { mode: AssertQueryMode::NonLinear, body, .. } => {
                // Wrap-mode fn (self-review 2026-07-24, finding 1):
                // production's hoist gate is PER-GOAL-CLOSER, and an NL
                // query scope carries the nonlin LADDER closer — which
                // IS default — so its goals HOIST even inside a
                // user-closer fn. The fn-level wrap_mode mirror cannot
                // express that mix; reject loud rather than emit a
                // non-bridging cert (P2 era). R1 RESOLVED the mix:
                // `strip_hyps` strips the seeded `FUserCloser` marker
                // exactly as production's `new_scope` resets the closer
                // to the (default-class) NONLIN ladder — NL query goals
                // inside a user-closer fn hoist again, both sides.
                // N1-hoist (bootstrap-74 slice 2): production's
                // `new_scope` DROPS the enclosing hyps for the isolated
                // query, so the sub-walk numbers its hyps from 0
                // (mul_bound evidence: `_h_hoist_1` inside the query);
                // the enclosing counter resumes untouched after (the
                // query's hyps don't leak — the proven facts re-enter
                // via the follow-on Assume statements, which number
                // themselves). The scope KEEPS Let/Binder frames, so
                // `flet_forced` carries in, but a poisoned OUTER hyp is
                // stripped — `poison_forced` resets inside and restores.
                let save = self.hyp_ordinal;
                let bstate = self.branch_state();
                self.hyp_ordinal = 0;
                self.poison_forced = false;
                let b = self.stm(body)?;
                self.hyp_ordinal = save;
                self.restore_branch(bstate);
                // The query's own ensures is EMPTY — production emits
                // one final in-scope goal `True`
                // (`emit_done_or_split`'s `and_all([])` fallback, the
                // `_tactus_ensures_` theorem; mul_bound evidence). The
                // model closes it under the post-body frame; the
                // obligation slot is the opaque `atom_ob("True")` (the
                // goal side atom-matches the interned `True` text).
                // Counter mirror (bootstrap-78 S1b): that final
                // `Wp::Done(LitBool(true))` terminator IS an emitted
                // theorem (mul_bound's `_tactus_ensures_mul_bound_4`) —
                // consume its id after the body walk, exactly where
                // production's body-Wp terminator emits it.
                self.consume_theorem_ids(1);
                let true_id = self.leaves.intern("True".to_string());
                let tq = atom_ob_lit(true_id);
                Ok(format!("({}.StmData.AssertQueryNl {} {})", NS, box_(&b), tq))
            }
            // A3 (bootstrap-77): the Tactus-mode assert-query, both kinds.
            // * AssertBy (`assert(P) by { tac }`): production emits ONE
            //   theorem for the span-marked P (`walk_assert_by_tactus`,
            //   `emit_with_closer` — NEVER hoists, so refWp closes it
            //   under `f + FUserCloser`), then pushes bare P as an
            //   `AssertFact` hyp for the continuation. Assert-shaped
            //   mirror (`StmData::AssertQueryTactus`): same two-role
            //   leaf emission as the Assert arm. P is proven inline
            //   under the user's tactic — census counts the fn
            //   serialized, never assumed.
            // * ProofBlock (`proof { tac }`): no theorem, no hyp — the
            //   tactic rides the emitter's closer prefix AFTER the hoist
            //   decision (closers are not stage-A-certified) and the
            //   fn-level `closer_is_default` DFS already made this fn
            //   wrap-mode. Structurally absent (Skip).
            StmX::AssertQuery { mode: AssertQueryMode::Tactus { kind, .. }, body, .. } => {
                match kind {
                    vir::ast::TactusKind::ProofBlock => Ok(self.skip()),
                    vir::ast::TactusKind::AssertBy => {
                        // Counter mirror: one production theorem per
                        // assert-by (emit_with_closer site; the inner
                        // Assert is destructured here, never re-walked).
                        self.consume_theorem_ids(1);
                        // `body` is a single `StmX::Assert` carrying the
                        // asserted condition (ast_to_sst's Tactus-shortcut
                        // emission; production destructures identically).
                        let StmX::Assert(_, _, cond) = &body.x else {
                            return Err("assert-query-tactus-shape".to_string());
                        };
                        // Binder-aware ctx (bootstrap-18 class): production's
                        // `walk_assert_by_tactus` pushes `cond_ast` rendered
                        // with `render_ctx().with_let_binder_typs(…)` — a
                        // `&`-param deref (`*s` → `s.deref`) must match
                        // (apply_hom_symbol per-goal evidence: hyp leaf
                        // `…view s` vs production's `…view s.deref`).
                        let hyp_lx_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                            cond,
                            &self.render_ctx().with_let_binder_typs(&self.let_binder_typs),
                        )
                        .map_err(|reason| format!("leaf-render: {}", reason))?;
                        let hyp_lx = self.apply_renames(&hyp_lx_raw);
                        let hp = self.hyp_poison(&hyp_lx);
                        if hp == 1 {
                            self.mark_poison_forced()?;
                        }
                        let hyp = self.leaves.intern(pp_expr(&hyp_lx));
                        // F4: register the prop's deep for the poison derivation.
                        self.register_prop_deep(hyp, cond, hp)?;
                        let hn = self.next_hyp_name();
                        let (_id, slot) = self.oblig_slot(cond)?;
                        Ok(format!(
                            "({}.StmData.AssertQueryTactus {} {} {})",
                            NS, slot, hn, hyp
                        ))
                    }
                }
            }
            StmX::AssertQuery { mode: AssertQueryMode::BitVector, .. } =>
                Err("assert-query-bitvector".to_string()),
            StmX::BreakOrContinue { .. } => Err("break-or-continue".to_string()),
            StmX::OpenInvariant(_) => Err("open-invariant".to_string()),
            StmX::ClosureInner { .. } => Err("closure-inner".to_string()),
        }
    }

    /// Terminal `Ret(ens, RetBind)` for a (possibly branch-local) return
    /// value — the shared tail of the plain Return path and every
    /// `ret_fork` leaf (bootstrap-77 A5 extraction; body unchanged).
    fn ret_terminal(&mut self, e: &Exp) -> Sr<String> {
        self.ret_terminal_opt(Some(e))
    }

    fn ret_terminal_opt(&mut self, ret_exp: Option<&Exp>) -> Sr<String> {
                // Counter mirror: one production theorem per ensures
                // obligation at each Ret terminal (fork-route branch Rets
                // each consume — head_exec `_1`/`_2`; a `return;`/no-ens fn
                // consumes 0).
                self.consume_theorem_ids(self.pending_ens_oblig.len() as u64);
                // Annotated ensures obligation leaves drive the `Return`
                // goal (Ret-annotation, finding-1): span_mark'd like
                // production's `WpCtx` postcondition so the goal-side
                // postcondition leaf reuses the same id and cancels.
                // W6d.2b: the ensures obligations are a DEEP `RawExpList`
                // (closed via `close_each_e`). Each slot was built at setup by
                // `oblig_slot` — a deep `RawExp.Span(loc, raw)` for a coverable
                // ensures (id in `deep_ids`), else the `atom_ob(id)` fallback.
                // bootstrap-79 (Ret-dest collision): production freshens the
                // return binder when the declared dest name is ALREADY taken
                // at the return site (copy_word: the loop's havoc set claims
                // `out`, so the ret binder becomes `out_hoist1` with eq-hyp
                // `_h_out_hoist1_hoist1 : out_hoist1 = out`, and the ensures
                // leaf renders with the rename in effect). Mirror the shadow
                // mirror: freshen via `fresh_let_name` (records the rename),
                // rebuild the ensures obligations with the rename applied,
                // and bind under the fresh name. (The coerced VALUE below
                // renders AFTER this — the local stays plain —
                // `out_hoist1 = out`.)
                let dest_collision = self
                    .pending_ret_lname
                    .as_ref()
                    .map_or(false, |d| self.bound_names.contains(d));
                let (ret_name, list) = if dest_collision {
                    let dest = self.pending_ret_lname.clone().unwrap();
                    // The rename applies to the ENSURES obligations
                    // (and the fresh binder/eq-name), NOT to the return
                    // VALUE (`out_hoist1 = out`, not `= out_hoist1`) —
                    // restore the rename env after the rebuild.
                    let save_renames = self.rename_env.clone();
                    let fresh = self.fresh_let_name(&dest);
                    let mut new_oblig = Vec::new();
                    for marked in self.pending_ens_marked.clone().iter() {
                        let renamed = self.apply_renames(marked);
                        let id = self.leaves.intern(pp_expr(&renamed));
                        new_oblig.push(atom_ob_lit(id));
                    }
                    self.rename_env = save_renames;
                    (Some(fresh), raw_exp_list(&new_oblig))
                } else {
                    (
                        self.pending_ret_lname.clone(),
                        raw_exp_list(&self.pending_ens_oblig),
                    )
                };
                // Return-value binding (finding-4): production prepends
                // `let <ret> := <e>` before the postcondition (the walker's
                // `let_bind_synthetic(sanitize(ret), <e_ast>, …)`, peeled
                // into a `CtxFrame::Let` by `emit_done_or_split`). Bind ONLY
                // when BOTH a declared return var AND a return expr exist —
                // exactly the walker's condition (a `return;` or a fn with no
                // `-> (r:T)` binds nothing). The value is the return expr via
                // the SAME `exp_leaf` path the body's Assign rhs uses; the
                // walker's coercion / if-value lifting is NOT replicated here
                // (a stage-A caveat — a divergence fails the bridge to close,
                // never silent-passes).
                let retbind = match (ret_name, ret_exp) {
                    (Some(ret_name), Some(e)) => {
                        let nleaf = self.text_leaf(&ret_name);
                        // Render the return value with the binder-aware ctx
                        // (bootstrap-18) so an explicit `&`-param `*p` derefs
                        // to `p.deref`, then apply production's per-leaf
                        // return-typ coercion (`lift_if_value_coerced` base
                        // case → `coerce_leaf`): coerce the rendered value
                        // from its OWN Exp typ to the declared `ret_typ`. This
                        // inserts the `.deref` for a bare `&`-value return
                        // (`fn clone(self: &S) -> S` returns `Var(self) : &S`
                        // → coerced to `S` → `self.deref`) that `binder_typs`
                        // alone can't reach (no explicit deref in the Exp). For
                        // a return whose Exp typ already equals `ret_typ`
                        // (u64→u64, arith, generic `T`) the coerce is a no-op.
                        // Scoped so the `&self` borrows (render_ctx,
                        // let_binder_typs, ret_typ) end before `intern`
                        // takes `&mut self`. if-value LIFTING is still
                        // NOT replicated (a genuinely-liftable-if return
                        // renders as one leaf here vs production's
                        // lifted And/Imp structure) — that case
                        // honest-fails the bridge, never silent-passes.
                        // The value renders through production's TYPED
                        // SPINE (`sst_exp_to_typed` + `into_slot`) with
                        // the let-binder env — that's what inserts
                        // `.deref` on a Ref-typed call-result local
                        // (`r = tmp__1.deref` in vec_read), which the
                        // checked path + claimed-typ coerce could not
                        // reach. The coerced LExpr is ALSO the equation
                        // rhs for the N1-hoisted binding (rendered
                        // once, used twice).
                        let coerced_raw = {
                            let rctx = self.render_ctx()
                                .with_let_binder_typs(&self.let_binder_typs);
                            let typed = crate::to_lean_sst_expr::sst_exp_to_typed(e, &rctx)
                                .map_err(|reason| format!("leaf-render: {}", reason))?;
                            match &self.ret_typ {
                                Some(rt) => typed.into_slot(rt),
                                None => typed.inner,
                            }
                        };
                        let coerced = self.apply_renames(&coerced_raw);
                        let vleaf = self.leaves.intern(pp_expr(&coerced));
                        // The b79 collision rename (above) already set
                        // `ret_name` to the freshened binder; the eq
                        // pair takes its LeanName form.
                        let ret_lname =
                            Some(crate::lean_name::LeanName::synthetic(ret_name.clone()));
                        // N1-hoist (bootstrap-74 slice 2): the return
                        // binding is a typed let — hoist it to
                        // `RetLetH` (binder pair `(r : T)
                        // (_h_r_hoist1 : r = v)`) when the declared ret
                        // typ is known non-Bool; a Bool ret stays
                        // `RetLet` (wrap — a Bool ret is the documented
                        // RetLetR-less caveat: production residue-wraps
                        // it, the bridge honest-fails). F4 (bootstrap-80
                        // stage 2): the poison collapse moved
                        // reference-side — a poisoned equation still
                        // emits `RetLetH` and refWp derives the lossless
                        // collapse from the registered deep. Wrap-mode
                        // fn: the legacy Return route keeps the
                        // goal-position let — never RetLetH.
                        let hoistable = !self.wrap_mode
                            && match (&self.ret_typ, &ret_lname) {
                                (Some(rt), Some(_)) => !matches!(&**rt, vir::ast::TypX::Bool),
                                _ => false,
                            };
                        match (hoistable, ret_lname) {
                            (true, Some(lname)) => {
                                let rt = self.ret_typ.clone().unwrap();
                                let ty_leaf = self.typ_leaf(&rt);
                                let (en, ep) = self.eq_leaves(&lname, &coerced);
                                // F4: register the eq prop's deep (the
                                // RHS transcription is mention-equivalent
                                // — the ret binder is never a residue).
                                let hp = self.hyp_poison(&LExpr::eq(LExpr::var(lname.clone()), coerced.clone()));
                                self.register_prop_deep(ep, e, hp)?;
                                format!(
                                    "{}.RetBind.RetLetH {} {} {} {} {}",
                                    NS, nleaf, ty_leaf, vleaf, en, ep
                                )
                            }
                            _ => format!("{}.RetBind.RetLet {} {}", NS, nleaf, vleaf),
                        }
                    }
                    _ => format!("{}.RetBind.RetNone", NS),
                };
                Ok(format!("({}.StmData.Ret {} {})", NS, box_(&list), paren(&retbind)))
    }

    fn skip(&self) -> String {
        format!("{}.StmData.Skip", NS)
    }

    /// Right-nest a block into `Seq(s0, Seq(s1, …, sn))`. Empty ⇒ Skip.
    ///
    /// Two-way If-join desugar (bootstrap-19, Option 2): when a mid-block
    /// `if C { t } else { e }` is FOLLOWED by a continuation, production
    /// clones `after` into BOTH branches (`build_wp`: `build_wp(then, after)`
    /// / `build_wp(else, after)`) so the trailing statements are visited once
    /// per branch under that branch's cond hyp + body frame. refWp is kept
    /// FROZEN — teaching `wp_stm` the two-way join forces well-founded
    /// recursion (the branch subterms sit at match-depth 2), and
    /// `WellFounded.fix` does NOT reduce under `decide`, breaking every Seq
    /// bridge (the bootstrap-19 finding). So the serializer bakes the clone
    /// into the SST TREE here: emit `If(t; rest, e; rest)` instead of
    /// `Seq(If(t,e), rest)`, and refWp's existing FLAT If/Seq arms (depth-1
    /// structural recursion) then reproduce production's goals. A branch that
    /// DIVERGES (`stm_diverges`: Return / DeadEnd / break) discards the
    /// continuation — production's Return arm ignores `after` — so `rest` is
    /// NOT cloned into it (the one-sided fall-through, e.g. find_square's
    /// `if … { return }`). This is NON-transcription (a TCB step, like the
    /// Call instantiation): the `decide` bridge validates the clone against
    /// production's independently-computed goals (recompute-not-copy).
    fn block(&mut self, stms: &[Stm]) -> Sr<String> {
        if stms.is_empty() {
            return Ok(self.skip());
        }
        // Flatten nested Blocks FIRST (bootstrap-77, inverse_column_exec
        // evidence): production's `build_wp` threads the continuation
        // through block boundaries transparently, so an If at the TAIL of
        // an inner block (a `proof { }` scope puts the rest of the body
        // in one) still clones the OUTER continuation into its branches.
        // Without flattening, `as_if(&stms[0])` sees a Block and the
        // two-way-join desugar never fires — refWp then closes the
        // post-If continuation ONCE where production emits it per branch.
        // Walk order (leaf interning, hyp ordinals) is unchanged —
        // flattening only reshapes the Seq tree.
        if stms.iter().any(|s| matches!(&s.x, StmX::Block(_))) {
            let mut flat: Vec<Stm> = Vec::new();
            for s in stms {
                match &s.x {
                    StmX::Block(inner) => flat.extend(inner.iter().cloned()),
                    _ => flat.push(s.clone()),
                }
            }
            return self.block(&flat);
        }
        if stms.len() > 1 {
            if let Some((cond, then_stm, else_stm)) = as_if(&stms[0]) {
                // Desugar ONLY the TRUE two-way join — BOTH branches fall
                // through to the continuation (count_down). A branch that
                // DIVERGES (find_square's `if … { return }`) is left as the
                // frozen `Seq(If, rest)`, handled by bootstrap-17's
                // `frame_after` fall-through special case. This restriction is
                // load-bearing, not just conservative: moving `rest` INTO an
                // If branch hides it from `frame_after(If)` (which, for a
                // two-way If, returns the BARE pre-If frame), so a loop whose
                // body ends in such an If would get a wrong maintain-reclose
                // frame — a `CLOSE-BROKE`, not an honest-fail. The
                // both-fall-through join only arises at a fn-body TAIL in the
                // corpus (count_down), where `frame_after` is never queried;
                // a both-fall-through If inside a loop stays a documented
                // residual (would need the loop-body post-frame to be the
                // branch join, which a single linear frame cannot express).
                let then_div = stm_diverges(then_stm);
                let else_div = else_stm.as_ref().map_or(false, stm_diverges);
                if !then_div && !else_div {
                    let c = self.oblig_leaf(cond)?;
                    let nc = self.neg_oblig_leaf(cond)?;
                    // N1-hoist names + per-branch counter snapshot (see the
                    // StmX::If arm — the cond hyp is `_h_hoist_{save+1}` in
                    // BOTH branches; each branch walk resumes from save+1;
                    // the counter restores after).
                    let cond_inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                        cond,
                        &self.render_ctx(),
                    )
                    .map_err(|reason| format!("leaf-render: {}", reason))?;
                    let cond_inner = self.apply_renames(&cond_inner_raw);
                    let cp = self.hyp_poison(&cond_inner);
                    if cp == 1 {
                        self.mark_poison_forced()?;
                    }
                    // F4: register both cond props' deeps (c, ¬c — same
                    // mention set).
                    self.register_prop_deep(c, cond, cp)?;
                    self.register_prop_deep(nc, cond, cp)?;
                    let save = self.hyp_ordinal;
                    let bstate = self.branch_state();
                    let cn = self.text_leaf(&format!("_h_hoist_{}", save + 1));
                    let ncn = cn;
                    // Serialize the then-branch, then the continuation ONCE
                    // (its leaves intern in then-branch position — matching
                    // production's after-clone walk order), then reuse the
                    // `rest` term verbatim in the else branch (interning is
                    // idempotent). An absent else falls through as `Skip`.
                    // Branch state restores between branches (separate
                    // walk paths — branch-local shadows don't leak).
                    self.hyp_ordinal = save + 1;
                    let then_body = self.stm(then_stm)?;
                    // Counter mirror (bootstrap-78 S1b): production clones
                    // `after` into BOTH branch Wps, so the continuation's
                    // theorems are emitted TWICE — once per branch
                    // (count_down id 5 / clamped_inc ids 4-5 = the
                    // else-branch copy). The term is reused verbatim, but
                    // the consumption must replay for the else copy.
                    // Record the continuation's consumption during its one
                    // serialization; replay after the else-branch walk.
                    let cont_ord_before = self.emit_ordinal;
                    let cont_preds_before = self.predicted_theorem_ids.len();
                    let rest = self.block(&stms[1..])?;
                    let cont_thms =
                        (self.predicted_theorem_ids.len() - cont_preds_before) as u64;
                    let cont_ords = self.emit_ordinal - cont_ord_before;
                    let t = format!("({}.StmData.Seq {} {})", NS, box_(&then_body), box_(&rest));
                    // Captured BEFORE the restore below wipes it — the
                    // forced-state-leak guard reads both branches' end
                    // states (bootstrap-78 review).
                    let then_forced = (self.flet_forced, self.poison_forced);
                    self.restore_branch(bstate.clone());
                    self.hyp_ordinal = save + 1;
                    let else_body = match else_stm {
                        Some(s) => self.stm(s)?,
                        None => self.skip(),
                    };
                    // A gensym-consuming continuation (a Call after the
                    // join) would mint then-copy names into the single
                    // reused term while production's else copy mints its
                    // own — the leaves cannot match both. Reject loud
                    // (P2; corpus population 0).
                    if cont_ords != cont_thms {
                        return Err("call-in-branch-join".to_string());
                    }
                    // Forced-state leak (bootstrap-78 review): a branch
                    // that trips a wrap-forcer (mut-call rebind, field-
                    // assign LetRaw, poison) changes how the SHARED
                    // continuation term's lets/hyps classify — the term
                    // was serialized once under THEN-state, so the other
                    // path's copy is wrong (production renders each path
                    // under its own frames). Undiagnosed CLOSE-BROKE
                    // without this tag; population 0 today. The long fix
                    // is per-branch continuation serialization (which
                    // would also retire call-in-branch-join) — card §3.
                    if then_forced != (bstate.2, bstate.3)
                        || (self.flet_forced, self.poison_forced) != (bstate.2, bstate.3)
                    {
                        return Err("branch-forced-state-join".to_string());
                    }
                    self.consume_theorem_ids(cont_thms);
                    let e = format!("({}.StmData.Seq {} {})", NS, box_(&else_body), box_(&rest));
                    self.restore_branch(bstate);
                    self.hyp_ordinal = save;
                    return Ok(format!(
                        "({}.StmData.If {} {} {} {} {} {})",
                        NS, c, cn, nc, ncn, box_(&t), box_(&e)
                    ));
                }
            }
        }
        let head = self.stm(&stms[0])?;
        if stms.len() == 1 {
            return Ok(head);
        }
        let tail = self.block(&stms[1..])?;
        Ok(format!("({}.StmData.Seq {} {})", NS, box_(&head), box_(&tail)))
    }

    /// Assemble the `StmData.Call { reqs, post }` literal from the
    /// production-rendered leaves (`cert_call_leaves`, bootstrap-02b).
    /// `reqs` is the single conjoined precondition obligation (or Nil);
    /// `post` is the post-call FrameList — built HERE from the
    /// path-tagged ingredients, so the frame STRUCTURE is the
    /// serializer's own (independent) code and the W2 `decide` bridge
    /// validates it against production's `push_post_call_frames`. Only
    /// the ret-eq path is assembled this turn; the ∀-path fails loud
    /// (`call-forall-path`) pending a validating fixture.
    fn call_stm(&mut self, leaves: crate::sst_to_lean::CertCallLeaves) -> Sr<String> {
        use crate::sst_to_lean::CertCallPost;
        // reqs: a single-element LeafList — production `and_all`s the
        // callee requires into ONE CallPrecondition obligation — or Nil.
        // W6d.2a: reqs is now a DEEP `RawExpList` (closed via `close_each_e`).
        // Single-element opaque fallback (or Nil) — the interned precondition
        // id rides through as `atom_ob(id)`.
        let reqs = match &leaves.precondition {
            Some(l) => {
                // The precondition IS a goal at this frame point.
                let id = self.leaves.intern(pp_expr(l));
                raw_exp_list(&[atom_ob_lit(id)])
            }
            None => raw_exp_list(&[]),
        };
        // `&mut` rebind targets (bootstrap-78 S3): production's Phase-4
        // pushes `CtxFrame::Let(local, …, None)` under the local's OWN
        // name — never freshened (the typ-less let wrap-forces every
        // goal containing it, and `rename_frame_vars` only runs inside
        // `hoist_all`). A target under an ACTIVE shadow rename would
        // need the rename applied on one side only — loud tag instead
        // (zero corpus population; a subject would pin the choice).
        for m in leaves.mut_args.iter() {
            if self.rename_env.contains_key(m.rebind_local.as_str()) {
                return Err("call-mut-renamed-local".to_string());
            }
        }
        // dest binder id = interned leaf id of the dest's rendered name
        // (same path as `binder_id`; production Phase-5 binds
        // `let <dest> := …`). Shadow mirror (Round D): a colliding dest
        // freshens, and the post-frame leaves render under the active
        // renames. `None` = dest-less unit call (mut path).
        let dest_parts: Option<(u64, crate::lean_name::LeanName, vir::ast::Typ)> =
            leaves.dest.as_ref().map(|(dname, dtyp)| {
                let chosen = self.fresh_let_name(dname.as_str());
                let dest_name = crate::lean_name::LeanName::synthetic(chosen);
                let dest_id = self.text_leaf(dest_name.as_str());
                // Record the dest binder at its Lean-level typ
                // (production's Phase-5 `with_let_binder(dest,
                // ret_typ_subst, true)`, every path) so downstream Var
                // reads coerce correctly (`.deref` on a Ref-typed call
                // result).
                self.let_binder_typs.insert(dest_name.clone(), (dtyp.clone(), true));
                (dest_id, dest_name, dtyp.clone())
            });
        // Hyp names in production PUSH order (bootstrap-74 slice 2):
        // per-mut-arg type bounds (Phase 1) take ordinals BEFORE the
        // ret-path hyps (Phases 2/3). Names never print in goals — every
        // goal containing mut frames is wrap-mode (the plain rebind
        // FLet) — but the ordinal stream must stay aligned for later
        // hoist goals' recounts.
        let mut_bound_names: Vec<Option<u64>> = leaves.mut_args.iter()
            .map(|m| m.bound.as_ref().map(|_| self.next_hyp_name()))
            .collect();
        let post = match leaves.post {
            CertCallPost::RetEq { e_bound, rest, dest_value } => {
                // Frame (outer→inner): [FHyp(E_bound)] [FHyp(rest)]
                // [FLet(rebind_i)…] FLet/FLetH/FLetR(dest, E). Built
                // innermost-out so E_bound ends up outermost — matching
                // `push_ret_frames`' push order (E_bound Hyp, then rest
                // Hyp, then Phase-4 rebinds, then Phase-5 dest Let).
                // Hyp names are assigned in PUSH order (bootstrap-74
                // slice 2): E_bound takes the earlier `_h_hoist_i`.
                let eb_name = if e_bound.is_some() { Some(self.next_hyp_name()) } else { None };
                let rest_name = if rest.is_some() { Some(self.next_hyp_name()) } else { None };
                let fnil = format!("{}.FrameList.FNil", NS);
                let (dest_id, dest_name, dest_typ) = dest_parts.as_ref()
                    .expect("ret-eq path requires dest (call-nodest-ret-eq guard)");
                let tail = self.dest_let_frame(*dest_id, dest_name, dest_typ, &dest_value, fnil)?;
                let mut post = self.wrap_mut_rebinds(&leaves.mut_args, tail);
                if let Some(rest) = rest {
                    let hp = self.hyp_poison(&rest);
                    if hp == 1 {
                        self.mark_poison_forced()?;
                    }
                    // F4: no SST source for this prop's deep — a real mention rejects loud.
                    self.guard_no_poison(hp, "call-post rest hyp")?;
                    let r = self.leaves.intern(pp_expr(&rest));
                    post = format!(
                        "({}.FrameList.FHyp {} {} {})",
                        NS, rest_name.unwrap(), r, box_(&post)
                    );
                }
                if let Some(eb) = e_bound {
                    let hp = self.hyp_poison(&eb);
                    if hp == 1 {
                        self.mark_poison_forced()?;
                    }
                    // F4: no SST source for this prop's deep — a real mention rejects loud.
                    self.guard_no_poison(hp, "call-post e_bound hyp")?;
                    let b = self.leaves.intern(pp_expr(&eb));
                    post = format!(
                        "({}.FrameList.FHyp {} {} {})",
                        NS, eb_name.unwrap(), b, box_(&post)
                    );
                }
                post
            }
            CertCallPost::Forall { ret_typ, ret_bound, ens, binder_name, dest_value, use_dest_name } => {
                // ∀-path (bootstrap-71; no callee `r == E` conjunct).
                // Frame (outer→inner): FBind(binder, ret_typ)
                // [FHyp(ret_bound)] [FHyp(ens)] [FLet(rebind_i)…]
                // [dest-let] — matching `push_ret_frames`' ∀-path push
                // order (binder, bound Hyp, ens Hyp) + the Phase-4
                // rebinds + the Phase-5 alias let, which is SKIPPED
                // when Approach A named the ∀-binder with the dest's
                // own name (`use_dest_name` ⟺ binder == dest) and
                // ABSENT for dest-less unit calls (mut path).
                // Hyp names in push order (ret_bound before ens).
                let rb_name = if ret_bound.is_some() { Some(self.next_hyp_name()) } else { None };
                let ens_name = if ens.is_some() { Some(self.next_hyp_name()) } else { None };
                let fnil = format!("{}.FrameList.FNil", NS);
                let tail = match dest_parts.as_ref() {
                    Some((dest_id, dest_name, dest_typ)) if !use_dest_name => {
                        self.dest_let_frame(*dest_id, dest_name, dest_typ, &dest_value, fnil)?
                    }
                    _ => fnil,
                };
                let mut post = self.wrap_mut_rebinds(&leaves.mut_args, tail);
                if let Some(e) = ens {
                    let hp = self.hyp_poison(&e);
                    if hp == 1 {
                        self.mark_poison_forced()?;
                    }
                    // F4: no SST source for this prop's deep — a real mention rejects loud.
                    self.guard_no_poison(hp, "call-post ens hyp")?;
                    let i = self.leaves.intern(pp_expr(&e));
                    post = format!(
                        "({}.FrameList.FHyp {} {} {})",
                        NS, ens_name.unwrap(), i, box_(&post)
                    );
                }
                if let Some(rb) = ret_bound {
                    let hp = self.hyp_poison(&rb);
                    if hp == 1 {
                        self.mark_poison_forced()?;
                    }
                    // F4: no SST source for this prop's deep — a real mention rejects loud.
                    self.guard_no_poison(hp, "call-post ret_bound hyp")?;
                    let b = self.leaves.intern(pp_expr(&rb));
                    post = format!(
                        "({}.FrameList.FHyp {} {} {})",
                        NS, rb_name.unwrap(), b, box_(&post)
                    );
                }
                let bn = self.text_leaf(binder_name.as_str());
                let ty = self.leaves.intern(pp_expr(&ret_typ));
                format!("({}.FrameList.FBind {} {} {})", NS, bn, ty, box_(&post))
            }
        };
        // Phase-1 mut frames OUTERMOST (production pushes them before
        // the ret frames): per arg, `FBind(fresh, declared typ)` +
        // optional `FHyp(bound)` — reverse iteration so the FIRST arg
        // ends outermost.
        let mut post = post;
        for (m, bname) in leaves.mut_args.iter().zip(mut_bound_names.iter()).rev() {
            if let Some(b) = &m.bound {
                let hp = self.hyp_poison(b);
                if hp == 1 {
                    self.mark_poison_forced()?;
                }
                // F4: no SST source for this prop's deep — a real mention rejects loud.
                self.guard_no_poison(hp, "call-post mut bound hyp")?;
                let bid = self.leaves.intern(pp_expr(b));
                post = format!(
                    "({}.FrameList.FHyp {} {} {})",
                    NS, bname.expect("name minted iff bound"), bid, box_(&post)
                );
            }
            let fname = self.text_leaf(m.fresh.as_str());
            let fty = self.leaves.intern(pp_expr(&m.binder_typ));
            post = format!("({}.FrameList.FBind {} {} {})", NS, fname, fty, box_(&post));
        }
        // The plain rebind FLets wrap-force every downstream goal
        // (production: `hoist_all` bails on the typ-less Phase-4 lets),
        // so shadow-freshening is off from here — same off-switch as
        // the mut-preamble/attr cases. Loop bodies restore the flag at
        // body end (post-loop frames drop body frames).
        if !leaves.mut_args.is_empty() {
            self.mark_flet_forced()?;
        }
        Ok(format!("({}.StmData.Call {} {})", NS, box_(&reqs), box_(&post)))
    }

    /// Phase-4 rebind frames (bootstrap-78 S3): one PLAIN `FLet(local,
    /// coerced fresh)` per `&mut` arg, wrapped innermost-out around
    /// `tail` in reverse arg order (first arg outermost) — production's
    /// `push_mut_rebinds` push order, typ-less `CtxFrame::Let` ⇒ plain
    /// FLet by construction (never FLetH/FLetR).
    fn wrap_mut_rebinds(
        &mut self,
        mut_args: &[crate::sst_to_lean::CertMutArg],
        tail: String,
    ) -> String {
        let mut post = tail;
        for m in mut_args.iter().rev() {
            let name = self.text_leaf(m.rebind_local.as_str());
            let val = self.leaves.intern(pp_expr(&m.rebind_value));
            post = format!("({}.FrameList.FLet {} {} {})", NS, name, val, box_(&post));
        }
        post
    }

    /// Serialize a `StmX::Loop` into the finding-3 `StmData.Loop` shape:
    /// the maintain/use telescopes production builds around a loop, made
    /// explicit so refWp can recompute them. Mirrors `sst_to_lean`'s
    /// `build_wp_loop` + `walk_loop` + `push_mod_var_frames` +
    /// `split_leading_binders` + `lex_decrease_obligation`. Every emitted
    /// leaf is byte-reconstructed via the SAME render path production
    /// uses, so matching leaves cancel across the W2 bridge.
    fn loop_stm(
        &mut self,
        cond: &Option<(Stm, Exp)>,
        original_cond: &Option<(Stm, Exp)>,
        body: &Stm,
        invs: &[LoopInv],
        decrease: &[Exp],
        loop_id: u64,
    ) -> Sr<String> {
        // Recover the while-condition from `cond` or the preserved
        // `original_cond` (break-lowering nulls `cond`). A genuine
        // `loop {}` (both None) has no cond leaf the mirror can carry.
        let cond_exp: &Exp = match (cond, original_cond) {
            (Some((_, c)), _) => c,
            (None, Some((_, c))) => c,
            (None, None) => return Err("loop-without-cond".to_string()),
        };
        // bootstrap-79: the canonical break-form — `loop_normalize`'s
        // output (cond: None, original_cond: Some((setup, exp)), body =
        // Block[setup-copy, If(¬exp, break, None), user-body], setup
        // non-empty). Mirror at the `original_cond` level (NO Break
        // arm): transcribe the setup ONCE from `original_cond`, walk the
        // USER body. Anything else with a Break keeps the loud
        // `break-or-continue` tag (genuine user break/continue — no
        // corpus population), including Verus-lowered user
        // while-with-breaks (their original_cond has an EMPTY setup —
        // production's `original_cond_recoverable` path renders vacuous
        // break-leaf goals the mirror does not yet model).
        let break_form: Option<(&Stm, &Stm)> = match (cond, original_cond, &body.x) {
            (None, Some((o_setup, _)), StmX::Block(ss))
                if ss.len() == 3
                    && !matches!(&o_setup.x, StmX::Block(es) if es.is_empty())
                    && matches!(&ss[1].x,
                        StmX::If(guard_cond, then_stm, None)
                            if matches!(&guard_cond.x, ExpX::Unary(UnaryOp::Not, _))
                                && matches!(&then_stm.x, StmX::BreakOrContinue { label: None, is_break: true })) =>
            {
                Some((o_setup, &ss[2]))
            }
            _ => None,
        };
        // Stage A: single-level `decreases` only. A multi-level lex
        // measure needs the full `lex_decrease_obligation` chain +
        // per-level d_old lets the flat mirror does not carry.
        if decrease.len() != 1 {
            return Err("loop-multilevel-decrease".to_string());
        }

        // Modified locals = production's RE-DERIVED havoc set, NOT the
        // (None) `StmX::Loop.modified_vars`: `collect_modifications(body)`
        // in body-traversal order, filtered to those with a `type_map`
        // entry (`build_wp_loop`:collect + `filter_map(type_map.get)`).
        let mut mod_names: Vec<&VarIdent> = Vec::new();
        let mut locally_declared: std::collections::HashSet<&VarIdent> =
            std::collections::HashSet::new();
        crate::sst_to_lean::collect_modifications(body, &mut locally_declared, &mut mod_names);

        // Hyp names are `_h_hoist_i` ordinals continuing the walk counter
        // (bootstrap-74 slice 2; S3-pre retired `_h_ctx_N` entirely —
        // `split_leading_binders` now replays the same scheme):
        // mod-var bounds first, then invariants, then the cond — the
        // maintain and use telescopes share them (sum_to evidence:
        // `_h_hoist_1..7` in both).

        // Havoc-set binders (id, typ leaf) + the parallel bound list.
        // Each modified local is re-quantified `∀ (x : T)`; an int-typed
        // one gets a `_h_hoist_i` type-bound hyp right after (production's
        // `push_mod_var_frames`, BARE `LExpr::var(name)` — no deref,
        // unlike params). The mod-var binders claim the SOURCE names
        // (production never freshens them) so body rebinds shadow.
        let mut binder_entries: Vec<(u64, u64)> = Vec::new();
        let mut bound_entries: Vec<Option<(u64, u64)>> = Vec::new();
        for vid in mod_names.iter() {
            // `filter_map(type_map.get)`: a mod name with no local-decl
            // typ is dropped (as production drops it), keeping `binders`
            // and `bound_entries` parallel.
            let Some(typ) = self.local_typs.get(*vid).cloned() else {
                continue;
            };
            let bid = self.binder_id(vid);
            let tleaf = self.typ_leaf(&typ);
            binder_entries.push((bid, tleaf));
            let name = crate::lean_name::LeanName::from_var_ident(vid);
            self.bound_names.insert(name.as_str().to_string());
            match crate::to_lean_sst_expr::type_bound_predicate(&LExpr::var(name.clone()), &typ) {
                Some(pred) => {
                    let hname = self.next_hyp_name();
                    let prop = self.leaves.intern(pp_expr(&pred));
                    bound_entries.push(Some((hname, prop)));
                }
                None => bound_entries.push(None),
            }
        }

        // Standard `invariant` clauses only (at_entry && at_exit). An
        // `invariant_except_break` (at_entry only) or loop-`ensures`
        // (at_exit only) needs the entry/exit distinction the flat shape
        // does not carry. Each becomes a `(_h_hoist_i name, ANNOTATED
        // obligation leaf)` — the annotated leaf serves BOTH the
        // init obligation AND the ∀-hyp (production reuses the one
        // span_mark'd `LoopInvariant` leaf for both roles, unlike
        // Assert's bare/annotated split). The maintain-RECLOSE
        // obligation is the RENAMED variant (`inv_obligs_exit`,
        // rendered after the body walk — the `i_hoist1 ≤ n` evidence).
        let mut inv_entries: Vec<(u64, u64)> = Vec::new();
        // W6d.2b: the parallel DEEP invariant obligation slots (index-aligned
        // with `inv_entries`). `oblig_slot` gives BOTH the opaque leaf id (for
        // the `inv_hyps` frame binder) AND the deep-or-atom `RawExp` slot (for
        // `inv_obligs`) — split only by role, never desynced.
        let mut inv_slots: Vec<String> = Vec::new();
        for li in invs.iter() {
            if !(li.at_entry && li.at_exit) {
                return Err("loop-nonstandard-invariant".to_string());
            }
            let hname = self.next_hyp_name();
            let (oblig, slot) = self.oblig_slot(&li.inv)?;
            inv_entries.push((hname, oblig));
            inv_slots.push(slot);
        }

        // Decreases snapshot let — an FLetH binder pair (the
        // `_tactus_d_old_<id>_0 : T` binder + its equation
        // `_h__tactus_d_old_<id>_0_hoist1 : _tactus_d_old_<id>_0 = D`,
        // maintain only) + the body-end decrease obligation. The measure
        // renders pre-body (the renames are not yet in effect —
        // `_tactus_d_old_0_0 = n - i`, NOT `n - i_hoist1`).
        let d_old_text = format!("_tactus_d_old_{}_0", loop_id);
        let d_old_name = self.text_leaf(&d_old_text);
        self.bound_names.insert(d_old_text.clone());
        let d_old_ty = self.typ_leaf(&decrease[0].typ);
        let d_old_val = self.exp_leaf(&decrease[0])?;
        let measure_lx = crate::to_lean_sst_expr::sst_exp_to_ast_checked(&decrease[0])
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let d_old_eq_name = self.text_leaf(&format!("_h_{}_hoist1", d_old_text));
        let d_old_eq_prop = self.leaves.intern(pp_expr(&LExpr::eq(
            LExpr::var(crate::lean_name::LeanName::synthetic(d_old_text.clone())),
            measure_lx,
        )));

        // W6d.2b: the parallel DEEP invariant obligations (`inv_obligs`,
        // index-aligned with `inv_hyps`). Each slot is `oblig_slot`'s output —
        // a deep `RawExp.Span(loc, raw)` for a coverable invariant (id in
        // `deep_ids`, so the goal walk deepens too), else `atom_ob(id)`. The
        // SAME id serves the opaque frame hyp (`inv_hyps`) and the deep
        // obligation (`inv_obligs`), split only by role, not by content.
        let inv_obligs = raw_exp_list(&inv_slots);
        let inv_hyps = self.binder_list(&inv_entries);
        let binders = self.binder_list(&binder_entries);
        let bounds = self.param_bound_list(&bound_entries);

        // The loop is a SCOPE boundary for hyp numbering (production's
        // per-goal-path ordinals — find_square evidence): the body's
        // own hyps (if conds, overflow assumes) number INSIDE the
        // loop's goals but do NOT advance the post-loop path — the
        // continuation resumes from the telescope end (`0 ≤ a + 1` in
        // the outer body gets `_h_hoist_10` right after the inner
        // loop's `_h_hoist_5..9`, while the inner body's own hyps
        // number from the same point).
        // Counter mirror: production emits the ENTRY invariant theorems
        // (one per inv) at the loop head, BEFORE walking the body
        // (fill_zeros: entry 2,3,4 precede the in-body call's 5,6).
        self.consume_theorem_ids(invs.len() as u64);
        // Wrap-latch scope (bootstrap-78 S3): a plain FLet inside the
        // body (a mut-call rebind) wrap-forces the BODY's downstream
        // goals only — production's post-loop frames drop body frames,
        // so post-loop goals hoist (and freshen) again (fill_zeros
        // `v_hoist1` Ret evidence). Restore alongside `hyp_ordinal`.
        let flet_forced_save = self.flet_forced;
        // bootstrap-79 break-form: walk the setup ONCE from
        // `original_cond` (the body-run side — consumes the setup's
        // emit ordinals and hyp names, applies the setup's renames),
        // derive the exit-reclose obligations at the post-setup rename
        // state, and consume the exit-reclose theorems (production's
        // break leaf emits between the setup run and the user-body
        // walk: count_to_len ids 2 [call], 3 [exit-reclose]). The
        // restore point for the post-loop path is PRE-setup (the exit
        // replay re-walks the setup — its hyps renumber from there).
        let (setup_term, inv_obligs_break, pre_setup_ordinal) = if let Some((o_setup, _)) = break_form {
            let pre = self.hyp_ordinal;
            let setup_term = self.stm(o_setup)?;
            let break_slots = self.renamed_inv_slots(invs, &inv_slots)?;
            self.consume_theorem_ids(invs.len() as u64);
            (setup_term, raw_exp_list(&break_slots), pre)
        } else {
            (self.skip(), raw_exp_list(&[]), 0)
        };
        // The guard/cond leaves — shared position: post-setup for the
        // break-form (the setup rebinds no mod var in the common case,
        // so this coincides with the classical pre-body state), pre-body
        // for classical. One shared `_h_hoist_i` name for every
        // cond-flavored hyp (the maintain hyp `cond_ann` / use hyp
        // `neg_cond_ann` for classical; the exit-reclose / maintain /
        // post-loop guards for break-form — per-goal-path ordinals
        // coincide since the d_old eq-hyp is name-based); plus the
        // cond's poison bit (a cond mentioning a residue let forces
        // whole-goal wrap).
        let cond_name = self.next_hyp_name();
        let cond_ann = self.oblig_leaf(cond_exp)?;
        let (neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann) =
            if break_form.is_some() {
                (
                    // The classical use-hyp shape `¬(/- …-/ cond)` does not
                    // occur in break-form goals (the exit_wrap hyp is the
                    // BARE `¬cond` — `break_use_ann`).
                    999999,
                    self.neg_neg_oblig_leaf(cond_exp)?,
                    self.marked_neg_cond_leaf(cond_exp)?,
                    self.bare_neg_cond_leaf(cond_exp)?,
                )
            } else {
                (self.neg_oblig_leaf(cond_exp)?, 999999, 999999, 999999)
            };
        let cond_inner_raw = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
            cond_exp,
            &self.render_ctx(),
        )
        .map_err(|reason| format!("leaf-render: {}", reason))?;
        let cond_poison = self.hyp_poison(&self.apply_renames(&cond_inner_raw));
        if cond_poison == 1 {
            self.mark_poison_forced()?;
        }
        // F4: register the deeps for every cond-flavored prop (the
        // shared bit covers all five — c / ¬c / ¬¬c / the break guard
        // and use hyps — all with the same mention set). The 999999
        // sentinels (shapes absent from this loop form) are skipped.
        for prop_id in [cond_ann, neg_cond_ann, neg_neg_cond_ann, break_guard_ann, break_use_ann] {
            if prop_id != 999999 {
                self.register_prop_deep(prop_id, cond_exp, cond_poison)?;
            }
        }
        // The restore point: classical = the telescope end (post-cond);
        // break-form = PRE-setup (the exit replay re-walks the setup for
        // the post-loop goals — its hyps renumber from there, e.g.
        // count_to_len's postcondition `_h_hoist_3` bound hyp).
        let loop_counter_end = if break_form.is_some() { pre_setup_ordinal } else { self.hyp_ordinal };
        let walk_body: &Stm = match break_form {
            Some((_, user_body)) => user_body,
            None => body,
        };
        let body_term = self.stm(walk_body)?;
        self.hyp_ordinal = loop_counter_end;
        self.flet_forced = flet_forced_save;
        // Counter mirror: MAINTAIN theorems (one per inv) + the DECREASE
        // theorem, consumed after the body walk (fill_zeros: 8,9,10 then
        // 11). `decrease.len() == 1` is enforced above; nonstandard
        // invariants fail loud above, so |invs| is exact by construction.
        self.consume_theorem_ids(invs.len() as u64 + 1);

        // The body-end decrease obligation — rendered AFTER the body
        // walk so the shadow renames apply to the measure
        // (`0 ≤ n - i_hoist1 ∧ …`, NOT the loop-entry `n - i` the
        // d_old value keeps).
        let decrease_oblig = self.decrease_oblig_leaf(&decrease[0], loop_id)?;

        // The maintain-RECLOSE obligations (Round D): the invariant
        // texts with the body's shadow renames applied
        // (`i_hoist1 ≤ n`, `Int.toNat acc_hoist1 = lib.tri (Int.toNat
        // i_hoist1)` — fresh leaf ids, distinct from the init
        // obligations' plain texts).
        let inv_obligs_exit = raw_exp_list(&self.renamed_inv_slots(invs, &inv_slots)?);

        // Loop exit: the use telescope re-binds the mod-vars under their
        // SOURCE names, so the shadow renames for them end here
        // (post-loop references are plain again — `r = acc`).
        for vid in mod_names.iter() {
            let name = crate::lean_name::LeanName::from_var_ident(vid);
            self.rename_env.remove(name.as_str());
        }

        // bootstrap-79 break-form EXIT REPLAY: production's exit_wrap
        // re-walks the setup around the post-loop continuation
        // (`build_wp_loop`: build_wp(cond_setup, Hyp(¬cond, after))), so
        // the setup's calls consume their OWN emit ordinals (count_to_len
        // id 7, copy_word id 20) and its hyps number per the post-loop
        // path (the len bound is `_h_hoist_3` again, then the bare-¬cond
        // exit hyp — the SAME ordinal as the walk guard `cond_name`,
        // since both are the first hyp minted after the setup frames on
        // their respective paths). Replay the walk for those counter
        // effects only: the output is discarded (the Loop node carries
        // ONE setup transcription; refWp derives both renderings) and the
        // name/rename state is restored (the exit replay is a fresh goal
        // path — production does NOT freshen tmp__2/tmp__1 there).
        if let Some((o_setup, _)) = break_form {
            let save_renames = self.rename_env.clone();
            let save_bound = self.bound_names.clone();
            let _replay_term = self.stm(o_setup)?;
            let replay_guard = self.next_hyp_name();
            if replay_guard != cond_name {
                return Err("loop-break-form-replay-drift".to_string());
            }
            self.rename_env = save_renames;
            self.bound_names = save_bound;
        }

        Ok(format!(
            "({}.StmData.Loop {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {})",
            NS,
            box_(&inv_hyps),
            box_(&inv_obligs),
            box_(&inv_obligs_exit),
            box_(&inv_obligs_break),
            box_(&binders),
            box_(&bounds),
            cond_name,
            cond_ann,
            neg_cond_ann,
            neg_neg_cond_ann,
            break_guard_ann,
            break_use_ann,
            d_old_name,
            d_old_ty,
            d_old_val,
            d_old_eq_name,
            d_old_eq_prop,
            // W6d.2a: decrease_oblig is now a DEEP `RawExp` (like Assert);
            // opaque fallback wraps the synthesized `0 ≤ D ∧ D < d_old` leaf id.
            atom_ob_lit(decrease_oblig),
            box_(&setup_term),
            box_(&body_term),
        ))
    }

    // ── List builders ───────────────────────────────────────────────

    /// `lib.LeafList` from a slice of ids (order preserved).
    fn leaf_list(&self, ids: &[u64]) -> String {
        let mut term = format!("{}.LeafList.Nil", NS);
        for &id in ids.iter().rev() {
            term = format!("{}.LeafList.Cons {} {}", NS, id, box_(&term));
        }
        term
    }

    /// F4: `lib.PropDeepList` from the registered (prop leaf id, deep
    /// `RawExp` text) pairs (order preserved — walk order).
    fn prop_deep_list(&self) -> String {
        let mut term = format!("{}.PropDeepList.Nil", NS);
        for (id, raw) in self.prop_deeps.iter().rev() {
            term = format!("{}.PropDeepList.Cons {} {} {}", NS, id, box_raw(raw), box_(&term));
        }
        term
    }

    /// `lib.BinderList` from (id, typ-leaf) pairs (order preserved).
    fn binder_list(&self, pairs: &[(u64, u64)]) -> String {
        let mut term = format!("{}.BinderList.Nil", NS);
        for &(id, typ) in pairs.iter().rev() {
            term = format!("{}.BinderList.Cons {} {} {}", NS, id, typ, box_(&term));
        }
        term
    }

    /// `lib.ParamBoundList` from per-param optional `(name, prop)` leaves
    /// (order preserved). `Some((name, prop))` ⇒ `Bound name prop` — a NAMED
    /// ∀-binder `∀ (h_x_bound : prop)` (finding-2); `None` ⇒ `NoBound`.
    fn param_bound_list(&self, bounds: &[Option<(u64, u64)>]) -> String {
        let mut term = format!("{}.ParamBoundList.Nil", NS);
        for b in bounds.iter().rev() {
            term = match b {
                Some((name, prop)) => format!("{}.ParamBoundList.Bound {} {} {}", NS, name, prop, box_(&term)),
                None => format!("{}.ParamBoundList.NoBound {}", NS, box_(&term)),
            };
        }
        term
    }

    /// `lib.MutParamList` from `(param, at_pre, deref-value)` leaf
    /// triples (order preserved) — the `&mut`-param fn-entry preamble
    /// entries (bootstrap-78 S2).
    fn mut_param_list(&self, entries: &[(u64, u64, u64)]) -> String {
        let mut term = format!("{}.MutParamList.Nil", NS);
        for &(p, at_pre, dv) in entries.iter().rev() {
            term = format!("{}.MutParamList.Cons {} {} {} {}", NS, p, at_pre, dv, box_(&term));
        }
        term
    }

    // ── Goal walk (GoalData / GoalList literal) — N3b ────────────────

    /// Intern an already-built `LExpr` (a goal-spine leaf) by its
    /// production-rendered text — the SAME `pp_expr` path SST leaves use,
    /// so a goal leaf whose text matches an SST leaf reuses that id and
    /// the two cancel across the bridge (§4).
    fn lexpr_leaf(&mut self, e: &LExpr) -> u64 {
        self.leaves.intern(pp_expr(e))
    }

    /// Binder-name id for a spine `∀` node = the interned leaf of the
    /// binder's source name (`_` for an anonymous / instance binder).
    /// Same binder-id caveat as `binder_id` — refWp's only consumers
    /// (`goal_size`/`goal_count`) ignore the value.
    fn goal_binder_name_leaf(&mut self, b: &crate::lean_ast::Binder) -> u64 {
        match &b.name {
            Some(n) => self.text_leaf(n.as_str()),
            None => self.text_leaf("_"),
        }
    }

    /// Render one obligation's [`GoalShape`] as a `lib.GoalData` term. The
    /// spine is OUTERMOST-first, so fold from the core `Leaf` outward
    /// (reverse spine). Interning order within a goal is therefore
    /// core-leaf-then-inner-to-outer — arbitrary but deterministic, which
    /// is all §4/acceptance §3 require of the goal half (the leaf table is
    /// audit-only; the bridge never reads id values).
    fn goal_data(&mut self, shape: &GoalShape) -> String {
        // Residue-let peel (bootstrap-74 slice 2): production's partial
        // hoist folds Bool-typed residue lets AROUND the leaf
        // (`let tmp__1 := s < 2000; <annotated leaf>`), and the ref side
        // emits them structurally as `GoalData::Let` via `residue_fold_e`.
        // Peel them here (outermost first) so both sides agree: the
        // binder id is the name's interned text, the value leaf the
        // interned value text — the same ids the FLetR frame carries.
        let mut residue: Vec<(&crate::lean_name::LeanName, &LExpr)> = Vec::new();
        let mut core = &shape.leaf;
        while let ExprNode::Let { name, value, body } = &core.node {
            residue.push((name, value));
            core = body;
        }
        let leaf_id = self.lexpr_leaf(core);
        // W6d.2b emit gate — deepen the goal's core leaf into
        // `LeafE(ExprData…)` ONLY when the matching obligation went DEEP on the
        // reference side (`deep_ids`, the "ob-drives" coordination — populated
        // by the whole stm walk, which runs before this) AND the goal-side
        // transcription `lexpr_to_exprdata(shape.leaf)` succeeds. Then the
        // bridge `decide`s `expr_eq(render_exp(rawExp), lexpr(leaf))` — the
        // Friction-2 catcher. Otherwise the opaque `Atom(id)` fallback (the
        // W6d.2a verdict-neutral behavior), matching refWp's `atom_ob(id)` by
        // the same interned id. A `deep_ids`-hit whose `lexpr_to_exprdata`
        // FAILS (ref-deep, goal-atom) makes this fn's bridge fail — sound
        // (never a silent pass), only a coverage loss for that fn.
        let atom_core =
            || format!("{}.GoalData.LeafE ({}.ExprData.Atom {})", NS, NS, leaf_id);
        let mut term = if self.deep_ids.contains(&leaf_id) {
            match self.lexpr_to_exprdata(core) {
                Ok(ed) => format!("{}.GoalData.LeafE {}", NS, ed),
                Err(_) => atom_core(),
            }
        } else {
            atom_core()
        };
        // Wrap the residue lets back around the core, INNERMOST first —
        // the outermost residue let ends up outermost (frame order,
        // matching residue_fold_e).
        for (n, v) in residue.into_iter().rev() {
            let name = self.text_leaf(n.as_str());
            let val = self.lexpr_leaf(v);
            term = format!("{}.GoalData.Let {} {} {}", NS, name, val, box_(&term));
        }
        for node in shape.spine.iter().rev() {
            term = match node {
                GoalSpine::Imp(p, _) => {
                    let h = self.lexpr_leaf(p);
                    format!("{}.GoalData.Imp {} {}", NS, h, box_(&term))
                }
                GoalSpine::All(b, _) => {
                    let name = self.goal_binder_name_leaf(b);
                    let typ = self.lexpr_leaf(&b.ty);
                    format!("{}.GoalData.All {} {} {}", NS, name, typ, box_(&term))
                }
                GoalSpine::Let(n, v) => {
                    let name = self.text_leaf(n.as_str());
                    let val = self.lexpr_leaf(v);
                    format!("{}.GoalData.Let {} {} {}", NS, name, val, box_(&term))
                }
            };
        }
        paren(&term)
    }

    /// The production `lib.GoalList` — one `GoalData` per WP obligation in
    /// emit (= production theorem) order. Obligations whose spine is
    /// `None` (bit_vector/query stage-A exclusions) are skipped. Returns
    /// the list term plus the included obligations' theorem names, in the
    /// same order, for the O4 per-goal audit comments (§6).
    fn goal_list(
        &mut self,
        theorems: &[Theorem],
        shapes: &[Option<GoalShape>],
    ) -> (String, Vec<String>) {
        let mut terms: Vec<String> = Vec::new();
        let mut names: Vec<String> = Vec::new();
        for (thm, shape) in theorems.iter().zip(shapes.iter()) {
            if let Some(shape) = shape {
                names.push(thm.name.clone());
                terms.push(self.goal_data(shape));
            }
        }
        // W4c red-path pin (b68): deliberate drift injection. The gate
        // re-emits certs from SST every run, so an on-disk edit never
        // reaches the bridge — the red channel needs an emission-side
        // hook. Two goals are the minimum for a swap to change the
        // list (the e2e pin uses an assert + postcondition fn).
        if self.perturb_goals && terms.len() >= 2 {
            terms.swap(0, 1);
        }
        let mut term = format!("{}.GoalList.Nil", NS);
        for t in terms.iter().rev() {
            term = format!("{}.GoalList.Cons {} {}", NS, box_(t), box_(&term));
        }
        (term, names)
    }
}

// ── Top-level: build the certificate for one fn ─────────────────────

/// The pieces of a serialized fn, assembled into the cert file text.
struct CertBody {
    /// The `FnCtxData` seed as a Lean term.
    ctx_term: String,
    /// The `StmData` body as a Lean term.
    stm_term: String,
    /// N3b: the production `GoalList` literal (the goal spines refWp's
    /// result is compared against at the W2 bridge). `GoalList.Nil` +
    /// empty `goal_names` when no obligation carried a spine.
    goal_term: String,
    /// N3b: production theorem names for the emitted goals, in `GoalList`
    /// order — one per `Cons`, for the O4 per-goal audit comment (§6).
    goal_names: Vec<String>,
    /// The interned leaf table, in id order.
    leaf_texts: Vec<String>,
}

/// Serialize `(fn_sst, check)` plus the production obligation goals into
/// a [`CertBody`], or `Err(tag)` on the first uncaptured construct.
///
/// `theorems` / `goal_shapes` are the index-aligned output of
/// `exec_fn_theorems_to_ast` (N3b): the goal spines interned into the
/// SAME leaf table as the SST half, appended AFTER the SST walk so SST
/// leaf ids stay in their §4 first-appearance order and matching goal
/// leaves reuse them.
fn serialize<'a>(
    krate: &'a KrateX,
    fn_sst: &FunctionSst,
    // `'a`: the AssertByVar map borrows local_decls for the
    // serializer's lifetime (A6-short).
    check: &'a FuncCheckSst,
    theorems: &[Theorem],
    goal_shapes: &[Option<GoalShape>],
) -> Sr<CertBody> {
    let mut s: Serializer<'a> = Serializer::default();

    // W4c red-path pin (b68): test-only drift injection, off unless the
    // TACTUS_BRIDGE_PERTURB env knob names this fn.
    s.perturb_goals = bridge_perturb_matches(short_name(&fn_sst.x.name.path));

    // Wrap-mode mirror (endgame A2): the SHARED closer gate — a user
    // `tactus_tactic` / proof-block prefix means production never
    // hoists this fn's goals; every let classifies plain and the
    // shadow-freshening is off from the start (production's
    // `rename_frame_vars` only runs inside `hoist_all`).
    s.wrap_mode = !crate::sst_to_lean::closer_is_default(fn_sst, check);
    s.attr_user_closer = fn_sst.x.attrs.tactus_tactic.is_some();
    if s.attr_user_closer {
        // Freshening runs only inside `hoist_all`; an attr fn's goals
        // never hoist. (A proof-block-only fn's goals DO hoist, so its
        // freshening stays live — b77 proof_block_fn evidence.)
        s.mark_flet_forced()?;
    }

    // Assert-forall skolem map (endgame A6-short) — built EXACTLY as
    // `WpCtx::new`'s `assert_by_var_typs`; the DeadEnd arm rejects when
    // a scope references one.
    s.assert_by_var_typs = check
        .local_decls
        .iter()
        .filter(|d| matches!(d.kind, vir::sst::LocalDeclKind::AssertByVar { .. }))
        .map(|d| (&d.ident, &d.typ))
        .collect();

    // fn_map for `render_ctx()` (bootstrap-18) — built EXACTLY as
    // production's (sst_to_lean.rs:503): borrows the krate for the
    // serializer's lifetime. Callee resolution puts plain-spec-fn calls in
    // obligations on the migrated typed-arg path so `&`-param call args
    // deref (head_exec's `tree_head(*t)` → `tree_head t.deref`).
    s.fn_map = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();

    // Datatypes by path (bootstrap-77 A5) — built EXACTLY as
    // `WpCtx::new`'s map; the N2 ctor-frame mirror reads it.
    s.dt_map = krate
        .datatypes
        .iter()
        .filter_map(|d| match &d.x.name {
            vir::ast::Dt::Path(p) => Some((p, &d.x)),
            _ => None,
        })
        .collect();

    // Value params at body-shadow Lean typ (bootstrap-18) — built EXACTLY
    // as production's `caller_param_typs` (sst_to_lean.rs,
    // exec_fn_theorems_to_ast): strip one outer ref decoration for
    // `&mut`-style params, else as-declared. Set before any leaf render so
    // `render_ctx()` derefs `&`-params consistently across obligation and
    // RetBind-value leaves.
    s.caller_param_typs = fn_sst
        .x
        .pars
        .iter()
        .map(|p| {
            let typ = if crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut) {
                crate::to_lean_expr::strip_one_ref_decoration(&p.x.typ)
            } else {
                p.x.typ.clone()
            };
            (p.x.name.clone(), typ)
        })
        .collect();

    // Walk order (§4): params → requires → body → ensures. Interning in
    // this order fixes leaf ids deterministically.

    // Type params: (name-binder-id, `Type` kind leaf).
    let mut typ_param_entries: Vec<(u64, u64)> = Vec::new();
    for tp in fn_sst.x.typ_params.iter() {
        let id = s.text_leaf(tp.as_str());
        let kind = s.text_leaf("Type");
        typ_param_entries.push((id, kind));
    }

    // Value params (skip Verus-synthetic `%`-named ones): binder-id +
    // typ leaf, plus the parallel optional bound-hyp `(name, prop)`.
    let mut param_entries: Vec<(u64, u64)> = Vec::new();
    let mut param_bounds: Vec<Option<(u64, u64)>> = Vec::new();
    for p in fn_sst.x.pars.iter().filter(|p| !p.x.name.0.contains('%')) {
        let id = s.binder_id(&p.x.name);
        let typ = s.param_typ_leaf(&p.x.typ, p.x.is_mut);
        param_entries.push((id, typ));
        // `type_bound_predicate` over the (possibly deref'd) param value
        // decides whether an `h_x_bound` hypothesis exists.
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        let is_mut_ref = crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut);
        let bound_value = if is_mut_ref {
            LExpr::field_proj(LExpr::var(name.clone()), "deref")
        } else {
            LExpr::var(name.clone())
        };
        match crate::to_lean_sst_expr::type_bound_predicate(&bound_value, &p.x.typ) {
            Some(pred) => {
                let prop = s.leaves.intern(pp_expr(&pred));
                // The bound hyp renders as a NAMED ∀-binder; production mints
                // the name as `h_<param>_bound` (sst_to_lean::build_param_binders).
                // Intern the identical text so the goal-walk binder-name leaf
                // (goal_binder_name_leaf) unifies with this one (finding-2).
                let hname = s.text_leaf(&format!("h_{}_bound", name.as_str()));
                param_bounds.push(Some((hname, prop)));
            }
            None => param_bounds.push(None),
        }
    }

    // Requires: `(h_req<i>, prop)` pairs — production renders each as a NAMED
    // ∀-binder `∀ (h_req0 : x < 1000)` (sst_to_lean::build_req_binders), so
    // reqs is a BinderList, not a leaf list (finding-2). The `h_req<i>` name
    // text matches production's `format!("h_req{}", i)`.
    // Leaf TEXT via production's own `build_req_binders` (endgame A2):
    // the fn_map ctx + mut-ref rewrite + shadow prefix produce e.g. the
    // view-arg auto-ref coercion (`Ref.mk h.deref.generator_images`)
    // that a bare render misses — the req prop must byte-match
    // production's base-binder ty or refWp's seed hyp diverges.
    let mut_param_names: std::collections::HashSet<String> = {
        let mut m: std::collections::HashSet<String> = fn_sst.x.pars.iter()
            .filter(|p| crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut))
            .map(|p| crate::to_lean_type::sanitize(&p.x.name.0))
            .collect();
        for decl in check.local_decls.iter() {
            if matches!(decl.kind, vir::sst::LocalDeclKind::BorrowMut) {
                m.insert(crate::to_lean_type::sanitize(&decl.ident.0));
            }
        }
        m
    };
    // The same set feeds the Call arm's mut-target extraction
    // (bootstrap-78 S3) — set BEFORE the body walk below.
    s.mut_ref_locals = mut_param_names.clone();
    let mut req_entries: Vec<(u64, u64)> = Vec::new();
    for (i, b) in crate::sst_to_lean::build_req_binders(fn_sst, check, &mut_param_names, &s.fn_map)
        .iter()
        .enumerate()
    {
        let prop = s.leaves.intern(pp_expr(&b.ty));
        let hname = s.text_leaf(&format!("h_req{}", i));
        req_entries.push((hname, prop));
    }

    // `&mut`-param fn-entry preamble entries → `FnCtxData.mut_params`
    // (bootstrap-78 S2). Mirrors production's initial-OblCtx loop
    // (sst_to_lean ~1526): per mut-ref PAR then per `BorrowMut` local,
    // in declaration order — (param name, `<p>_at_pre_tactus` name,
    // interned `<p>.deref` value text). refWp derives the two typ-less
    // frame lets per entry (`mut_preamble_frame`); their plainness
    // trips the wrap gate exactly as production's `hoist_all` bails on
    // the typ-less `CtxFrame::Let`s.
    let mut mut_names: Vec<(crate::lean_name::LeanName, String)> = Vec::new();
    for par in fn_sst.x.pars.iter() {
        if crate::expr_shared::is_mut_ref_typ(&par.x.typ, par.x.is_mut) {
            mut_names.push((
                crate::lean_name::LeanName::from_var_ident(&par.x.name),
                crate::to_lean_type::sanitize(&par.x.name.0),
            ));
        }
    }
    for decl in check.local_decls.iter() {
        if matches!(decl.kind, vir::sst::LocalDeclKind::BorrowMut) {
            mut_names.push((
                crate::lean_name::LeanName::from_var_ident(&decl.ident),
                crate::to_lean_type::sanitize(&decl.ident.0),
            ));
        }
    }
    let mut mut_entries: Vec<(u64, u64, u64)> = Vec::new();
    for (lean_name, raw_name) in mut_names.iter() {
        let p = s.text_leaf(lean_name.as_str());
        let at_pre = s.text_leaf(&crate::expr_shared::varat_pre_name(raw_name));
        let deref_val = s.leaves.intern(pp_expr(&LExpr::field_proj(
            LExpr::var(lean_name.clone()),
            "deref",
        )));
        mut_entries.push((p, at_pre, deref_val));
    }
    if !mut_entries.is_empty() {
        // Every goal of a mut-param fn wraps (production's hoist bail),
        // so the shadow-freshening never runs — same off-switch as the
        // attr-fn case (`rename_frame_vars` only runs inside hoist_all).
        s.mark_flet_forced()?;
    }

    // Shadow-mirror seed (bootstrap-74 slice 2 Round D): production's
    // `taken_names` = the base binders — value params, their `h_<p>_bound`
    // names, and the `h_req<i>` names (sst_to_lean.rs:2499-2503).
    for p in fn_sst.x.pars.iter().filter(|p| !p.x.name.0.contains('%')) {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        s.bound_names.insert(name.as_str().to_string());
        s.bound_names.insert(format!("h_{}_bound", name.as_str()));
    }
    for i in 0..check.reqs.len() {
        s.bound_names.insert(format!("h_req{}", i));
    }

    // Ensures leaves — from the ENSURES-PHASE mut-ref-rewritten exps
    // (bootstrap-78 S3, the inc pinpoint): production's `WpCtx::new`
    // canonicalizes every ens BEFORE rendering (`VarAt(x, Pre)` /
    // `MutRefCurrent(x)` → `Var(<x>_at_pre_tactus)`, post-state forms →
    // `Var(x)`), so its goal leaf reads `x = x_at_pre_tactus + 1` while
    // the raw exp would render `x = x + 1` — the ref side must rewrite
    // identically or the Ret obligation leaf diverges. Identity for fns
    // without mut params/BorrowMut locals (`mut_param_names` empty ⇒
    // no shapes match), so non-mut certs are byte-stable.
    let ens_rewritten: Vec<Exp> = check.post_condition.ens_exps.iter()
        .map(|e| crate::mut_ref_normalize::rewrite_mut_ref_in_exp(
            e,
            &mut_param_names,
            crate::mut_ref_normalize::RewritePhase::Ensures,
        ))
        .collect();

    // Ensures leaves (bare) → `FnCtxData.enss`. refWp does NOT read this
    // slot (the `Return` goal uses the annotated obligations below); it is
    // kept for the fall-through documentation + O4 audit.
    let mut ens_leaves: Vec<u64> = Vec::new();
    for e in ens_rewritten.iter() {
        ens_leaves.push(s.exp_leaf(e)?);
    }
    // Annotated ensures obligation SLOTS → the `Return` goal
    // (Ret-annotation, finding-1): production renders each ensures at the
    // return site as a span_mark'd `Postcondition` obligation
    // (`WpCtx::new`); `oblig_slot` reconstructs the identical span_mark'd leaf
    // text (so the goal-side postcondition leaf reuses this id and the two
    // cancel across the W2 bridge) AND, when the ensures is coverable, emits
    // the DEEP `RawExp.Span(loc, raw)` (id → `deep_ids`, so the goal walk
    // deepens too). Built here (before the body) so the Ret arm stays a plain
    // read of `pending_ens_oblig`; the raw_exp atoms intern in ensures order,
    // exactly where the old `oblig_leaf` interned the span_mark'd leaf.
    let mut ens_oblig: Vec<String> = Vec::new();
    let mut ens_marked: Vec<LExpr> = Vec::new();
    let mut ens_all_deep = true;
    for e in ens_rewritten.iter() {
        let (id, slot) = s.oblig_slot(e)?;
        // `oblig_slot` inserts `id` into `deep_ids` iff it emitted a deep
        // `RawExp.Span` (else an `atom_ob` fallback). The G4 Return-lift
        // recompute conjoins these slots into the branch-folded leaf, which
        // is only faithful when every ensures is a real `Span` (an `atom_ob`
        // conjunct would render to `Atom` and diverge from the goal side).
        ens_all_deep &= s.deep_ids.contains(&id);
        ens_marked.push(s.marked_oblig_lexpr(e)?);
        ens_oblig.push(slot);
    }
    s.pending_ens_all_deep = ens_all_deep;
    s.pending_ens_oblig = ens_oblig;
    s.pending_ens_marked = ens_marked;
    // Return-var name leaf (finding-4): production binds `let <sanitize(ret)>
    // := <e>` before the postcondition (the `Return` walker's
    // `let_bind_synthetic(sanitize(name), …)`). `dest` is the declared
    // `-> (r: T)` name; `None` (unit return) ⇒ no binding.
    s.pending_ret_name = check
        .post_condition
        .dest
        .as_ref()
        .map(|d| s.text_leaf(&crate::to_lean_type::sanitize(d.0.as_str())));
    // The SAME name, kept as text for the RetLetH equation pair
    // (bootstrap-74 slice 2).
    s.pending_ret_lname = check
        .post_condition
        .dest
        .as_ref()
        .map(|d| crate::to_lean_type::sanitize(d.0.as_str()));

    // Local-decl typ map (finding-3): the `Loop` arm re-derives its
    // modified-local havoc set from the body and looks up each var's typ
    // here — the SAME source production's `WpCtx.type_map` uses
    // (`check.local_decls`, `sst_to_lean.rs`). Cloned (owned) so the
    // statement recursion stays a plain `&Stm → String` walk over `&mut
    // self` without threading `check` through every arm.
    s.local_typs = check
        .local_decls
        .iter()
        .map(|d| (d.ident.clone(), d.typ.clone()))
        .collect();

    // Declared return typ (bootstrap-18) — mirrors production's
    // `WpCtx.ret_typ` (sst_to_lean.rs:524): the `post_condition.dest`
    // VarIdent looked up in `local_typs` (production's `type_map`). Used by
    // the `Return` arm to coerce the return value to this typ (inserting a
    // `&`-value `.deref`), exactly as production's per-leaf return-typ
    // coercion. Must be set AFTER `local_typs`.
    s.ret_typ = check
        .post_condition
        .dest
        .as_ref()
        .and_then(|dest| s.local_typs.get(dest).cloned());

    // Body — the LOOP-NORMALIZED tree, the same one production walks
    // (decision #2 follow-up, 2026-07-26). `normalize_setup_loops` is
    // the identity on every body without a setup-carrying `while`, so
    // existing certs are byte-identical; setup-carrying whiles arrive
    // here in Verus's own break form (cond:None + guard in body),
    // which the Loop arm already models — instead of a cond:Some
    // shape refWp would otherwise have to learn to normalize itself.
    // TCB note: like leaf rendering and `cert_call_leaves`, the
    // normalization joins the TRUSTED transcription surface — the
    // structural decide-check validates the WP of the normalized
    // program, taking the (pure, shared-code) pre-pass on faith. See
    // the faithfulness contract above.
    let normalized_body = crate::loop_normalize::normalize_setup_loops(&check.body);
    let stm_term = s.stm(&normalized_body)?;

    // G4/W6e — seed `deep_ids` for the value-if-lift goal leaves. The Return
    // arm recomputed the branch-folded obligations on the REFERENCE side
    // (`Ret([impl…], RetNone)`); the goal side must deepen the matching leaves
    // so `goal_data` emits `LeafE(lexpr_to_exprdata(leaf))` (not `Atom`). Those
    // leaves are `Implies`-topped whole implications (NOT the bare `SpanMark`
    // ensures `oblig_slot` already seeded) — production's `emit_done_or_split`
    // splits the top `And` but leaves each `Implies` intact, so its id was
    // never in `deep_ids`. We seed straight from the ACTUAL production goal
    // shapes (`goal_shapes`), so the id matches `goal_data`'s `lexpr_leaf` by
    // construction. Gated on a successful recompute (`lifted_return_recomputes
    // > 0`) so a fn with no lift is untouched (verdict-neutral); a leaf whose
    // transcription FAILS is skipped (goal stays `Atom` → that fn honest-fails,
    // same as before — never a NEW regression, since a lifted return already
    // honest-failed on the plain path).
    if s.lifted_return_recomputes > 0 {
        for shape in goal_shapes.iter().flatten() {
            if matches!(
                &shape.leaf.node,
                ExprNode::BinOp { op: LBinOp::Implies, .. }
            ) && s.lexpr_to_exprdata(&shape.leaf).is_ok()
            {
                let id = s.lexpr_leaf(&shape.leaf);
                s.deep_ids.insert(id);
            }
        }
    }

    // Assemble the FnCtxData term. `.mk` positional order matches the
    // emitted `structure lib.FnCtxData`: typ_params, params, param_bounds,
    // reqs, mut_params, enss, residue_names, prop_deeps, closer_default.
    // The closer bit (R1,
    // bootstrap-77) seeds refWp's `FUserCloser` wrap-forcer — the
    // fn-level `closer_is_default` DFS (attr + proof-block prefix)
    // rendered as data instead of the retired all-lets-plain collapse.
    // F4 (bootstrap-80 stage 2): residue_names + prop_deeps feed refWp's
    // poison derivation (`poisoned_props`) — the era-1 bit slots ride
    // along unread until era-2 deletion.
    let residue_names = s.residue_names.clone();
    let residue_ids: Vec<u64> = residue_names
        .iter()
        .map(|n| s.text_leaf(n))
        .collect();
    let ctx_term = format!(
        "({}.FnCtxData.mk {} {} {} {} {} {} {} {} {})",
        NS,
        paren(&s.binder_list(&typ_param_entries)),
        paren(&s.binder_list(&param_entries)),
        paren(&s.param_bound_list(&param_bounds)),
        paren(&s.binder_list(&req_entries)),
        paren(&s.mut_param_list(&mut_entries)),
        paren(&s.leaf_list(&ens_leaves)),
        paren(&s.leaf_list(&residue_ids)),
        paren(&s.prop_deep_list()),
        if s.attr_user_closer { 0 } else { 1 },
    );

    // Goal half (N3b): after the SST walk, so SST leaf ids are fixed and
    // matching goal leaves reuse them. One `GoalData` per obligation that
    // carried a spine; `None` (bit_vector/query) are skipped.
    let (goal_term, goal_names) = s.goal_list(theorems, goal_shapes);

    // Emitter-counter cross-check (bootstrap-78 S1 review): production's
    // theorem names carry their consumed ids (`build_theorem_name`'s
    // trailing `_<id>`); the walk's replayed predictions must match them
    // element-wise. A mis-counted site or an unmodeled consumer rejects
    // the cert HERE with a sharp tag instead of surfacing downstream as
    // an opaque leaf diff (or, for fns whose gensym names never print,
    // not at all until a mut cert diverges in S3). This also pins
    // walk-order emission timing for wrap-mode fns on every cert.
    // Checked against ALL production theorems, not `goal_names` —
    // `goal_list` filters to spine-carrying theorems, but every theorem
    // consumed an id regardless.
    let parsed: Vec<u64> = theorems
        .iter()
        .map(|t| {
            t.name
                .rsplit('_')
                .next()
                .and_then(|tail| tail.parse::<u64>().ok())
                .ok_or_else(|| {
                    format!("emit-counter-drift: unparseable theorem name {:?}", t.name)
                })
        })
        .collect::<Result<_, _>>()?;
    if parsed != s.predicted_theorem_ids {
        return Err(format!(
            "emit-counter-drift: production theorem ids {:?} != replayed predictions {:?}",
            parsed, s.predicted_theorem_ids
        ));
    }

    Ok(CertBody {
        ctx_term,
        stm_term,
        goal_term,
        goal_names,
        leaf_texts: s.leaves.texts,
    })
}

/// Emit the certificate for one exec/WP-proof fn. Never propagates
/// errors — an uncaptured construct is logged (`tactus: cert: <fn> not
/// serialized: <tag>`), counted, and the crate run continues (fail-loud
/// rule, spec §3). A no-op when the flag is off.
pub fn emit_cert(
    krate: &KrateX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    crate_name: &str,
    // N3b: the production obligation theorems + their goal spines,
    // index-aligned (the output of `exec_fn_theorems_to_ast`). Read here
    // — after that call, but from the SAME `&`-borrowed `check`, so the
    // SST snapshot is still faithful (§2).
    theorems: &[Theorem],
    goal_shapes: &[Option<GoalShape>],
) {
    if !cert_emit_enabled() {
        return;
    }
    let fn_name = crate::to_lean_type::lean_name_relative(&fn_sst.x.name.path);
    match serialize(krate, fn_sst, check, theorems, goal_shapes) {
        Ok(body) => match write_cert_file(crate_name, &fn_name, &body) {
            Ok(()) => census_note_certified(),
            Err(io) => {
                eprintln!("tactus: cert: {} write failed: {}", fn_name, io);
                census_note_rejected("io-error");
            }
        },
        Err(tag) => {
            eprintln!("tactus: cert: {} not serialized: {}", fn_name, tag);
            census_note_rejected(&tag);
        }
    }
}

/// Filesystem-safe / Lean-identifier-safe leaf built from the fn's
/// relative name (mirrors `generate::lean_file_path`).
fn cert_leaf_name(fn_name: &str) -> String {
    fn_name.replace(['«', '»'], "").replace('.', "__")
}

/// M5e-style content-compare write (b67): write only when the on-disk
/// text differs, so a byte-identical re-emission keeps the file's mtime.
/// Returns whether the file was (re)written.
fn write_if_changed(path: &std::path::Path, text: &str) -> std::io::Result<bool> {
    let changed = std::fs::read_to_string(path).ok().as_deref() != Some(text);
    if changed {
        let mut f = std::fs::File::create(path)?;
        f.write_all(text.as_bytes())?;
    }
    Ok(changed)
}

fn write_cert_file(crate_name: &str, fn_name: &str, body: &CertBody) -> std::io::Result<()> {
    let leaf = cert_leaf_name(fn_name);
    let dir = crate::generate::lean_out_root()
        .join(crate::to_lean_type::sanitize(crate_name))
        .join("cert");
    std::fs::create_dir_all(&dir)?;
    let path = dir.join(format!("{}.cert.lean", leaf));

    let text = render_cert(crate_name, fn_name, &leaf, body);

    // Determinism: the text is a pure function of the inputs (no
    // timestamps). Content-compare write (b67): byte-identical
    // re-emissions keep the mtime.
    write_if_changed(&path, &text)?;
    Ok(())
}

/// Assemble the cert file text. Determinism-critical: no timestamps, no
/// HashMap iteration.
fn render_cert(crate_name: &str, fn_name: &str, leaf: &str, body: &CertBody) -> String {
    let mut out = String::new();

    out.push_str(&format!("import {}\n", CERT_IMPORT));
    out.push_str("set_option linter.unusedVariables false\n");
    out.push_str("set_option autoImplicit false\n\n");

    // Header: provenance + honest-scope + vocab hash (audit block).
    out.push_str(&format!("-- tactus certificate (stage A) — crate `{}`, fn `{}`\n", crate_name, fn_name));
    out.push_str(&format!("-- tactus-core-vocab-hash: {}\n", vocab_hash()));
    out.push_str("-- Stage A certifies statement ASSEMBLY (binder telescopes, hypothesis\n");
    out.push_str("-- order, let-chains, obligation multiplicity/order). It does NOT certify\n");
    out.push_str("-- leaf rendering (stage B/W6), the serializer (it is the TCB), the\n");
    out.push_str("-- frontend, or SST-semantics adequacy (W5). Leaves below are opaque ids;\n");
    out.push_str("-- a stage-A pass coexisting with a leaf-renderer bug is possible.\n\n");

    // Leaf table (structured comments; nothing in the bridge reads it).
    out.push_str("-- ── leaf table ──────────────────────────────────────────────\n");
    for (i, t) in body.leaf_texts.iter().enumerate() {
        out.push_str(&format!("-- leaf {}: ⟦{}⟧\n", i, sanitize_comment(t)));
    }
    out.push('\n');

    // The refWp context seed.
    out.push_str(&format!("@[reducible] def cert_{}_ctx : {}.FnCtxData :=\n  {}\n\n", leaf, NS, body.ctx_term));

    // The SST body literal.
    out.push_str(&format!("@[reducible] def cert_{}_sst : {}.StmData :=\n  {}\n\n", leaf, NS, body.stm_term));

    // Kernel-computation probe (§7.2; folds N5's smoke into acceptance):
    // the literal kernel-computes to the size we counted structurally.
    out.push_str(&format!(
        "example : {}.stm_size cert_{}_sst = {} := by decide\n",
        NS,
        leaf,
        stm_size_of(&body.stm_term),
    ));

    // Goal half (N3b). Emitted only when at least one obligation carried a
    // spine — an all-excluded fn leaves this section (and the byte stream)
    // exactly as N3a produced it, so the N3a golden stays valid.
    if !body.goal_names.is_empty() {
        out.push('\n');
        out.push_str("-- ── production goals (N3b) ──────────────────────────────────\n");
        // O4 obligation pairing: one comment per `GoalList` entry, in
        // order, carrying the production theorem name.
        for (i, name) in body.goal_names.iter().enumerate() {
            out.push_str(&format!("-- goal {}: {}\n", i, sanitize_comment(name)));
        }
        out.push_str(&format!(
            "@[reducible] def cert_{}_goals : {}.GoalList :=\n  {}\n\n",
            leaf, NS, body.goal_term,
        ));
        // Parallel to the SST probe: the GoalList literal kernel-computes
        // to the obligation count we emitted.
        out.push_str(&format!(
            "example : {}.goal_count cert_{}_goals = {} := by decide\n",
            NS,
            leaf,
            body.goal_names.len(),
        ));
    }

    out
}

/// Newlines / control chars would break the single-line `-- leaf` comment
/// form; collapse them. (Rendered leaves are usually single-line already.)
fn sanitize_comment(text: &str) -> String {
    text.replace('\n', " ⏎ ").replace('\r', "")
}

// ── W7d (bootstrap-32): defs-layer certificate emission ─────────────────
//
// The def/datatype analog of `emit_cert`. Where `emit_cert` bridges the
// obligation GOALS (`goals_eq`), these bridge the SHARED-DEFS layer: each
// spec-fn `@[reducible] def` earns a `def_eq (render_def raw) defdata = 1`
// certificate, each `inductive` a `dt_eq (render_dt raw) dtdata = 1`. The
// REFERENCE side (`raw_vir_def` / `raw_vir_dt`) reads VIR; PRODUCTION
// (`ldef_to_defdata` / `ldt_to_dtdata`) reads the already-emitted `lean_ast`.
//
// Both sides are driven on ONE `Serializer` (see `serialize_def` /
// `serialize_dt`), so the interned leaf ids agree by the atom-id-consistency
// invariant — the reference walk interns every string first, and the
// production walk reuses those ids. This is the exact `(raw, defdata)` pairing
// probe16 (`probe-w0/probe16_w7d_defbridge`) proved closes under `decide`
// against the LANDED tactus-core `render_def` / `def_eq`.
//
// Fail-loud like `emit_cert`: an uncertifiable def/datatype (polymorphic,
// struct-datatype, uncovered body/type) is logged, census'd, and the crate run
// continues (spec §3). A no-op when the flag is off. The REFERENCE side is the
// gate — if it fails loud, `?` short-circuits before the production side runs,
// so the census tag names the reference construct and no half-cert is written.

/// Emit the defs-layer certificate for one spec fn (the `def_eq` bridge).
/// The VIR side is passed DECOMPOSED (name / typ_params / value params / ret /
/// body) — exactly the `raw_vir_def` argument shape — so the generate.rs wire
/// unpacks the `FunctionX` at the call site and this stays unit-testable with
/// the lightweight VIR builders.
pub fn emit_def_cert(
    crate_name: &str,
    name: &vir::ast::Fun,
    typ_params: &vir::ast::Idents,
    params: &vir::ast::Params,
    ret: &Typ,
    body: &VirExpr,
    def: &crate::lean_ast::Def,
) {
    if !cert_emit_enabled() {
        return;
    }
    let fn_name = crate::to_lean_type::lean_name_relative(&name.path);
    match serialize_def(name, typ_params, params, ret, body, def) {
        Ok((raw, defdata)) => match write_def_cert_file(crate_name, &fn_name, &raw, &defdata) {
            Ok(()) => census_note_certified(),
            Err(io) => {
                eprintln!("tactus: def-cert: {} write failed: {}", fn_name, io);
                census_note_rejected("io-error");
            }
        },
        Err(tag) => {
            eprintln!("tactus: def-cert: {} not serialized: {}", fn_name, tag);
            census_note_rejected(&tag);
        }
    }
}

/// Emit the defs-layer certificate for one datatype (the `dt_eq` bridge).
/// VIR side DECOMPOSED (name / typ_params / variants), matching `raw_vir_dt`.
pub fn emit_dt_cert(
    crate_name: &str,
    name: &Dt,
    typ_params: &vir::ast::TypPositives,
    variants: &vir::ast::Variants,
    dt: &crate::lean_ast::Datatype,
) {
    if !cert_emit_enabled() {
        return;
    }
    let dt_name = dt.name.clone();
    match serialize_dt(name, typ_params, variants, dt) {
        Ok((raw, dtdata)) => match write_dt_cert_file(crate_name, &dt_name, &raw, &dtdata) {
            Ok(()) => census_note_certified(),
            Err(io) => {
                eprintln!("tactus: dt-cert: {} write failed: {}", dt_name, io);
                census_note_rejected("io-error");
            }
        },
        Err(tag) => {
            eprintln!("tactus: dt-cert: {} not serialized: {}", dt_name, tag);
            census_note_rejected(&tag);
        }
    }
}

/// Drive both def transcribers on a SHARED `Serializer` (so the reference's
/// forward-interned leaf ids are reused by the production side), returning the
/// `(raw_vir_def text, ldef_to_defdata text)` pair the bridge compares. The
/// reference runs first and gates (poly/mut-param fail loud before production).
fn serialize_def(
    name: &vir::ast::Fun,
    typ_params: &vir::ast::Idents,
    params: &vir::ast::Params,
    ret: &Typ,
    body: &VirExpr,
    def: &crate::lean_ast::Def,
) -> Sr<(String, String)> {
    let mut s = Serializer::default();
    let raw = s.raw_vir_def(name, typ_params, params, ret, body)?;
    let defdata = s.ldef_to_defdata(def)?;
    Ok((raw, defdata))
}

/// Datatype twin of `serialize_def`: `(raw_vir_dt text, ldt_to_dtdata text)`.
fn serialize_dt(
    name: &Dt,
    typ_params: &vir::ast::TypPositives,
    variants: &vir::ast::Variants,
    dt: &crate::lean_ast::Datatype,
) -> Sr<(String, String)> {
    let mut s = Serializer::default();
    let raw = s.raw_vir_dt(name, typ_params, variants)?;
    let dtdata = s.ldt_to_dtdata(dt)?;
    Ok((raw, dtdata))
}

fn write_def_cert_file(
    crate_name: &str,
    fn_name: &str,
    raw: &str,
    defdata: &str,
) -> std::io::Result<()> {
    let leaf = cert_leaf_name(fn_name);
    let dir = crate::generate::lean_out_root()
        .join(crate::to_lean_type::sanitize(crate_name))
        .join("cert");
    std::fs::create_dir_all(&dir)?;
    // Distinct `.defcert.lean` suffix so a def cert never collides with the
    // obligation cert's `.cert.lean` (nor the datatype's `.dtcert.lean`).
    let path = dir.join(format!("{}.defcert.lean", leaf));
    let text = render_def_cert(crate_name, fn_name, &leaf, raw, defdata);
    write_if_changed(&path, &text)?;
    Ok(())
}

fn write_dt_cert_file(
    crate_name: &str,
    dt_name: &str,
    raw: &str,
    dtdata: &str,
) -> std::io::Result<()> {
    let leaf = cert_leaf_name(dt_name);
    let dir = crate::generate::lean_out_root()
        .join(crate::to_lean_type::sanitize(crate_name))
        .join("cert");
    std::fs::create_dir_all(&dir)?;
    let path = dir.join(format!("{}.dtcert.lean", leaf));
    let text = render_dt_cert(crate_name, dt_name, &leaf, raw, dtdata);
    write_if_changed(&path, &text)?;
    Ok(())
}

/// The header block shared by both defs-layer cert kinds (import + options +
/// provenance/honest-scope). `kind` is the human tag (`"spec fn"` / `"datatype"`).
fn defcert_header(out: &mut String, crate_name: &str, kind: &str, name: &str) {
    out.push_str(&format!("import {}\n", CERT_IMPORT));
    // `render_def`/`render_dt` + `def_eq`/`dt_eq` are shallow struct
    // projections, but the interned body/ctor lists nest through `Box`; match
    // the probe's recursion budget so a deep fixture still `decide`s.
    out.push_str("set_option maxRecDepth 8000\n");
    out.push_str("set_option linter.unusedVariables false\n");
    out.push_str("set_option autoImplicit false\n\n");
    out.push_str(&format!(
        "-- tactus defs-layer certificate (W7d) — crate `{}`, {} `{}`\n",
        crate_name, kind, name
    ));
    out.push_str(&format!("-- tactus-core-vocab-hash: {}\n", vocab_hash()));
    out.push_str("-- Certifies that the INDEPENDENT reference transcription of this\n");
    out.push_str("-- def/datatype (VIR-side `raw_vir_*`, rendered by tactus-core `render_*`)\n");
    out.push_str("-- agrees with the PRODUCTION `lean_ast`-side transcription (`l*_to_*data`)\n");
    out.push_str("-- via `def_eq`/`dt_eq`. It does NOT certify the transcribers (they are the\n");
    out.push_str("-- TCB), the leaf-id interning, the frontend, or SST-semantics adequacy (W5).\n\n");
}

/// Assemble a def cert file (`<leaf>.defcert.lean`). Determinism-critical: pure
/// function of its inputs (no timestamps, no HashMap iteration).
fn render_def_cert(crate_name: &str, fn_name: &str, leaf: &str, raw: &str, defdata: &str) -> String {
    let mut out = String::new();
    defcert_header(&mut out, crate_name, "spec fn", fn_name);
    // The reference RawDef literal + the production DefData literal, built on
    // the shared leaf table (so their ids line up) — the exact `(raw, defdata)`
    // shape probe16 proved closes.
    out.push_str(&format!("def cert_{}_raw : {}.RawDef :=\n  {}\n\n", leaf, NS, raw));
    out.push_str(&format!(
        "def cert_{}_defdata : {}.DefData :=\n  {}\n\n",
        leaf, NS, defdata
    ));
    // The bridge: the rendered reference equals the production def (`= 1`).
    out.push_str(&format!(
        "example : {}.def_eq ({}.render_def cert_{}_raw) cert_{}_defdata = 1 := by decide\n",
        NS, NS, leaf, leaf
    ));
    out
}

/// Datatype twin of `render_def_cert` (`<leaf>.dtcert.lean`, `dt_eq`/`render_dt`).
fn render_dt_cert(crate_name: &str, dt_name: &str, leaf: &str, raw: &str, dtdata: &str) -> String {
    let mut out = String::new();
    defcert_header(&mut out, crate_name, "datatype", dt_name);
    out.push_str(&format!("def cert_{}_raw : {}.RawDt :=\n  {}\n\n", leaf, NS, raw));
    out.push_str(&format!(
        "def cert_{}_dtdata : {}.DtData :=\n  {}\n\n",
        leaf, NS, dtdata
    ));
    out.push_str(&format!(
        "example : {}.dt_eq ({}.render_dt cert_{}_raw) cert_{}_dtdata = 1 := by decide\n",
        NS, NS, leaf, leaf
    ));
    out
}

/// Structural `stm_size` of an emitted `StmData` term, computed by
/// counting constructor heads exactly as `tactus-core`'s `stm_size`
/// does — so the emitted `example : stm_size … = n := by decide` probe
/// carries the right `n`. Mirrors `lib.stm_size` (lib.rs):
///   Assert/Assume/Assign/Skip → 1
///   Call → 1 + |reqs| + frame_len(post)
///   DeadEnd/Ret → 1 + inner list/stm
///   If → 1 + size(t) + size(e)
///   Loop → 1 + |invs| + |binders| + size(body)
///   Seq → 1 + size(a) + size(b)
///
/// Computed by re-parsing our own emitted text would be fragile; instead
/// `serialize` could return the size directly. For turn-1 we compute it
/// from the string by counting the relevant constructor tokens, which is
/// Does control through `stm` UNCONDITIONALLY diverge (return / dead-end /
/// loop-break) before reaching its end? The Rust mirror of refWp's
/// `diverges` (tactus-core/lib.rs) — used by the two-way If-join desugar
/// (`block`, bootstrap-19) to decide whether a branch DISCARDS the post-if
/// continuation (production's `build_wp(branch, after)` discards `after` at
/// a `Return` — the `after` is passed in but the Return arm ignores it).
/// A `Block` diverges if ANY statement does (the rest is dead code); an
/// `If` diverges only if BOTH branches do (a missing else falls through).
/// SOUND either way vs the `decide` bridge: too-weak (cloning `rest` into a
/// diverging branch) adds a dead-continuation goal refWp emits but
/// production does not → honest-fail; too-strong (dropping the clone from a
/// falling-through branch) omits a goal → honest-fail. Never silent-pass
/// (`goals_eq` is strict-structural).
fn stm_diverges(stm: &Stm) -> bool {
    match &stm.x {
        StmX::Return { .. } => true,
        StmX::DeadEnd(_) => true,
        StmX::BreakOrContinue { .. } => true,
        StmX::Block(stms) => stms.iter().any(stm_diverges),
        StmX::If(_, then_stm, else_stm) => {
            stm_diverges(then_stm) && else_stm.as_ref().map_or(false, stm_diverges)
        }
        _ => false,
    }
}

/// View `stm` as an `if C { t } else { e }`, peeling single-statement
/// `Block` wrappers (the frontend often wraps a bare `if` in a one-element
/// block). Returns the cond / then / else so the two-way join desugar
/// (`block`) can fire whether the head statement is a raw `StmX::If` or a
/// `Block([If])`. Only SINGLE-element blocks are peeled — a `Block` ending
/// in an `If` after other statements is NOT an If head (the desugar leaves
/// it, a sound honest-fail).
fn as_if(stm: &Stm) -> Option<(&Exp, &Stm, &Option<Stm>)> {
    match &stm.x {
        StmX::If(cond, then_stm, else_stm) => Some((cond, then_stm, else_stm)),
        StmX::Block(stms) if stms.len() == 1 => as_if(&stms[0]),
        _ => None,
    }
}

/// exact for the terms this serializer emits (well-formed, fully
/// parenthesized). See the N3c golden test for the pin.
fn stm_size_of(stm_term: &str) -> u64 {
    // Count of leaf-list `Cons` and binder-list `Cons` occurrences that
    // feed size, plus statement heads. This is a deliberate structural
    // token count over OUR OWN output grammar (not general Lean).
    let count = |needle: &str| stm_term.matches(needle).count() as u64;
    // NOTE the trailing space on `Assert `: `AssertQueryNl` and
    // `AssertQueryTactus` contain `Assert` as a prefix and must not
    // double-count. Same for `If ` vs `IfCtor` (bootstrap-77).
    let stmt_heads = count(&format!("{}.StmData.Assert ", NS))
        + count(&format!("{}.StmData.AssertQueryNl", NS))
        + count(&format!("{}.StmData.AssertQueryTactus", NS))
        + count(&format!("{}.StmData.Assume", NS))
        + count(&format!("{}.StmData.Assign", NS))
        + count(&format!("{}.StmData.Call", NS))
        + count(&format!("{}.StmData.DeadEnd", NS))
        + count(&format!("{}.StmData.Ret", NS))
        + count(&format!("{}.StmData.If ", NS))
        + count(&format!("{}.StmData.IfCtor", NS))
        + count(&format!("{}.StmData.Loop", NS))
        + count(&format!("{}.StmData.Skip", NS))
        + count(&format!("{}.StmData.Seq", NS));
    // Each StmData head contributes its own `1`. The obligation lists under
    // Call/Ret/Loop are now `RawExpList`s (W6d.2a) — each `Cons` adds 1, as
    // tactus-core's `raw_exp_list_len` counts them; BinderList `Cons`
    // (inv_hyps/binders) likewise. (LeafList `Cons` stays counted for the
    // pre-W6d.2a golden round-trip, where Ret/Call carried a LeafList; a live
    // stm_term now emits RawExpList, so only one of the two is ever nonzero.)
    let leaf_cons = count(&format!("{}.LeafList.Cons", NS))
        + count(&format!("{}.RawExpList.Cons", NS));
    let binder_cons = count(&format!("{}.BinderList.Cons", NS));
    // Call's `post` FrameList (bootstrap-02b): `frame_len` counts each
    // FBind/FHyp/FLet entry as 1 (FNil as 0), exactly as tactus-core's
    // `stm_size(Call) = 1 + leaf_len(reqs) + frame_len(post)`.
    let frame_entries = count(&format!("{}.FrameList.FBind", NS))
        + count(&format!("{}.FrameList.FHyp", NS))
        + count(&format!("{}.FrameList.FLet", NS));
    stmt_heads + leaf_cons + binder_cons + frame_entries
}

/// Content hash of the vendored `tactus-core` vocabulary
/// (`$TACTUS_CORE_VOCAB`). Dependency-free FNV-1a as a placeholder for the
/// SHA-256 the §6 vendoring will bring; deterministic within a pinned
/// toolchain. `unvendored` when the env var is unset / unreadable.
fn vocab_hash() -> String {
    match std::env::var("TACTUS_CORE_VOCAB").ok().and_then(|p| std::fs::read(p).ok()) {
        Some(bytes) => {
            let mut h: u64 = 0xcbf29ce484222325;
            for b in bytes {
                h ^= b as u64;
                h = h.wrapping_mul(0x100000001b3);
            }
            format!("fnv1a:{:016x}", h)
        }
        None => "unvendored".to_string(),
    }
}

// ── Lean-term helpers ───────────────────────────────────────────────

/// Wrap a term in `Tactus.Box.mk (…)`. Matches the emitted-defs literal
/// syntax (`tactus-core/out/lib/...`).
fn box_(term: &str) -> String {
    format!("(Tactus.Box.mk {})", paren(term))
}

/// Parenthesize a term if it's an application (has a top-level space).
/// Bare atoms (`lib.StmData.Skip`) pass through.
fn paren(term: &str) -> String {
    let t = term.trim();
    if t.starts_with('(') || !t.contains(' ') {
        t.to_string()
    } else {
        format!("({})", t)
    }
}

/// The opaque-fallback obligation `RawExp` literal: tactus-core's
/// `atom_ob(id) = RawExp::Var(id, TyBool)`, which `render_exp` maps to
/// `ExprData::Atom(id)`. Emitted wherever the raw SST obligation leaf is not
/// yet one of the deepened `RawExp` shapes (G0–G7, W6d.2b) — the interned
/// `id` still cancels against the goal-side `LeafE(Atom id)` by construction
/// (the stage-A W2 leaf match, now carried inside the deep leaf). W6d.2a.
fn atom_ob_lit(id: u64) -> String {
    format!("({}.RawExp.Var {} {}.TypData.TyBool)", NS, id, NS)
}

// ── G4/W6e: value-if-lift recompute helpers (free fns / types) ──────

/// One pending `let name := <hole>; body` wrap around a lifted leaf value
/// (see `Serializer::lift_if_raw`). `body` is pre-rendered `RawExp` text.
#[derive(Clone)]
struct RawLet {
    name: u64,
    body: String,
}

/// The lifted return-obligation tree before the top-level `And` split.
enum LiftedRaw {
    /// A conjunction the split descends into (the `if`-lift's top node).
    And(Box<LiftedRaw>, Box<LiftedRaw>),
    /// `cond → body`. `cond` is pre-rendered `RawExp` text (already `¬`-
    /// wrapped for the else branch); the split does NOT descend past it.
    Implies(String, Box<LiftedRaw>),
    /// A fully-rendered obligation `RawExp` (the `let r := …; ens` leaf).
    Leaf(String),
}

/// Fold the wrap-stack (outer→inner) around a leaf value `v`, applying the
/// INNERMOST wrap first: `apply([(r, ens), (m, m_body)], v)` =
/// `Let r (Let m v m_body) ens`. Mirrors `lift_if_value_coerced`'s nested
/// `emit_leaf(let name := <hole>; body)` continuation.
fn apply_raw_wraps(wraps: &[RawLet], v: &str) -> String {
    let mut acc = v.to_string();
    for w in wraps.iter().rev() {
        acc = format!(
            "({}.RawExp.Let {} {} {})",
            NS,
            w.name,
            box_raw(&acc),
            box_raw(&w.body)
        );
    }
    acc
}

/// Serialize a `LiftedRaw` node (non-split context) to `RawExp` text.
/// `And` → `BinOp 11 TyBool` (a NESTED conjunction — reachable only under an
/// `Implies` body from nested ifs, which the split leaves intact).
fn serialize_lifted(t: &LiftedRaw) -> String {
    match t {
        LiftedRaw::And(a, b) => format!(
            "({}.RawExp.BinOp 11 {}.TypData.TyBool {} {})",
            NS,
            NS,
            box_raw(&serialize_lifted(a)),
            box_raw(&serialize_lifted(b))
        ),
        LiftedRaw::Implies(cond, body) => format!(
            "({}.RawExp.BinOp 13 {}.TypData.TyBool {} {})",
            NS,
            NS,
            box_raw(cond),
            box_raw(&serialize_lifted(body))
        ),
        LiftedRaw::Leaf(s) => s.clone(),
    }
}

/// Split top-level `And`s into separate obligation `RawExp`s (matching
/// production's `emit_done_or_split`, which recurses only through `And`).
/// `Implies`/`Leaf` nodes are terminal obligations serialized as-is.
fn split_lifted(t: LiftedRaw, out: &mut Vec<String>) {
    match t {
        LiftedRaw::And(a, b) => {
            split_lifted(*a, out);
            split_lifted(*b, out);
        }
        other => out.push(serialize_lifted(&other)),
    }
}

/// Right-associated conjunction of `RawExp` terms (matching `and_all`,
/// `lean_ast.rs`): `[e0, e1, e2]` → `And(e0, And(e1, e2))`. `RawExp.BinOp 11
/// TyBool`. Callers guarantee a non-empty slice.
fn conjoin_raw(terms: &[String]) -> String {
    let (last, init) = terms.split_last().expect("conjoin_raw: non-empty");
    let mut acc = last.clone();
    for t in init.iter().rev() {
        acc = format!(
            "({}.RawExp.BinOp 11 {}.TypData.TyBool {} {})",
            NS,
            NS,
            box_raw(t),
            box_raw(&acc)
        );
    }
    acc
}

/// Pure structural test: does the return VALUE `e` lift — i.e. contain an
/// `if` in a value position `lift_if_value_coerced` would pull into the
/// ensures leaf? Mirrors the lift's If/single-let-bind recursion WITHOUT
/// interning, so the Return arm can gate the recompute before running it.
fn value_lifts(e: &Exp) -> bool {
    let p = crate::sst_to_lean::peel_value_position(e);
    match &p.x {
        ExpX::If(..) => true,
        ExpX::Bind(bnd, body) => match crate::sst_to_lean::match_single_let_bind(bnd, body) {
            Some((_, rhs, inner_body)) => {
                let pi = crate::sst_to_lean::peel_value_position(inner_body);
                let inner_is_let_chain =
                    matches!(&pi.x, ExpX::Bind(b, _) if matches!(&b.x, BndX::Let(_)));
                // The lift recurses into `rhs` (non-let-chain inner) or
                // `inner_body` (let-chain); check the same position.
                if inner_is_let_chain {
                    value_lifts(inner_body)
                } else {
                    value_lifts(rhs)
                }
            }
            None => false,
        },
        _ => false,
    }
}

/// `lib.RawExpList` from RawExp literal terms (order preserved). The element
/// is `Box<RawExp>` (`Cons (Box.mk <re>) (Box.mk <tail>)`, mirroring the
/// tactus-core `RawExpList::Cons(Box<RawExp>, Box<RawExpList>)`), unlike
/// `leaf_list`'s inline `u64` head. Feeds `close_each_e` (Call reqs, Ret
/// enss, Loop inv_obligs). W6d.2a.
fn raw_exp_list(terms: &[String]) -> String {
    let mut term = format!("{}.RawExpList.Nil", NS);
    for t in terms.iter().rev() {
        term = format!("{}.RawExpList.Cons {} {}", NS, box_(t), box_(&term));
    }
    term
}

// ── W6c: RawExp emit helpers ────────────────────────────────────────

/// Box a `RawExp` sub-term for a recursive field (`Box<RawExp>` in the W6b
/// mirror), matching `box_`'s `Tactus.Box.mk (…)` literal syntax.
fn box_raw(term: &str) -> String {
    box_(term)
}

/// Box an `ExprData` sub-term for a recursive field (`Box<ExprData>` in the
/// W6b mirror). Same `Tactus.Box.mk (…)` syntax as `box_raw`; a distinct name
/// documents the production-side (prod ExprData) vs reference-side (ref
/// RawExp) role.
fn box_ed(term: &str) -> String {
    box_(term)
}

/// True iff `e` is a bare `Var` whose rendered name equals `name` — the shape
/// production uses for the `Int.toNat` / `Int.ofNat` cast heads
/// (`LExpr::var_lit`). `&Box<Expr>` deref-coerces to `&Expr` at the call site.
fn is_var_named(e: &LExpr, name: &str) -> bool {
    matches!(&e.node, ExprNode::Var(n) if n.as_str() == name)
}

/// The effective fn name of an App head: a bare `Var(name)` (the no-type-args
/// callee, e.g. `tri`), or a type-arg application `App { head: Var(name), .. }`
/// (production applies the fn to its type args before the value arg). The
/// reference `RawExp::Call` carries no type args, so we key on the name alone
/// and drop any type-arg layer — keeping both W6c sides identical on generic
/// calls. Returns `None` for any other head shape (→ `ed-app-head`).
fn app_head_fn_name(head: &LExpr) -> Option<&str> {
    match &head.node {
        ExprNode::Var(n) => Some(n.as_str()),
        ExprNode::App { head: inner, .. } => match &inner.node {
            ExprNode::Var(n) => Some(n.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Production-side counterpart of `binop_opcode`: map the `lean_ast::BinOp`
/// production chose (via `binop_to_ast`) into the SAME canonical opcode table.
/// The `binop_opcode_alignment` test pins that the two tables agree through
/// `binop_to_ast` on every structural op, so a future edit to one without the
/// other is caught. `Iff` / bitwise / `Prod` are outside the cast class (the
/// reference `binop_opcode` likewise rejects the vir ops that would produce
/// them) → fail loud (`ed-binop-<k>`). Note `Xor` has no `lean_ast::BinOp`
/// variant — production renders it as a 2-arg App (`Bool.xor a b`), which
/// `lexpr_to_exprdata` now lowers to `ExprData.AppN` (bootstrap-34 widened the
/// multi-arg App arm), NOT a `BinOp` node. So `lean_binop_opcode` is never
/// called with `Xor`, and the reference's `Xor → 14` BinOp opcode is never
/// produced by a bridged fn (both sides mirror `Bool.xor` through the App/AppN
/// path, keyed on the same interned fn id).
fn lean_binop_opcode(op: &crate::lean_ast::BinOp) -> Sr<u64> {
    use crate::lean_ast::BinOp as L;
    let code = match op {
        L::Eq => 0,
        L::Ne => 1,
        L::Lt => 2,
        L::Le => 3,
        L::Gt => 4,
        L::Ge => 5,
        L::Add => 6,
        L::Sub => 7,
        L::Mul => 8,
        L::Div => 9,
        L::Mod => 10,
        L::And => 11,
        L::Or => 12,
        L::Implies => 13,
        L::Iff => return Err("ed-binop-iff".to_string()),
        L::BitAnd => return Err("ed-binop-bitand".to_string()),
        L::BitOr => return Err("ed-binop-bitor".to_string()),
        L::BitXor => return Err("ed-binop-bitxor".to_string()),
        L::Shr => return Err("ed-binop-shr".to_string()),
        L::Shl => return Err("ed-binop-shl".to_string()),
        L::Prod => return Err("ed-binop-prod".to_string()),
    };
    Ok(code)
}

/// Sharp census tag for an un-mirrored `ExprNode` (the `_` arm of
/// `lexpr_to_exprdata`). Var/Lit/BinOp/App/FieldProj/SpanMark are handled in
/// the main match and never reach here.
fn lexpr_construct_tag(n: &ExprNode) -> &'static str {
    match n {
        ExprNode::LitBool(_) => "litbool",
        ExprNode::LitStr(_) => "litstr",
        ExprNode::LitChar(_) => "litchar",
        ExprNode::UnOp { .. } => "unop",
        ExprNode::Let { .. } => "let",
        ExprNode::Lambda { .. } => "lambda",
        ExprNode::Forall { .. } => "forall",
        ExprNode::Exists { .. } => "exists",
        ExprNode::If { .. } => "if",
        ExprNode::Match { .. } => "match",
        ExprNode::TypeAnnot { .. } => "typeannot",
        ExprNode::StructUpdate { .. } => "structupdate",
        ExprNode::ArrayLit(_) => "arraylit",
        ExprNode::VectorLit(_) => "vectorlit",
        ExprNode::Tuple(_) => "tuple",
        ExprNode::Index { .. } => "index",
        ExprNode::Anon(_) => "anon",
        ExprNode::Subtype { .. } => "subtype",
        ExprNode::Raw(_) => "raw",
        ExprNode::ByBlock { .. } => "byblock",
        _ => "other",
    }
}

/// The CANONICAL binary-opcode table — a fixed small-int namespace living in
/// `ExprData::BinOp`'s op slot (compared position-wise by `expr_eq`, so it
/// never collides with the interned atom-id namespace). Both W6c
/// transcriptions map into it: `raw_exp` from `vir::ast::BinaryOp` (here),
/// and the production `LExpr→ExprData` side from `lean_ast::BinOp` (must use
/// the SAME assignments). Fails loud (`raw-binop-<k>`) on ops outside the
/// cast class. Keep in sync with the prod-side table when W6d lands it.
fn binop_opcode(op: &BinaryOp) -> Sr<u64> {
    let code = match op {
        BinaryOp::Eq(_) => 0,
        BinaryOp::Ne => 1,
        BinaryOp::Inequality(InequalityOp::Lt) => 2,
        BinaryOp::Inequality(InequalityOp::Le) => 3,
        BinaryOp::Inequality(InequalityOp::Gt) => 4,
        BinaryOp::Inequality(InequalityOp::Ge) => 5,
        BinaryOp::Arith(ArithOp::Add(_)) => 6,
        BinaryOp::Arith(ArithOp::Sub(_)) => 7,
        BinaryOp::Arith(ArithOp::Mul(_)) => 8,
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => 9,
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => 10,
        BinaryOp::And => 11,
        BinaryOp::Or => 12,
        BinaryOp::Implies => 13,
        BinaryOp::Xor => 14,
        _ => return Err(format!("raw-binop-{}", binop_construct_tag(op))),
    };
    Ok(code)
}

/// Sharp census tag for an un-mirrored `BinaryOp` (the `_` arm of
/// `binop_opcode`).
fn binop_construct_tag(op: &BinaryOp) -> &'static str {
    match op {
        BinaryOp::HeightCompare { .. } => "height",
        BinaryOp::Bitwise(..) => "bitwise",
        BinaryOp::RealArith(..) => "realarith",
        BinaryOp::IeeeFloat(..) => "ieeefloat",
        BinaryOp::StrGetChar => "strgetchar",
        BinaryOp::Index(..) => "index",
        _ => "other",
    }
}

/// Sharp census tag for an un-mirrored `TypX` (the `_` arm of `typ_data`).
/// Width `n` of a fixed-width UNSIGNED integer range a `HasType(U(n))`
/// refinement carries (G6), peeling SMT `Boxed`/`Decorate` wrappers (parallel
/// to `typ_data`). Only the unsigned ranges production expands to
/// `0 ≤ e ∧ e < 2^n` are accepted; every other range fails loud
/// (`hastype-range`), matching the `RawExp::HasType` contract
/// (signed/usize/char/vacuous ranges are not carried). A `U(n)` whose width is
/// outside `pow2`'s table would render a `0` bound → a loud bridge mismatch,
/// still never a silent pass; the Verus fixed widths (8/16/32/64/128) are all
/// covered.
fn uint_bound_width(typ: &Typ) -> Sr<u64> {
    match &**typ {
        TypX::Int(IntRange::U(n)) => Ok(*n as u64),
        TypX::Decorate(_, _, inner) | TypX::Boxed(inner) => uint_bound_width(inner),
        _ => Err("hastype-range".to_string()),
    }
}

fn typ_construct_tag(typ: &Typ) -> &'static str {
    match &**typ {
        TypX::Real => "real",
        TypX::Float(..) => "float",
        TypX::SpecFn(..) => "specfn",
        TypX::AnonymousClosure(..) => "closure",
        TypX::FnDef(..) => "fndef",
        TypX::Dyn(..) => "dyn",
        TypX::Opaque { .. } => "opaque",
        TypX::Primitive(..) => "primitive",
        TypX::TypParam(..) => "typparam",
        TypX::Projection { .. } => "projection",
        TypX::PointeeMetadata(..) => "pointeemeta",
        TypX::TypeId => "typeid",
        TypX::ConstInt(..) => "constint",
        _ => "other",
    }
}

/// Sharp census tag for an un-mirrored `ExpX` (the `_` arm of `raw_exp`).
fn exp_construct_tag(e: &ExpX) -> &'static str {
    match e {
        ExpX::Const(..) => "const-nonint",
        ExpX::StaticVar(..) => "staticvar",
        ExpX::VarLoc(..) => "varloc",
        ExpX::VarAt(..) => "varat",
        ExpX::Loc(..) => "loc",
        ExpX::Old(..) => "old",
        ExpX::Call(..) => "call-nonfun",
        ExpX::CallLambda(..) => "calllambda",
        ExpX::Ctor(..) => "ctor",
        ExpX::NullaryOpr(..) => "nullaryopr",
        ExpX::Unary(..) => "unary-nonclip",
        ExpX::UnaryOpr(..) => "unaryopr",
        ExpX::BinaryOpr(..) => "binaryopr",
        ExpX::If(..) => "if",
        ExpX::WithTriggers(..) => "withtriggers",
        ExpX::Bind(..) => "bind",
        ExpX::ExecFnByName(..) => "execfnbyname",
        ExpX::ArrayLiteral(..) => "arrayliteral",
        ExpX::Interp(..) => "interp",
        ExpX::FuelConst(..) => "fuelconst",
        _ => "other",
    }
}

/// Sharp census tag for an un-mirrored VIR `ExprX` (the `_` arm of
/// `raw_vir_exp`). The deferred-but-expected def-body shapes get named tags
/// (quantifiers, ctor construction, multi-arg call, blocks); everything else
/// is `other`.
fn vir_expr_construct_tag(e: &ExprX) -> &'static str {
    match e {
        ExprX::Const(..) => "const-nonint",
        ExprX::VarLoc(..) => "varloc",
        ExprX::ConstVar(..) => "constvar",
        ExprX::StaticVar(..) => "staticvar",
        ExprX::Loc(..) => "loc",
        ExprX::Call(..) => "call-nonfun",
        ExprX::Ctor(..) => "ctor",
        ExprX::NullaryOpr(..) => "nullaryopr",
        ExprX::Unary(..) => "unary-nonclip",
        ExprX::UnaryOpr(..) => "unaryopr",
        ExprX::BinaryOpr(..) => "binaryopr",
        ExprX::Multi(..) => "multi",
        ExprX::Quant(..) => "quant",
        ExprX::Closure(..) => "closure",
        ExprX::NonSpecClosure { .. } => "nonspecclosure",
        ExprX::ArrayLiteral(..) => "arrayliteral",
        ExprX::ExecFnByName(..) => "execfnbyname",
        ExprX::Choose { .. } => "choose",
        ExprX::WithTriggers { .. } => "withtriggers",
        ExprX::If(..) => "if-noelse",
        ExprX::Block(..) => "block",
        _ => "other",
    }
}

#[cfg(test)]
#[path = "sst_serialize_tests.rs"]
mod tests;
