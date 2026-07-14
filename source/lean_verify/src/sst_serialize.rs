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
//! # Snapshot point (faithfulness anchor #1)
//!
//! [`emit_cert`] is called at the inputs of
//! `sst_to_lean::exec_fn_theorems_to_ast(krate, fn_sst, check,
//! broadcast_lemmas)` — the single source of obligation shape both the
//! island and package paths feed. The serializer transcribes the RAW
//! `check.body: Stm`. The mut-ref rewrite and `WpCtx` construction happen
//! *inside* `exec_fn_theorems_to_ast`, downstream of this snapshot, so
//! they are deliberately not the serializer's input — refWp recomputes
//! whatever the walker does from the literal, and the `decide` equality
//! (W2) is what validates the recomputation.
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
//! * `check.body` — the `Stm` tree → `StmData` (the stage-A subset:
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
//!   parallel `_h_ctx_N` type-bound hyps, the standard invariants as
//!   `(_h_ctx_N, ANNOTATED obligation leaf)`, the ANNOTATED cond /
//!   ¬cond hyps (shared `_h_ctx_N` name), and the single-level decrease
//!   snapshot (`_tactus_d_old_<id>_0`) + its annotated
//!   `0 ≤ D ∧ D < d_old` obligation. `_h_ctx_N` names mirror
//!   `OblCtx::split_leading_binders`' counter byte-for-byte so the
//!   binder-name ids unify with the goal side.
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
//!
//! ## Deliberately NOT read (each a stage-A exclusion — fail-loud)
//!
//! * `StmX::Call` shapes OUTSIDE the restricted subset above — each a
//!   sharp fail-loud tag (so the census pinpoints the missing arm):
//!   `call-trait` (trait-method-impl callee), `call-crosscrate` (callee
//!   not in `fn_map`), `call-mut` (`&mut` param — needs the existential /
//!   rebind / prophecy machinery), `call-generic` (type params —
//!   instantiated-typ leaves), `call-unit-dest` (unit-returning call, no
//!   dest binder), `call-dynamic-resolved` / `call-trait-default`
//!   (non-Static resolution), and `call-forall-path` (a callee with no
//!   `r == E` ensures — the ∀-path frame assembly, pending a validating
//!   fixture).
//! * `StmX::AssertBitVector` / `AssertQuery` — bv/compute/query asserts
//!   and their isolated contexts (tags `assert-bitvector`/`assert-query`).
//! * `StmX::OpenInvariant` / `ClosureInner` / `BreakOrContinue` —
//!   concurrency, closures, loop control. `BreakOrContinue` therefore also
//!   excludes `invariant_except_break` loops.
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

use vir::ast::{KrateX, Typ, VarIdent};
use vir::sst::{Exp, FuncCheckSst, FunctionSst, LoopInv, Stm, StmX};

use crate::lean_ast::{AssertKind, Expr as LExpr, GoalShape, GoalSpine, ObligationKind, Theorem};
use crate::lean_pp::pp_expr;
use crate::to_lean_type::{param_binder_typ, typ_to_expr};

/// The emitted `tactus-core` namespace. The crate compiled from
/// `tactus-core/lib.rs` has crate name `lib`, so its inductives emit as
/// `lib.StmData`, `lib.LeafList`, … (see `tactus-core/out/lib/`). One
/// constant so a future vendored-rename to `TactusCore` is a one-line
/// change.
const NS: &str = "lib";

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
    /// The fn's ANNOTATED ensures obligation leaves (span_mark'd, the
    /// `Return` goal — finding-1's Ret-annotation), set once before
    /// walking the body so the statement recursion stays a plain
    /// `&Stm → String`. Production renders each ensures at the return
    /// site as a `Postcondition` `SpanMark` (`WpCtx::new`); `oblig_leaf`
    /// byte-matches it so the goal-side postcondition leaf cancels.
    pending_ens_oblig: Vec<u64>,
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
        // Render through the binder-aware ctx (bootstrap-18) so a `&`-param
        // deref matches production's postcondition leaf. The ctx's `&self`
        // borrow ends with this statement (`inner` is owned), before
        // `intern` takes `&mut self`.
        let inner = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        let marked = LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            inner,
        );
        Ok(self.leaves.intern(pp_expr(&marked)))
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
        // Binder-aware render (bootstrap-18) — see `oblig_leaf`.
        let inner = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(e, &self.render_ctx())
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        let loc = crate::obligation_naming::format_rust_loc(&e.span);
        let marked = LExpr::span_mark(
            loc,
            Some(e.span.clone()),
            AssertKind::Obligation(ObligationKind::Plain),
            inner,
        );
        Ok(self.leaves.intern(pp_expr(&LExpr::not(marked))))
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
        let cur = crate::to_lean_sst_expr::sst_exp_to_ast_checked(d)
            .map_err(|reason| format!("leaf-render: {}", reason))?;
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
                let hyp = self.exp_leaf(e)?;
                let oblig = self.oblig_leaf(e)?;
                Ok(format!("({}.StmData.Assert {} {})", NS, oblig, hyp))
            }

            StmX::Assume(e) => {
                // Mirror the walker: drop synthetic resolution-tracking
                // assumes (HasResolved / closure-spec), which don't render
                // to Prop and carry no information the mirror models.
                if crate::sst_to_lean::is_synthetic_assume_to_drop(e) {
                    return Ok(self.skip());
                }
                let id = self.exp_leaf(e)?;
                Ok(format!("({}.StmData.Assume {})", NS, id))
            }

            StmX::Assign { lhs, rhs } => {
                // Simple `x = e` only. Field-path `x.f = e` becomes a
                // functional update in the walker — not modeled by the
                // flat Assign mirror.
                let Some(vid) = crate::sst_to_lean::extract_simple_var_ident(&lhs.dest) else {
                    return Err("assign-field-path".to_string());
                };
                let dest = self.binder_id(vid);
                let rhs_leaf = self.exp_leaf(rhs)?;
                Ok(format!("({}.StmData.Assign {} {})", NS, dest, rhs_leaf))
            }

            StmX::Return { ret_exp, .. } => {
                // Annotated ensures obligation leaves drive the `Return`
                // goal (Ret-annotation, finding-1): span_mark'd like
                // production's `WpCtx` postcondition so the goal-side
                // postcondition leaf reuses the same id and cancels.
                let list = self.leaf_list(&self.pending_ens_oblig.clone());
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
                let retbind = match (self.pending_ret_name, ret_exp) {
                    (Some(nleaf), Some(e)) => {
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
                        // Scoped so the `&self` borrows (render_ctx, ret_typ)
                        // end (`vtext` is owned) before `intern` takes
                        // `&mut self`. if-value LIFTING is still NOT replicated
                        // (a genuinely-liftable-if return renders as one leaf
                        // here vs production's lifted And/Imp structure) — that
                        // case honest-fails the bridge, never silent-passes.
                        let vtext = {
                            let lexpr = crate::to_lean_sst_expr::sst_exp_to_ast_checked_with_ctx(
                                e,
                                &self.render_ctx(),
                            )
                            .map_err(|reason| format!("leaf-render: {}", reason))?;
                            let coerced = match &self.ret_typ {
                                Some(rt) => {
                                    crate::expr_shared::coerce_lexpr(lexpr, &e.typ, rt)
                                }
                                None => lexpr,
                            };
                            pp_expr(&coerced)
                        };
                        let vleaf = self.leaves.intern(vtext);
                        format!("{}.RetBind.RetLet {} {}", NS, nleaf, vleaf)
                    }
                    _ => format!("{}.RetBind.RetNone", NS),
                };
                Ok(format!("({}.StmData.Ret {} {})", NS, box_(&list), paren(&retbind)))
            }

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
                let t = self.stm(then_stm)?;
                let e = match else_stm {
                    Some(s) => self.stm(s)?,
                    None => self.skip(),
                };
                Ok(format!("({}.StmData.If {} {} {} {})", NS, c, nc, box_(&t), box_(&e)))
            }

            StmX::Loop {
                cond,
                original_cond,
                body,
                invs,
                decrease,
                id,
                ..
            } => {
                // finding-3: `modified_vars` is IGNORED (it's `None` at
                // this SST stage — production's `build_wp` spells it `_`
                // and RE-DERIVES the havoc set in `build_wp_loop` via
                // `collect_modifications(body)` + `type_map`). `loop_stm`
                // mirrors that path. `id` names the `_tactus_d_old`
                // snapshot; `decrease` is the termination measure.
                self.loop_stm(cond, original_cond, body, invs, decrease, *id)
            }

            StmX::DeadEnd(inner) => {
                let b = self.stm(inner)?;
                Ok(format!("({}.StmData.DeadEnd {})", NS, box_(&b)))
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
                )?;
                self.call_stm(leaves)
            }
            // Fail-loud stage-A exclusions.
            StmX::AssertBitVector { .. } => Err("assert-bitvector".to_string()),
            StmX::AssertQuery { .. } => Err("assert-query".to_string()),
            StmX::BreakOrContinue { .. } => Err("break-or-continue".to_string()),
            StmX::OpenInvariant(_) => Err("open-invariant".to_string()),
            StmX::ClosureInner { .. } => Err("closure-inner".to_string()),
        }
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
                    // Serialize the then-branch, then the continuation ONCE
                    // (its leaves intern in then-branch position — matching
                    // production's after-clone walk order), then reuse the
                    // `rest` term verbatim in the else branch (interning is
                    // idempotent). An absent else falls through as `Skip`.
                    let then_body = self.stm(then_stm)?;
                    let rest = self.block(&stms[1..])?;
                    let t = format!("({}.StmData.Seq {} {})", NS, box_(&then_body), box_(&rest));
                    let else_body = match else_stm {
                        Some(s) => self.stm(s)?,
                        None => self.skip(),
                    };
                    let e = format!("({}.StmData.Seq {} {})", NS, box_(&else_body), box_(&rest));
                    return Ok(format!("({}.StmData.If {} {} {} {})", NS, c, nc, box_(&t), box_(&e)));
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
        let reqs = match &leaves.precondition {
            Some(l) => {
                let id = self.leaves.intern(pp_expr(l));
                self.leaf_list(&[id])
            }
            None => self.leaf_list(&[]),
        };
        // dest binder id = interned leaf id of the dest's rendered name
        // (same path as `binder_id`; production Phase-5 binds
        // `let <dest> := …`).
        let dest_id = self.text_leaf(leaves.dest_name.as_str());
        let post = match leaves.post {
            CertCallPost::RetEq { e_bound, rest, dest_value } => {
                // Frame (outer→inner): [FHyp(E_bound)] [FHyp(rest)]
                // FLet(dest, E). Built innermost-out so E_bound ends up
                // outermost — matching `push_ret_frames`' push order
                // (E_bound Hyp, then rest Hyp, then Phase-5 dest Let).
                let dv = self.leaves.intern(pp_expr(&dest_value));
                let fnil = format!("{}.FrameList.FNil", NS);
                let mut post = format!(
                    "({}.FrameList.FLet {} {} {})", NS, dest_id, dv, box_(&fnil));
                if let Some(rest) = rest {
                    let r = self.leaves.intern(pp_expr(&rest));
                    post = format!("({}.FrameList.FHyp {} {})", NS, r, box_(&post));
                }
                if let Some(eb) = e_bound {
                    let b = self.leaves.intern(pp_expr(&eb));
                    post = format!("({}.FrameList.FHyp {} {})", NS, b, box_(&post));
                }
                post
            }
            CertCallPost::Forall { .. } => {
                // The ∀-path (no callee `r == E`) needs the FBind +
                // ret_bound + ens + Approach-A `use_dest_name` assembly.
                // Deferred until a ∀-path fixture exists to bridge-validate
                // it — no fixture Call fn currently takes it
                // (quad_exec / count_down / vec_read are all ret-eq).
                return Err("call-forall-path".to_string());
            }
        };
        Ok(format!("({}.StmData.Call {} {})", NS, box_(&reqs), box_(&post)))
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

        // The shared `_h_ctx_N` counter (mirrors `OblCtx::
        // split_leading_binders`: one increment per HYPOTHESIS frame that
        // trails the mod-var binders — the mod-var bounds, then the
        // invariants, then the cond — while the ∀-binder frames for the
        // mod-vars themselves keep their source names).
        let mut hyp_counter: usize = 0;

        // Havoc-set binders (id, typ leaf) + the parallel bound list.
        // Each modified local is re-quantified `∀ (x : T)`; an int-typed
        // one gets a `_h_ctx_N` type-bound hyp right after (production's
        // `push_mod_var_frames`, BARE `LExpr::var(name)` — no deref,
        // unlike params).
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
            match crate::to_lean_sst_expr::type_bound_predicate(&LExpr::var(name.clone()), &typ) {
                Some(pred) => {
                    let hname = self.text_leaf(&format!("_h_ctx_{}", hyp_counter));
                    hyp_counter += 1;
                    let prop = self.leaves.intern(pp_expr(&pred));
                    bound_entries.push(Some((hname, prop)));
                }
                None => bound_entries.push(None),
            }
        }

        // Standard `invariant` clauses only (at_entry && at_exit). An
        // `invariant_except_break` (at_entry only) or loop-`ensures`
        // (at_exit only) needs the entry/exit distinction the flat shape
        // does not carry. Each becomes a `(_h_ctx_N name, ANNOTATED
        // obligation leaf)` — the annotated leaf serves BOTH the
        // init/maintain obligation AND the ∀-hyp (production reuses the
        // one span_mark'd `LoopInvariant` leaf for both roles, unlike
        // Assert's bare/annotated split).
        let mut inv_entries: Vec<(u64, u64)> = Vec::new();
        for li in invs.iter() {
            if !(li.at_entry && li.at_exit) {
                return Err("loop-nonstandard-invariant".to_string());
            }
            let hname = self.text_leaf(&format!("_h_ctx_{}", hyp_counter));
            hyp_counter += 1;
            let oblig = self.oblig_leaf(&li.inv)?;
            inv_entries.push((hname, oblig));
        }

        // The loop condition: one shared `_h_ctx_N` name for both the
        // maintain hyp (`cond_ann`) and the use hyp (`neg_cond_ann`), the
        // last hyp in the telescope (counter not consumed further).
        let cond_name = self.text_leaf(&format!("_h_ctx_{}", hyp_counter));
        let cond_ann = self.oblig_leaf(cond_exp)?;
        let neg_cond_ann = self.neg_oblig_leaf(cond_exp)?;

        // Decreases snapshot let (`_tactus_d_old_<id>_0 := D`, maintain
        // only) + the body-end decrease obligation.
        let d_old_name = self.text_leaf(&format!("_tactus_d_old_{}_0", loop_id));
        let d_old_val = self.exp_leaf(&decrease[0])?;
        let decrease_oblig = self.decrease_oblig_leaf(&decrease[0], loop_id)?;

        let inv_hyps = self.binder_list(&inv_entries);
        let binders = self.binder_list(&binder_entries);
        let bounds = self.param_bound_list(&bound_entries);

        let body_term = self.stm(body)?;
        Ok(format!(
            "({}.StmData.Loop {} {} {} {} {} {} {} {} {} {})",
            NS,
            box_(&inv_hyps),
            box_(&binders),
            box_(&bounds),
            cond_name,
            cond_ann,
            neg_cond_ann,
            d_old_name,
            d_old_val,
            decrease_oblig,
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
        let leaf_id = self.lexpr_leaf(&shape.leaf);
        let mut term = format!("{}.GoalData.Leaf {}", NS, leaf_id);
        for node in shape.spine.iter().rev() {
            term = match node {
                GoalSpine::Imp(p) => {
                    let h = self.lexpr_leaf(p);
                    format!("{}.GoalData.Imp {} {}", NS, h, box_(&term))
                }
                GoalSpine::All(b) => {
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
    check: &FuncCheckSst,
    theorems: &[Theorem],
    goal_shapes: &[Option<GoalShape>],
) -> Sr<CertBody> {
    let mut s: Serializer<'a> = Serializer::default();

    // fn_map for `render_ctx()` (bootstrap-18) — built EXACTLY as
    // production's (sst_to_lean.rs:503): borrows the krate for the
    // serializer's lifetime. Callee resolution puts plain-spec-fn calls in
    // obligations on the migrated typed-arg path so `&`-param call args
    // deref (head_exec's `tree_head(*t)` → `tree_head t.deref`).
    s.fn_map = krate.functions.iter().map(|f| (&f.x.name, &f.x)).collect();

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
    let mut req_entries: Vec<(u64, u64)> = Vec::new();
    for (i, r) in check.reqs.iter().enumerate() {
        let prop = s.exp_leaf(r)?;
        let hname = s.text_leaf(&format!("h_req{}", i));
        req_entries.push((hname, prop));
    }

    // Ensures leaves (bare) → `FnCtxData.enss`. refWp does NOT read this
    // slot (the `Return` goal uses the annotated obligations below); it is
    // kept for the fall-through documentation + O4 audit.
    let mut ens_leaves: Vec<u64> = Vec::new();
    for e in check.post_condition.ens_exps.iter() {
        ens_leaves.push(s.exp_leaf(e)?);
    }
    // Annotated ensures obligation leaves → the `Return` goal
    // (Ret-annotation, finding-1): production renders each ensures at the
    // return site as a span_mark'd `Postcondition` obligation
    // (`WpCtx::new`); `oblig_leaf` reconstructs the identical text so the
    // goal-side postcondition leaf reuses this id and the two cancel across
    // the W2 bridge.
    let mut ens_oblig: Vec<u64> = Vec::new();
    for e in check.post_condition.ens_exps.iter() {
        ens_oblig.push(s.oblig_leaf(e)?);
    }
    s.pending_ens_oblig = ens_oblig;
    // Return-var name leaf (finding-4): production binds `let <sanitize(ret)>
    // := <e>` before the postcondition (the `Return` walker's
    // `let_bind_synthetic(sanitize(name), …)`). `dest` is the declared
    // `-> (r: T)` name; `None` (unit return) ⇒ no binding.
    s.pending_ret_name = check
        .post_condition
        .dest
        .as_ref()
        .map(|d| s.text_leaf(&crate::to_lean_type::sanitize(d.0.as_str())));

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

    // Body.
    let stm_term = s.stm(&check.body)?;

    // Assemble the FnCtxData term. `.mk` positional order matches the
    // emitted `structure lib.FnCtxData`: typ_params, params, param_bounds,
    // reqs, enss.
    let ctx_term = format!(
        "({}.FnCtxData.mk {} {} {} {} {})",
        NS,
        paren(&s.binder_list(&typ_param_entries)),
        paren(&s.binder_list(&param_entries)),
        paren(&s.param_bound_list(&param_bounds)),
        paren(&s.binder_list(&req_entries)),
        paren(&s.leaf_list(&ens_leaves)),
    );

    // Goal half (N3b): after the SST walk, so SST leaf ids are fixed and
    // matching goal leaves reuse them. One `GoalData` per obligation that
    // carried a spine; `None` (bit_vector/query) are skipped.
    let (goal_term, goal_names) = s.goal_list(theorems, goal_shapes);

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

fn write_cert_file(crate_name: &str, fn_name: &str, body: &CertBody) -> std::io::Result<()> {
    let leaf = cert_leaf_name(fn_name);
    let dir = crate::generate::lean_out_root()
        .join(crate::to_lean_type::sanitize(crate_name))
        .join("cert");
    std::fs::create_dir_all(&dir)?;
    let path = dir.join(format!("{}.cert.lean", leaf));

    let text = render_cert(crate_name, fn_name, &leaf, body);

    // Write atomically-ish: full contents in one call. Determinism: the
    // text is a pure function of the inputs (no timestamps).
    let mut f = std::fs::File::create(&path)?;
    f.write_all(text.as_bytes())?;
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
    let stmt_heads = count(&format!("{}.StmData.Assert", NS))
        + count(&format!("{}.StmData.Assume", NS))
        + count(&format!("{}.StmData.Assign", NS))
        + count(&format!("{}.StmData.Call", NS))
        + count(&format!("{}.StmData.DeadEnd", NS))
        + count(&format!("{}.StmData.Ret", NS))
        + count(&format!("{}.StmData.If", NS))
        + count(&format!("{}.StmData.Loop", NS))
        + count(&format!("{}.StmData.Skip", NS))
        + count(&format!("{}.StmData.Seq", NS));
    // Each StmData head contributes its own `1`. LeafList/BinderList
    // `Cons` under Call/Ret/Loop each add 1 to stm_size.
    let leaf_cons = count(&format!("{}.LeafList.Cons", NS));
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

#[cfg(test)]
#[path = "sst_serialize_tests.rs"]
mod tests;
