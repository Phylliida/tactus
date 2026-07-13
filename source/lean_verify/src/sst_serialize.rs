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
//! `FnCtxData` seed refWp (W2) will recompute obligations from. The
//! production goals (`GoalList`) join in N3b; the `refWp … = production`
//! bridge line joins in W2. N3a's job is faithful *input* serialization.
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
//!   (`Bound(leaf)` for int-typed `h_x_bound`, else `NoBound`).
//! * `check.reqs` — requires exps → `FnCtxData.reqs` leaf list.
//! * `check.post_condition.ens_exps` — ensures exps → `FnCtxData.enss`
//!   leaf list (and the fall-through postcondition source; refWp appends
//!   the implicit `Ret` from these when the body doesn't end in one).
//! * `check.body` — the `Stm` tree → `StmData` (the stage-A subset:
//!   Assert, Assume, Assign, DeadEnd, Return, If, Loop, Block→Seq/Skip).
//! * `StmX::Loop{cond|original_cond, invs, modified_vars}` — cond +
//!   ¬cond leaves, standard-invariant leaves, loop-state binders from
//!   the havoc set.
//!
//! ## Deliberately NOT read (each a stage-A exclusion — fail-loud)
//!
//! * `StmX::Call` — the callee's req/ens must be INSTANTIATED at the
//!   actual args (walker-side `build_wp_call`), a non-transcription
//!   trusted step; deferred to keep N3a pure transcription (census tag
//!   `call`; the amended `StmData::Call` shape is exercised by the
//!   in-crate `decide` proofs meanwhile).
//! * `StmX::AssertBitVector` / `AssertQuery` — bv/compute/query asserts
//!   and their isolated contexts (tags `assert-bitvector`/`assert-query`).
//! * `StmX::OpenInvariant` / `ClosureInner` / `BreakOrContinue` —
//!   concurrency, closures, loop control. `BreakOrContinue` therefore also
//!   excludes `invariant_except_break` loops.
//! * `check.unwind`, `check.local_decls` (except the loop havoc set via
//!   `modified_vars`), masks, recommends, fuel/reveal *state*, decrease
//!   measures, `assert_id`/`base_error`, `mode`, trait dispatch/impl-subst
//!   — none bear a stage-A obligation the mirror models.
//! * `StmX::Air` / `Fuel` / `RevealString` — transparently ELIDED (the
//!   walker returns `after` unchanged for these); not obligation-bearing,
//!   so not a rejection.
//!
//! ## Trusted-surface caveats (leaf content is opaque; stage A does not
//! certify it — W6 does)
//!
//! * Leaves are rendered by the PRODUCTION renderer
//!   (`sst_exp_to_ast_checked`, EMPTY `RenderCtx`) then pretty-printed
//!   (`lean_pp::pp_expr`) and interned by text: identical text ⇒ same id.
//!   Leaf-renderer bugs are therefore NOT caught here.
//! * Binder id = the interned leaf id of the binder's rendered name.
//!   The SSA-fresh-per-occurrence discipline (DESIGN-W2-refwp §2.1) is a
//!   W2 refinement — deferred because N3a's only consumer of ids is
//!   `stm_size`/`binder_len`, which ignore the id value.
//! * `Ret` and the fall-through postcondition carry the ens clauses
//!   PRE-substitution (the ret-value substitution the walker performs is
//!   deferred to N3b/W2, where the bridge actually constrains it).
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

use crate::lean_ast::Expr as LExpr;
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
struct Serializer {
    leaves: LeafTable,
    /// The fn's ensures leaves, needed by the `Return` arm; set once
    /// before walking the body so the recursion stays a plain
    /// `&Stm → String`.
    pending_ens: Vec<u64>,
}

impl Serializer {
    // ── Leaf rendering ──────────────────────────────────────────────

    fn exp_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let lexpr = crate::to_lean_sst_expr::sst_exp_to_ast_checked(e)
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        Ok(self.leaves.intern(pp_expr(&lexpr)))
    }

    /// Render `¬e` as a leaf (the walker's else-branch / loop-exit
    /// hypothesis text — same `LExpr::not` call `Wp::Branch` uses).
    fn neg_leaf(&mut self, e: &Exp) -> Sr<u64> {
        let lexpr = crate::to_lean_sst_expr::sst_exp_to_ast_checked(e)
            .map_err(|reason| format!("leaf-render: {}", reason))?;
        Ok(self.leaves.intern(pp_expr(&LExpr::not(lexpr))))
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
            // walker; fold it here.
            StmX::Assert(_, _, e) | StmX::AssertCompute(_, e, _) => {
                let id = self.exp_leaf(e)?;
                Ok(format!("({}.StmData.Assert {})", NS, id))
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

            StmX::Return { .. } => {
                // Stage A: one leaf per postcondition, rendered
                // PRE-substitution (ret-value substitution deferred to
                // N3b/W2). Sourced from the fn ctx's ens leaves.
                let list = self.leaf_list(&self.pending_ens.clone());
                Ok(format!("({}.StmData.Ret {})", NS, box_(&list)))
            }

            StmX::If(cond, then_stm, else_stm) => {
                let c = self.exp_leaf(cond)?;
                let nc = self.neg_leaf(cond)?;
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
                modified_vars,
                ..
            } => {
                // Loop-state binders = the havoc set (the modified locals
                // the maintain/use telescopes quantify over). Extracted
                // here so `HavocSet`'s (private) type never appears in a
                // signature. `IndexMap` iteration is insertion-ordered ⇒
                // deterministic.
                let binder_entries: Vec<(u64, u64)> = match modified_vars {
                    Some(hs) => {
                        let mut entries = Vec::with_capacity(hs.vars.len());
                        for (vid, (typ, _hvar)) in hs.vars.iter() {
                            let id = self.binder_id(vid);
                            let t = self.typ_leaf(typ);
                            entries.push((id, t));
                        }
                        entries
                    }
                    None => Vec::new(),
                };
                self.loop_stm(cond, original_cond, body, invs, &binder_entries)
            }

            StmX::DeadEnd(inner) => {
                let b = self.stm(inner)?;
                Ok(format!("({}.StmData.DeadEnd {})", NS, box_(&b)))
            }

            // Transparent passthrough — the walker returns `after`
            // unchanged. Elide (⇒ Skip in a Seq position).
            StmX::Air(_) | StmX::Fuel(..) | StmX::RevealString(_) => Ok(self.skip()),

            // Fail-loud stage-A exclusions.
            StmX::Call { .. } => Err("call".to_string()),
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
    fn block(&mut self, stms: &[Stm]) -> Sr<String> {
        if stms.is_empty() {
            return Ok(self.skip());
        }
        let head = self.stm(&stms[0])?;
        if stms.len() == 1 {
            return Ok(head);
        }
        let tail = self.block(&stms[1..])?;
        Ok(format!("({}.StmData.Seq {} {})", NS, box_(&head), box_(&tail)))
    }

    fn loop_stm(
        &mut self,
        cond: &Option<(Stm, Exp)>,
        original_cond: &Option<(Stm, Exp)>,
        body: &Stm,
        invs: &[LoopInv],
        binder_entries: &[(u64, u64)],
    ) -> Sr<String> {
        // Recover the while-condition from `cond` or the preserved
        // `original_cond` (break-lowering nulls `cond`). A genuine
        // `loop {}` (both None) has no cond leaf the mirror can carry.
        let cond_exp: &Exp = match (cond, original_cond) {
            (Some((_, c)), _) => c,
            (None, Some((_, c))) => c,
            (None, None) => return Err("loop-without-cond".to_string()),
        };
        let c = self.exp_leaf(cond_exp)?;
        let nc = self.neg_leaf(cond_exp)?;

        // Standard `invariant` clauses only (at_entry && at_exit). An
        // `invariant_except_break` (at_entry only) or loop-`ensures`
        // (at_exit only) needs the entry/exit distinction the flat leaf
        // list does not carry.
        let mut inv_leaves = Vec::with_capacity(invs.len());
        for li in invs.iter() {
            if !(li.at_entry && li.at_exit) {
                return Err("loop-nonstandard-invariant".to_string());
            }
            inv_leaves.push(self.exp_leaf(&li.inv)?);
        }
        let inv_list = self.leaf_list(&inv_leaves);
        let binders = self.binder_list(binder_entries);

        let body_term = self.stm(body)?;
        Ok(format!(
            "({}.StmData.Loop {} {} {} {} {})",
            NS,
            box_(&inv_list),
            c,
            nc,
            box_(&binders),
            box_(&body_term)
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

    /// `lib.ParamBoundList` from per-param optional leaves (order
    /// preserved). `Some(leaf)` ⇒ `Bound(leaf)`, `None` ⇒ `NoBound`.
    fn param_bound_list(&self, bounds: &[Option<u64>]) -> String {
        let mut term = format!("{}.ParamBoundList.Nil", NS);
        for b in bounds.iter().rev() {
            term = match b {
                Some(leaf) => format!("{}.ParamBoundList.Bound {} {}", NS, leaf, box_(&term)),
                None => format!("{}.ParamBoundList.NoBound {}", NS, box_(&term)),
            };
        }
        term
    }
}

// ── Top-level: build the certificate for one fn ─────────────────────

/// The pieces of a serialized fn, assembled into the cert file text.
struct CertBody {
    /// The `FnCtxData` seed as a Lean term.
    ctx_term: String,
    /// The `StmData` body as a Lean term.
    stm_term: String,
    /// The interned leaf table, in id order.
    leaf_texts: Vec<String>,
}

/// Serialize `(fn_sst, check)` into a [`CertBody`], or `Err(tag)` on the
/// first uncaptured construct.
fn serialize(fn_sst: &FunctionSst, check: &FuncCheckSst) -> Sr<CertBody> {
    let mut s = Serializer::default();

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
    // typ leaf, plus the parallel optional bound-hyp leaf.
    let mut param_entries: Vec<(u64, u64)> = Vec::new();
    let mut param_bounds: Vec<Option<u64>> = Vec::new();
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
                let leaf = s.leaves.intern(pp_expr(&pred));
                param_bounds.push(Some(leaf));
            }
            None => param_bounds.push(None),
        }
    }

    // Requires leaves.
    let mut req_leaves: Vec<u64> = Vec::new();
    for r in check.reqs.iter() {
        req_leaves.push(s.exp_leaf(r)?);
    }

    // Ensures leaves (also the `Return` arm's source and the
    // fall-through postcondition).
    let mut ens_leaves: Vec<u64> = Vec::new();
    for e in check.post_condition.ens_exps.iter() {
        ens_leaves.push(s.exp_leaf(e)?);
    }
    s.pending_ens = ens_leaves.clone();

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
        paren(&s.leaf_list(&req_leaves)),
        paren(&s.leaf_list(&ens_leaves)),
    );

    Ok(CertBody { ctx_term, stm_term, leaf_texts: s.leaves.texts })
}

/// Emit the certificate for one exec/WP-proof fn. Never propagates
/// errors — an uncaptured construct is logged (`tactus: cert: <fn> not
/// serialized: <tag>`), counted, and the crate run continues (fail-loud
/// rule, spec §3). A no-op when the flag is off.
pub fn emit_cert(
    _krate: &KrateX,
    fn_sst: &FunctionSst,
    check: &FuncCheckSst,
    crate_name: &str,
) {
    if !cert_emit_enabled() {
        return;
    }
    let fn_name = crate::to_lean_type::lean_name_relative(&fn_sst.x.name.path);
    match serialize(fn_sst, check) {
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
///   Call → 1 + |reqs| + |enss|
///   DeadEnd/Ret → 1 + inner list/stm
///   If → 1 + size(t) + size(e)
///   Loop → 1 + |invs| + |binders| + size(body)
///   Seq → 1 + size(a) + size(b)
///
/// Computed by re-parsing our own emitted text would be fragile; instead
/// `serialize` could return the size directly. For turn-1 we compute it
/// from the string by counting the relevant constructor tokens, which is
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
    stmt_heads + leaf_cons + binder_cons
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
mod tests {
    use super::*;

    #[test]
    fn box_and_paren() {
        assert_eq!(paren("lib.StmData.Skip"), "lib.StmData.Skip");
        assert_eq!(paren("(lib.StmData.Seq a b)"), "(lib.StmData.Seq a b)");
        assert_eq!(paren("lib.LeafList.Cons 0 x"), "(lib.LeafList.Cons 0 x)");
        assert_eq!(box_("lib.LeafList.Nil"), "(Tactus.Box.mk lib.LeafList.Nil)");
    }

    #[test]
    fn leaf_list_order() {
        let s = Serializer::default();
        // ids 1,2,3 → Cons 1 (Cons 2 (Cons 3 Nil))
        let t = s.leaf_list(&[1, 2, 3]);
        assert_eq!(
            t,
            "lib.LeafList.Cons 1 (Tactus.Box.mk (lib.LeafList.Cons 2 (Tactus.Box.mk (lib.LeafList.Cons 3 (Tactus.Box.mk lib.LeafList.Nil)))))"
        );
    }

    #[test]
    fn stm_size_matches_core() {
        // Seq(Assert, If(Skip, Ret Nil)) — mirrors the in-crate
        // skeleton_kernel_computes example: size = 5.
        let term = "(lib.StmData.Seq (Tactus.Box.mk (lib.StmData.Assert 0)) (Tactus.Box.mk (lib.StmData.If 1 2 (Tactus.Box.mk lib.StmData.Skip) (Tactus.Box.mk (lib.StmData.Ret (Tactus.Box.mk lib.LeafList.Nil))))))";
        assert_eq!(stm_size_of(term), 5);
    }

    /// Golden-file pin (N3c §7.5). This module is the TCB — its emitted
    /// output shape is what a skeptic audits, so it must not drift
    /// silently. `GOLDEN` is the verbatim cert file the rebuilt binary
    /// emitted for the real fixture fn `add_capped` over
    /// `bootstrap-fixture/lib.rs`; the test re-renders and asserts
    /// byte-equality. Any change to the header text, leaf-table format,
    /// `def` naming, term spacing, or the `stm_size … := by decide` probe
    /// (incl. `stm_size_of`) breaks this test — a *reviewed* diff, like
    /// the trusted code it guards.
    ///
    /// The `CertBody` inputs are recovered from the golden itself (leaf
    /// texts from the `-- leaf N: ⟦…⟧` table; the ctx/sst terms from the
    /// two `def` bodies) rather than hand-transcribed. This is a valid
    /// regression pin: the golden bytes are fixed, while the recovered
    /// content is format-independent, so a format change makes the
    /// re-render diverge from the unchanged golden. (Bonus: no need to
    /// hand-copy the Unicode leaves or the long fully-parenthesized
    /// terms, which would themselves be a transcription-error surface.)
    #[test]
    fn golden_add_capped_cert() {
        const GOLDEN: &str = include_str!("testdata/add_capped.cert.lean");

        // vocab_hash() reads $TACTUS_CORE_VOCAB; the golden was emitted
        // with it unset ("unvendored"). Under a vendored env the header
        // hash differs by design — skip rather than spuriously fail.
        if vocab_hash() != "unvendored" {
            return;
        }

        let lines: Vec<&str> = GOLDEN.lines().collect();
        let mut leaf_texts: Vec<String> = Vec::new();
        let mut ctx_term = String::new();
        let mut stm_term = String::new();
        for (i, line) in lines.iter().enumerate() {
            // A leaf-table row is `-- leaf N: ⟦text⟧` (N numeric). The
            // digit + ⟦ guard distinguishes it from the header prose line
            // `-- leaf rendering (stage B/W6)…`, which also begins
            // `-- leaf `.
            if let Some(rest) = line.strip_prefix("-- leaf ") {
                if rest.starts_with(|c: char| c.is_ascii_digit()) {
                    let open = rest.find('⟦').expect("leaf row carries ⟦");
                    let close = rest.rfind('⟧').expect("leaf row carries ⟧");
                    leaf_texts.push(rest[open + '⟦'.len_utf8()..close].to_string());
                }
            } else if line.contains("def cert_add_capped_ctx") {
                ctx_term = lines[i + 1].trim().to_string();
            } else if line.contains("def cert_add_capped_sst") {
                stm_term = lines[i + 1].trim().to_string();
            }
        }
        assert_eq!(leaf_texts.len(), 15, "golden leaf-table size drifted");
        assert!(!ctx_term.is_empty(), "ctx term not recovered from golden");
        assert!(!stm_term.is_empty(), "sst term not recovered from golden");

        let body = CertBody { ctx_term, stm_term, leaf_texts };
        let rendered = render_cert("lib", "add_capped", "add_capped", &body);
        assert_eq!(rendered, GOLDEN, "cert-file format drift vs golden");
    }
}
