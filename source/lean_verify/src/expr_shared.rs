//! Helpers shared between the VIR-AST renderer (`to_lean_expr.rs`) and
//! the SST renderer (`to_lean_sst_expr.rs`).
//!
//! ## Why two renderers, and why shared helpers instead of full unification
//!
//! VIR-AST and SST are genuinely different trees at different pipeline
//! stages. VIR-AST renders spec fn bodies, proof fn requires/ensures/
//! goals, and decreases clauses. SST renders exec fn bodies and the
//! `CheckDecreaseHeight` termination obligation. Many variants don't
//! cross: VIR-AST has `Block` / `Match` / `Ctor` / `Place`; SST has
//! `CheckDecreaseHeight` / `CallFun::InternalFun` / a flattened
//! statement sequence.
//!
//! A full trait-based unification (`trait ExprLike`) was investigated
//! and rejected — half the variants are asymmetric, so a shared trait
//! would still require per-impl case-splits for the asymmetric half,
//! netting boilerplate without eliminating it. Routing callee-spec
//! inlining through SST (so `to_lean_expr.rs` is purely for spec/proof
//! fns) was also rejected — `FuncCheckSst` is built per-fn during
//! verification rather than prebuilt in the krate, so accessing a
//! callee's SST would require invasive changes to Verus's compilation
//! pipeline. See DESIGN.md § "Two parallel expression renderers" for
//! the full reasoning.
//!
//! What remains: each helper here corresponds to a rule that BOTH
//! renderers must apply identically. The exec-fn WP path inlines
//! callee require/ensure via the VIR renderer while the callee's own
//! theorem renders via the SST renderer; divergence between the two
//! would produce a silent mismatch between the spec Tactus checks and
//! the spec the callee actually proved. Centralising each rule here
//! makes divergence a compile error rather than a runtime
//! disagreement.

use std::collections::HashMap;

use vir::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, Dt, FieldOpr, Fun, FunctionX, Ident,
    InequalityOp, IntRange, RealArithOp, Typ, TypDecoration, TypX, VarIdent,
};

use crate::lean_ast::{BinOp as L, Expr as LExpr, ExprNode};
use crate::lean_name::LeanName;
use crate::to_lean_type::{lean_name, sanitize, short_name};

// ── RenderCtx ────────────────────────────────────────────────────────
//
// Context passed to expression renderers (VIR-AST and SST). Carries
// information that comes from OUTSIDE the local expression structure
// — currently the fn_map for trait-method param-typ lookups, but
// designed to grow as more typing-from-outside needs surface.
//
// The motivation: rendering a class-method-call site needs to know
// the class signature's expected param typs (so args can be coerced
// to wrapper-typed receivers for `&self` / `&mut self` methods).
// Without a context, the renderer only knows the arg's local typ
// and falls back to TypeAnnot-with-wrong-typ, which is what caused
// the test_old_view_trait_dispatch_probe failure pre-RenderCtx.
//
// Pattern: similar to the existing `BinderCtx` for VIR-AST (which
// tracks per-binder typs from fn params), `RenderCtx` carries
// codegen-time-known info that the renderer otherwise lacks.

/// Function lookup borrowed by `RenderCtx`. Same shape as
/// `sst_to_lean::FnMap` — declared here too so `expr_shared` doesn't
/// depend on `sst_to_lean`.
thread_local! {
    /// Per-datatype constructor-field DECLARED typs, all variants:
    /// Path → (typ params, variant name → [(raw field name, typ)]).
    /// Installed by `generate::install_datatype_field_bounds` alongside
    /// `DATATYPE_FIELDS` (same ambient-table idiom, see emit_ctx.rs).
    /// Why: spec-mode VIR ERASES `Box::new`/`Rc::new` at constructor
    /// argument slots — the arg expr is stamped BARE while the declared
    /// slot is `Decorate(Box, …)` — so the renderer needs the declared
    /// typ to re-materialize the `.mk` wrap. The ctor-position sibling
    /// of the RC4 call-arg bridge (`fn_param_typs`).
    static CTOR_FIELD_TYPS: std::cell::RefCell<
        HashMap<vir::ast::Path, (Vec<Ident>, HashMap<String, Vec<(String, Typ)>>)>,
    > = std::cell::RefCell::new(HashMap::new());
}

/// Install the ctor-field-typs table (see `CTOR_FIELD_TYPS`).
pub(crate) fn set_ctor_field_typs(
    map: HashMap<vir::ast::Path, (Vec<Ident>, HashMap<String, Vec<(String, Typ)>>)>,
) {
    CTOR_FIELD_TYPS.with(|m| *m.borrow_mut() = map);
}

/// The DECLARED typ of constructor field `field` of `path::variant`,
/// instantiated with the ctor's typ args. `None` when the datatype is
/// unknown (cross-crate opaque) — callers skip coercion, preserving
/// today's rendering.
pub(crate) fn ctor_field_typ(
    path: &vir::ast::Path,
    variant: &str,
    field: &str,
    typ_args: &[Typ],
) -> Option<Typ> {
    CTOR_FIELD_TYPS.with(|m| {
        let m = m.borrow();
        let (tps, variants) = m.get(path)?;
        let fields = variants.get(variant)?;
        let (_, ftyp) = fields.iter().find(|(n, _)| n == field)?;
        if !typ_args.is_empty() && typ_args.len() == tps.len() {
            let substs: HashMap<Ident, Typ> =
                tps.iter().cloned().zip(typ_args.iter().cloned()).collect();
            Some(vir::sst_util::subst_typ(&substs, ftyp))
        } else {
            Some(ftyp.clone())
        }
    })
}

/// The DECLARED field names of `path::variant`, in declaration order.
/// `None` when the datatype is unknown (cross-crate opaque / not in the
/// installed table). Used by `pattern_to_ast` to render a struct-variant
/// match pattern positionally: Lean requires ALL constructor fields be
/// present, but a Rust pattern with `{ position, .. }` (or fields in
/// non-declaration order) leaves the VIR `pats` incomplete / reordered.
/// The caller fills omitted fields with `_` and reorders to declaration
/// order using this list.
pub(crate) fn ctor_field_names(path: &vir::ast::Path, variant: &str) -> Option<Vec<String>> {
    CTOR_FIELD_TYPS.with(|m| {
        let m = m.borrow();
        let (_tps, variants) = m.get(path)?;
        let fields = variants.get(variant)?;
        Some(fields.iter().map(|(n, _)| n.clone()).collect())
    })
}

pub type RenderFnMap<'a> = HashMap<&'a Fun, &'a FunctionX>;

/// Render-time value substitution map. Each entry maps a variable
/// name (as it appears in the source AST being rendered) to a
/// `(rendered_value, value_typ)` pair: the LExpr to substitute, plus
/// the Lean-level typ that LExpr has post-substitution.
///
/// Used by `RenderCtx::lookup_subst` to bridge the substituted value
/// to the slot's expected typ at each `Var` rendering site. This
/// closes the "claimed-typ-lies" gap that LExpr-level substitute
/// can't address: at the Var site, the AST node carries the slot's
/// expected typ (`expr.typ`), while the map's entry carries the
/// value's actual typ — together they let `coerce_lexpr` bridge
/// per-use-site, instead of pre-coercing at map-build time toward
/// a single direction.
pub type RenderValueSubst<'a> = HashMap<LeanName, (LExpr, Typ)>;

/// Render context: typing info available to expression renderers.
///
/// * `fn_map` — function lookup for callee param-typ inspection
///   (`fn_param_typs`). Used at every call rendering site to bridge
///   args to the callee's expected param typs.
/// * `value_subst` — typed substitution map applied during render at
///   value sites (Var, VarAt, ReadPlace+Local). Stores values at the
///   callee local's **Lean-level storage typ** (e.g., `Tactus.MutRef
///   T` for `&mut` params). The renderer's `apply_ref_coercion_if_needed`
///   bridges from storage typ to the surrounding context's slot typ
///   at each use — driven by `structural_typ` which consults the
///   inlining `BinderCtx` (populated with mut-param storage typs).
/// * `value_subst_pre` — alternative substitution map for **pre-state
///   contexts** (inside Verus `Old(_)` markers). The renderer swaps
///   to this map when entering an `Old` subtree; same shape and storage
///   convention as `value_subst`, but maps each callee mut-param to
///   the caller's pre-call value rather than the post-state existential.
///
/// Construct with `RenderCtx::empty()` for tests or rendering paths
/// without typing info. Use `RenderCtx::with_fn_map(&fn_map)` or one
/// of the value-subst variants for production rendering at codegen
/// entry points.
#[derive(Clone, Copy)]
pub struct RenderCtx<'a> {
    pub fn_map: Option<&'a RenderFnMap<'a>>,
    pub value_subst: Option<&'a RenderValueSubst<'a>>,
    pub value_subst_pre: Option<&'a RenderValueSubst<'a>>,
    /// In-scope binders' **Lean-level** typs (post-shadow): wrapper-
    /// decorated for `&`-only params (e.g. `&self` → `&Bar`), stripped
    /// for body-shadowed `&mut` params. Seeded from the fn's params
    /// (the `WpCtx::caller_param_typs` map, built identically to the
    /// Exp path's `binder_ctx_from_params`).
    ///
    /// Consulted at Field / IsVariant projection sites so the `.deref`
    /// count matches the actual Lean wrapper depth of the receiver,
    /// rather than the SST expression's spanned typ — which Verus may
    /// have stripped of decorations the Lean binder still carries (the
    /// `self.v` vs `self.deref.v` case). Mirrors `to_lean_expr`'s
    /// `BinderCtx` + `lean_level_wrap_count` on the Exp-rendering side.
    /// `None` outside per-fn body/ensures rendering (falls back to the
    /// spanned typ — identical to the prior behaviour).
    pub binder_typs: Option<&'a HashMap<VarIdent, Typ>>,
    /// Let-bound locals' believed Lean typs, recorded by the WP walker
    /// as it pushes `Let` frames (P2, DESIGN-typed-renderer.md):
    /// `name → (typ the binding was coerced into, trusted)`. Keyed by
    /// [`crate::lean_name::LeanName`] because `Wp::Let` carries the
    /// rendered name, and the Var arm computes it before lookup anyway.
    /// `trusted` = whether the RHS's actual typ came from a D3-trusted
    /// source — untrusted entries behave exactly like claimed typs
    /// (reset at Box/Unbox in `exp_to_typed`); trusted entries lift
    /// the resets. `im::HashMap` for O(1) clone in the walker's
    /// extend-per-frame pattern.
    pub let_binder_typs: Option<&'a im::HashMap<crate::lean_name::LeanName, (Typ, bool)>>,
    /// Inlining-render mode: suppresses the `apply_ref_coercion_if_needed`
    /// lift at `ExprX::ReadPlace` sites. Callee-spec inlining substitutes
    /// the rendered form with a CALLER-provided arg that is already
    /// wrapper-typed; the lift would over-wrap. Set via
    /// [`Self::for_inlining`]; read in `to_lean_expr::structural_typ`.
    /// (Replaces the former `READPLACE_LIFT_ENABLED` thread-local —
    /// render-mode state belongs on the ctx that already threads through
    /// the recursion, not in ambient TLS.)
    pub inlining: bool,
}

impl<'a> RenderCtx<'a> {
    /// Empty context — class-method-call rendering falls back to
    /// no-coerce; Var substitution falls through to plain Var.
    pub fn empty() -> Self {
        Self { fn_map: None, value_subst: None, value_subst_pre: None, binder_typs: None, let_binder_typs: None, inlining: false }
    }

    /// Context with fn_map for class-method-call rendering.
    pub fn with_fn_map(fn_map: &'a RenderFnMap<'a>) -> Self {
        Self { fn_map: Some(fn_map), value_subst: None, value_subst_pre: None, binder_typs: None, let_binder_typs: None, inlining: false }
    }

    /// Attach the in-scope binder-typ map (see the `binder_typs` field).
    /// Builder-style so any constructor above composes with it:
    /// `RenderCtx::with_fn_map(&m).with_binder_typs(&pars)`.
    pub fn with_binder_typs(self, binder_typs: &'a HashMap<VarIdent, Typ>) -> Self {
        Self { binder_typs: Some(binder_typs), ..self }
    }

    /// Inlining-render mode (see the `inlining` field). Builder-style.
    pub fn for_inlining(self) -> Self {
        Self { inlining: true, ..self }
    }

    /// Clear the binder map. Inlining renders start with an empty
    /// binder scope by construction (the callee's spec is rendered
    /// against substituted caller values, not the caller's binders) —
    /// this makes that invariant structural at the entry point rather
    /// than dependent on which ctx the caller happened to pass.
    pub fn without_binder_typs(self) -> Self {
        Self { binder_typs: None, ..self }
    }

    /// In-scope binder lookup (see the `binder_typs` field). `None`
    /// when no binder map is attached or the var isn't in scope —
    /// callers fall back to the expression's spanned typ.
    pub fn binder(&self, v: &VarIdent) -> Option<&'a Typ> {
        self.binder_typs.and_then(|m| m.get(v))
    }

    /// Attach the walker's let-binder typ map (see the
    /// `let_binder_typs` field). Builder-style.
    pub fn with_let_binder_typs(
        self,
        m: &'a im::HashMap<crate::lean_name::LeanName, (Typ, bool)>,
    ) -> Self {
        Self { let_binder_typs: Some(m), ..self }
    }

    /// Let-binder lookup (see the `let_binder_typs` field).
    pub fn let_binder(&self, name: &crate::lean_name::LeanName) -> Option<&'a (Typ, bool)> {
        self.let_binder_typs.and_then(|m| m.get(name))
    }

    /// Context with both fn_map and a render-time value substitution
    /// map. Used by call-site inlining paths (`emit_call_precondition_theorem`,
    /// `push_post_call_frames`) where mut-param substitution needs
    /// typed bridging at each use site.
    pub fn with_fn_map_and_value_subst(
        fn_map: &'a RenderFnMap<'a>,
        value_subst: &'a RenderValueSubst<'a>,
    ) -> Self {
        Self { fn_map: Some(fn_map), value_subst: Some(value_subst), value_subst_pre: None, binder_typs: None, let_binder_typs: None, inlining: false }
    }

    /// Context with fn_map + both post-state and pre-state value
    /// substitution maps. Used by `push_post_call_frames` to set up
    /// the inlining renderer with everything needed for transparent
    /// pre/post translation: the value_subst handles post-state refs,
    /// the value_subst_pre handles refs inside `Old(_)` markers, and
    /// the renderer swaps between them based on context.
    pub fn with_fn_map_and_value_subst_pair(
        fn_map: &'a RenderFnMap<'a>,
        value_subst: &'a RenderValueSubst<'a>,
        value_subst_pre: &'a RenderValueSubst<'a>,
    ) -> Self {
        Self {
            fn_map: Some(fn_map),
            value_subst: Some(value_subst),
            value_subst_pre: Some(value_subst_pre),
            binder_typs: None,
            let_binder_typs: None,
            inlining: false,
        }
    }

    /// Variant of `self` with `value_subst` swapped to `value_subst_pre`.
    /// Used at the `Old(_)` rendering site to switch the inner expression
    /// into a pre-state context: every Var/ReadPlace lookup against the
    /// new active subst returns the pre-state value (caller's pre-call
    /// arg) rather than the post-state existential.
    pub fn with_pre_state_subst(&self) -> Self {
        Self {
            fn_map: self.fn_map,
            value_subst: self.value_subst_pre,
            value_subst_pre: self.value_subst_pre,
            binder_typs: self.binder_typs,
            let_binder_typs: self.let_binder_typs,
            // Mid-render swap — the inlining mode must survive it (the
            // thread-local this field replaced persisted across the
            // whole recursive render).
            inlining: self.inlining,
        }
    }

    /// Look up a callee's declared param typs. Returns `None` when the
    /// Fun isn't in fn_map (cross-crate, or no fn_map in this RenderCtx).
    /// Caller falls back to no-coerce rendering when `None` — gracefully
    /// degrades for the cross-crate case rather than panicking.
    ///
    /// Works for ALL fn calls (class methods, inherent methods, regular
    /// fns), not just trait dispatch — the lookup is structurally the
    /// same. The renderer's call-site bridge applies `coerce_lexpr` from
    /// each arg's rendered typ to the corresponding param typ from this
    /// list, codifying the auto-borrow semantic that Rust applies
    /// implicitly. For trait-resolved calls the decl's typs are what
    /// the class signature uses (the resolved impl might have textually-
    /// different param names but positionally-aligned typs).
    ///
    /// **Param types are returned AS INSTANTIATED at this call site.**
    /// `typ_args` is the call's type-argument list (positional, matching
    /// the callee's `typ_params`). We substitute it into each declared
    /// param type, so a param typed `K` (a type-param) becomes its actual
    /// instantiation — e.g. `Box<Q>` when the call passes `K ↦ Box<Q>`.
    /// This is what lets the call-arg bridge coerce `Q → Box Q` (recovering
    /// the wrapper construction Verus erases at the value level — `Box::new`
    /// in spec position collapses to a bare `*k : Q` in VIR, so the only
    /// surviving signal that a box belongs there is the instantiated param
    /// type). Without the substitution the target would be the abstract
    /// `TypParam(K)` and `coerce_lexpr` could not bridge.
    ///
    /// Substitution fires only when `typ_args.len() == typ_params.len()`
    /// (the unambiguous positional case Verus's call lowering produces —
    /// the same alignment the explicit-type-args head application already
    /// relies on). On any mismatch — or empty `typ_args` (non-generic
    /// call) — it falls through to the declared types, so this is a strict
    /// refinement: zero behaviour change for concrete-param calls, and no
    /// risk of misaligning a substitution.
    /// M6.1 drop-dummy rule: does `ast_simplify` inject the zero-arg
    /// `Const 0` dummy for calls to this callee? (The spec world
    /// renders from the unsimplified vir krate, so the injected arg
    /// must be dropped wherever post-simplify SSTs are rendered —
    /// same predicate as the injector, `injects_zero_arg_dummy`.)
    /// Unknown callees (not in fn_map) answer false — their calls
    /// render as-is and any real mismatch surfaces in elaboration.
    pub fn callee_injects_dummy(&self, fun: &Fun) -> bool {
        self.fn_map
            .and_then(|m| m.get(fun))
            .map_or(false, |f| vir::ast_simplify::injects_zero_arg_dummy(f, false))
    }

    pub fn fn_param_typs(&self, fun: &Fun, typ_args: &[Typ]) -> Option<Vec<Typ>> {
        let fn_map = self.fn_map?;
        let func = fn_map.get(fun)?;
        if !typ_args.is_empty() && typ_args.len() == func.typ_params.len() {
            let typ_substs: HashMap<Ident, Typ> = func
                .typ_params
                .iter()
                .cloned()
                .zip(typ_args.iter().cloned())
                .collect();
            Some(
                func.params
                    .iter()
                    .map(|p| vir::sst_util::subst_typ(&typ_substs, &p.x.typ))
                    .collect(),
            )
        } else {
            Some(func.params.iter().map(|p| p.x.typ.clone()).collect())
        }
    }

    /// Sibling of [`Self::fn_param_typs`] for the RESULT side: the
    /// callee's declared return typ, instantiated with the call-site
    /// typ args. Ground truth for a rendered application's Lean type —
    /// the emitted def's return type is `typ_to_expr` of exactly this
    /// typ — so the typed spine's Call arm reports it as the actual
    /// (B5a, DESIGN-B5-typed-spine-calls.md). The SST claim can differ
    /// by a ref-decoration when the call sits in an inlined `&self`
    /// receiver position: `sst_elaborate` splices the receiver arg
    /// with its call-site claim, which poly.rs needs — the lie is
    /// Lean-perspective-only, so the renderer is the seam.
    pub fn fn_ret_typ(&self, fun: &Fun, typ_args: &[Typ]) -> Option<Typ> {
        let fn_map = self.fn_map?;
        let func = fn_map.get(fun)?;
        if !typ_args.is_empty() && typ_args.len() == func.typ_params.len() {
            let typ_substs: HashMap<Ident, Typ> = func
                .typ_params
                .iter()
                .cloned()
                .zip(typ_args.iter().cloned())
                .collect();
            Some(vir::sst_util::subst_typ(&typ_substs, &func.ret.x.typ))
        } else {
            Some(func.ret.x.typ.clone())
        }
    }

    /// Look up a Var name in the render-time substitution map and,
    /// if present, return the substituted value bridged to `slot_typ`
    /// via `coerce_lexpr`. Returns `None` if no substitution is
    /// configured or the name isn't in the map — callers fall back
    /// to plain `Var(name)` rendering.
    ///
    /// This is the entry point for render-time substitution. By
    /// taking `slot_typ` from the caller (which holds the current
    /// AST node's typ), the bridge uses the slot's expectation
    /// rather than the value's claimed source typ — the architectural
    /// fix for the "claimed-typ-lies" gap that pre-render coercion
    /// can't address.
    pub fn lookup_subst(&self, name: &LeanName, slot_typ: &Typ) -> Option<LExpr> {
        let map = self.value_subst?;
        let (value, value_typ) = map.get(name)?;
        Some(coerce_lexpr(value.clone(), value_typ, slot_typ))
    }

    /// Look up a Var name in the render-time substitution map and
    /// return the substituted value **at its storage typ** — no
    /// bridge applied. The caller is responsible for downstream
    /// coercion (typically via `apply_ref_coercion_if_needed` with
    /// `structural_typ` reporting the storage typ from a populated
    /// BinderCtx).
    ///
    /// Use this in the principled "values live at storage typ;
    /// bridging is the consumer's job" architecture — substitution
    /// is faithful to Lean reality, downstream lifts handle slot
    /// mismatches.
    pub fn lookup_subst_raw(&self, name: &LeanName) -> Option<LExpr> {
        let map = self.value_subst?;
        let (value, _value_typ) = map.get(name)?;
        Some(value.clone())
    }

    /// Storage typ of a mut-param substitution entry. Used by
    /// `structural_typ` to report a binder-shaped value's Lean-level
    /// typ at each use site, so `apply_ref_coercion_if_needed` can
    /// bridge to the surrounding slot. Falls back to None when no
    /// substitution map is configured or the name isn't in it.
    pub fn lookup_subst_typ(&self, name: &LeanName) -> Option<Typ> {
        let map = self.value_subst?;
        map.get(name).map(|(_, t)| t.clone())
    }
}

/// Map a VIR/SST binary op to its structural Lean `BinOp` representation.
///
/// Returns `None` for ops that don't correspond to a Lean structural
/// binary operator — the caller emits those via
/// `App(non_binop_head(op), …)`. SST's exec-fn path rejects everything
/// except `Xor` before reaching the `None` branch; the VIR-AST path
/// accepts all variants for spec/proof fn rendering.
pub(crate) fn binop_to_ast(op: &BinaryOp) -> Option<L> {
    Some(match op {
        BinaryOp::And => L::And,
        BinaryOp::Or => L::Or,
        BinaryOp::Implies => L::Implies,
        BinaryOp::Eq(_) => L::Eq,
        BinaryOp::Ne => L::Ne,
        BinaryOp::Inequality(InequalityOp::Le) => L::Le,
        BinaryOp::Inequality(InequalityOp::Lt) => L::Lt,
        BinaryOp::Inequality(InequalityOp::Ge) => L::Ge,
        BinaryOp::Inequality(InequalityOp::Gt) => L::Gt,
        BinaryOp::Arith(ArithOp::Add(_)) => L::Add,
        BinaryOp::Arith(ArithOp::Sub(_)) => L::Sub,
        BinaryOp::Arith(ArithOp::Mul(_)) => L::Mul,
        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => L::Div,
        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => L::Mod,
        BinaryOp::RealArith(RealArithOp::Add) => L::Add,
        BinaryOp::RealArith(RealArithOp::Sub) => L::Sub,
        BinaryOp::RealArith(RealArithOp::Mul) => L::Mul,
        BinaryOp::RealArith(RealArithOp::Div) => L::Div,
        BinaryOp::Bitwise(BitwiseOp::BitAnd, _) => L::BitAnd,
        BinaryOp::Bitwise(BitwiseOp::BitOr, _) => L::BitOr,
        BinaryOp::Bitwise(BitwiseOp::BitXor, _) => L::BitXor,
        BinaryOp::Bitwise(BitwiseOp::Shr(_), _) => L::Shr,
        BinaryOp::Bitwise(BitwiseOp::Shl(_, _), _) => L::Shl,
        BinaryOp::Xor
        | BinaryOp::HeightCompare { .. }
        | BinaryOp::StrGetChar
        | BinaryOp::Index(_, _)
        | BinaryOp::IeeeFloat(_) => return None,
    })
}

/// Head identifier used when a VIR/SST binop is expressed as a 2-arg
/// function call rather than a structural `BinOp` — i.e., the `None`
/// return from [`binop_to_ast`]. These render as stand-ins; the exec-fn
/// SST path reaches `Xor` and `StrGetChar`. The spec/proof VIR path
/// reaches all cases.
pub(crate) fn non_binop_head(op: &BinaryOp) -> &'static str {
    match op {
        // Lean's `Bool.xor` — dotted so it bypasses the sanity allowlist
        // and resolves natively. Verus's `BinaryOp::Xor` is logical xor on
        // bools (bitwise xor on ints goes through `BitwiseOp::BitXor`,
        // which already has a structural `BinOp::BitXor`).
        BinaryOp::Xor => "Bool.xor",
        BinaryOp::HeightCompare { .. } => "Tactus.heightLt",
        // Verus's `verus_builtin::strslice_get_char(s, i)` — codepoint-
        // indexed string lookup. Lean's `String.get` is byte-indexed and
        // returns Lean's `Char`, while Verus's surface returns `char` →
        // Tactus's `Nat`. The prelude provides `Tactus.strGetChar` as
        // the right adapter (see TactusPrelude.lean for semantics).
        BinaryOp::StrGetChar => "Tactus.strGetChar",
        BinaryOp::Index(_, _) => "Tactus.index",
        BinaryOp::IeeeFloat(_) => "Tactus.floatOp",
        _ => "?",
    }
}

/// Render the non-float arms of a `Constant`.
///
/// Returns `None` for `Real` / `Float32` / `Float64` so each caller
/// decides: the VIR-AST path emits a type-annotated literal (Verus
/// accepts floats in spec code); the SST path rejects them as
/// unsupported in exec-fn bodies.
pub(crate) fn const_to_node_common(c: &Constant) -> Option<ExprNode> {
    Some(match c {
        Constant::Bool(b) => ExprNode::LitBool(*b),
        Constant::Int(n) => ExprNode::Lit(n.to_string()),
        Constant::StrSlice(s) => ExprNode::LitStr(s.to_string()),
        Constant::Char(c) => ExprNode::LitChar(*c),
        Constant::Real(_) | Constant::Float32(_) | Constant::Float64(_) => return None,
    })
}

/// `true` iff VIR's `IntRange` renders as Lean `Int` (the signed side
/// plus unbounded `Int`, and also fixed-width u-types — their spec-mode
/// subtraction is mathematical rather than truncating). The complement
/// — `Nat`, `USize`, `Char` — renders as `Nat`. Keep in sync with
/// `to_lean_type::typ_to_expr`.
///
/// Shared between the SST path (`clip_to_node_checked`), the VIR-AST
/// path (`to_lean_expr.rs`), and `coerce_lexpr`'s sort reconciliation,
/// so numeric-sort decisions stay consistent across both renderers —
/// relevant because exec-fn callees inline their `require`/`ensure`
/// via the VIR path while their own theorems render via the SST path.
/// Divergence would produce a different inlined spec than the callee
/// actually proved (silent soundness hole).
pub(crate) fn renders_as_lean_int(range: &IntRange) -> bool {
    matches!(
        range,
        IntRange::Int | IntRange::I(_) | IntRange::ISize | IntRange::U(_)
    )
}

/// The `IntRange` of a typ, peeling boxing / decorations. `None` for
/// non-integer typs (Bool, Prop, datatypes, …).
pub(crate) fn int_range_of(typ: &Typ) -> Option<IntRange> {
    let mut t = &**typ;
    loop {
        match t {
            TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => t = &**inner,
            TypX::Int(r) => return Some(*r),
            _ => return None,
        }
    }
}

/// Resolve a `Clip` coercion to its Lean wrapper name, given whether
/// the source and destination types render as Lean `Int` (per
/// [`renders_as_lean_int`]).
///
///   * `(Int, Nat)` → `Some("Int.toNat")`
///   * `(Nat, Int)` → `Some("Int.ofNat")`
///   * same-side    → `None` (passthrough)
///
/// Both renderers' Clip arms consult this table so the coercion rule
/// lives in one place. Dropping a coercion in the mixed case (the old
/// SST behaviour) caused a soundness hole: `x as int - y as int` for
/// `x, y : u8` rendered as `x - y` on `Nat`, which truncates negatives
/// to zero. Forcing subtraction to happen over `Int` — via
/// `Int.ofNat` — makes the lower-bound refinement check actually fire.
pub(crate) fn clip_coercion_head(src_int: bool, dst_int: bool) -> Option<&'static str> {
    match (src_int, dst_int) {
        (true, false) => Some("Int.toNat"),
        (false, true) => Some("Int.ofNat"),
        _ => None,
    }
}

/// Apply a clip coercion wrapper to an already-rendered `LExpr`, using
/// [`clip_coercion_head`] to pick the wrapper name. Passthrough
/// (same-side) returns the expression unchanged.
pub(crate) fn apply_clip_coercion(src_int: bool, dst_int: bool, inner: LExpr) -> LExpr {
    match clip_coercion_head(src_int, dst_int) {
        Some(head) => LExpr::app1(LExpr::var_lit(head), inner),
        None => inner,
    }
}

/// Build a Lean constructor expression from an already-rendered
/// `Vec<LExpr>` of field values.
///
/// * `Dt::Path(path)` + variant → named ctor `TypeName.variant arg₁ arg₂ …`,
///   with the special case that a struct's sole variant (whose name
///   equals the type's short name) renders as `TypeName.mk` —
///   matching Lean's auto-generated `.mk` for single-field-group
///   inductives.
/// * `Dt::Tuple(_)` → Lean tuple syntax `(a, b, c)` (sugar for
///   `Prod.mk a (Prod.mk b c)`). Distinct from anon-ctor `⟨a, b, c⟩`
///   because the bare anon-ctor needs a known expected type — which
///   isn't available at let-bindings (`let t := ⟨x, 0⟩` fails to
///   elaborate). Tuple syntax infers `Prod` from the operands and
///   works without context.
///
/// Both expression renderers (VIR-AST and SST) use this so the ctor
/// naming convention can't drift between the proof-fn / spec-fn path
/// and the exec-fn WP path. Caller is responsible for rendering the
/// fields via their respective per-tree walker.
pub(crate) fn ctor_node(
    dt: &Dt,
    variant: &Ident,
    rendered_fields: Vec<LExpr>,
) -> ExprNode {
    match dt {
        Dt::Path(path) => {
            let type_name = lean_name(path);
            let variant_seg = if variant.as_str() == short_name(path) {
                "mk".to_string()
            } else {
                sanitize(variant)
            };
            let head = format!("{}.{}", type_name, variant_seg);
            // Constructor heads are dotted Lean names like `MyType.Variant`.
            // They're path-derived (not VarIdent), but the path has already
            // been sanitized via `lean_name`. `synthetic` wraps verbatim.
            let head_name = crate::lean_name::LeanName::synthetic(head);
            if rendered_fields.is_empty() {
                ExprNode::Var(head_name)
            } else {
                ExprNode::App {
                    head: Box::new(LExpr::var(head_name)),
                    args: rendered_fields,
                }
            }
        }
        Dt::Tuple(_) => ExprNode::Tuple(rendered_fields),
    }
}

/// Array-literal rendering, shared by the VIR-AST and SST paths (F3,
/// DESIGN-lean-all-proofs-followons.md). Verus's `[T; N]` maps to Lean
/// core `Vector T N` (`to_lean_type`), so a literal in Array-typed
/// position must render `#v[a, b, c]` — a bare `[a, b, c]` is a `List`
/// and mistypes everywhere the array type is expected (the
/// `{ deref := [a, b, c] }` family: `seq![a, b]` lowers through vstd's
/// `View for [T; N]`, wrapping the literal in `Tactus.Ref.mk` ascribed
/// at `Vector`). Anything else (`Primitive::Slice` → `List`) keeps the
/// List literal. `#v[…]` + the `Tactus.Ref.mk` wrapper validated
/// empirically on the pinned toolchain (Lean 4.25.0).
/// F2b (DESIGN-lean-all-proofs-followons.md): a Verus `decreases`
/// measure of Int-rendered type (`int`, `iN`, `isize`) becomes a
/// `termination_by` value that Lean wraps in `sizeOf` — for `Int`
/// that unfolds to a raw `Int.rec` omega cannot see through, so
/// every such decreasing goal was stuck. Verus's decreases semantics
/// for int measures IS "a nonnegative ordinal" (nonnegativity is part
/// of the Z3-side decreases obligation), and `Int.toNat` is the
/// canonical embedding of that semantics — the same kind of type-level
/// mapping as the standing `uN → Nat` clip policy. Wrapping makes the
/// decreasing goals Nat `<`: omega-native, with the branch guards
/// supplying nonnegativity. Uniform on every Int-rendered measure and
/// visible in the emitted `termination_by`; Nat-rendered (`nat`, `uN`,
/// `usize`) and non-numeric (datatype height / sizeOf) measures pass
/// through unchanged.
pub(crate) fn wrap_int_measure(rendered: LExpr, d: &vir::ast::Expr) -> LExpr {
    let peeled = crate::to_lean_type::peel_typ_wrappers(&d.typ);
    match &**peeled {
        TypX::Int(
            vir::ast::IntRange::Int
            | vir::ast::IntRange::I(_)
            | vir::ast::IntRange::ISize,
        ) => LExpr::app1(LExpr::var_lit("Int.toNat"), rendered),
        _ => rendered,
    }
}

/// Dispatches on the PEELED typ only — decoration handling is the
/// caller's job and differs per path: the VIR renderer's
/// `apply_ref_coercion_if_needed` bridges decorations for literals
/// already (its `structural_typ` treats `ArrayLiteral` as producing an
/// undecorated value), while the SST arm must wrap explicitly (see the
/// `ExpX::ArrayLiteral` arm) — wrapping here would double-wrap the VIR
/// side.
pub(crate) fn array_literal_node(rendered_elems: Vec<LExpr>, typ: &Typ) -> LExpr {
    let peeled = crate::to_lean_type::peel_typ_wrappers(typ);
    match &**peeled {
        TypX::Primitive(vir::ast::Primitive::Array, _) =>
            LExpr::new(ExprNode::VectorLit(rendered_elems)),
        _ => LExpr::new(ExprNode::ArrayLit(rendered_elems)),
    }
}

/// Render the `is_<variant>` discriminator for a `UnaryOpr::IsVariant`
/// applied to an already-rendered receiver expression. Lean's inductive
/// derivation provides these accessors automatically: `x.isSome` for
/// `Option.Some`, `x.isOk` for `Result.Ok`, etc. Both renderers call
/// this so the naming convention stays consistent.
pub(crate) fn is_variant_node(variant: &Ident, inner: LExpr) -> ExprNode {
    LExpr::field_proj(inner, format!("is{}", variant)).node
}

// ── Reserved identifier conventions ────────────────────────────────────
//
// Tactus codegen produces several kinds of synthetic Lean identifiers.
// The conventions below describe what each prefix/suffix means and
// when to use which. A new contributor adding a gensym site or a
// prelude def should pick the matching convention rather than invent
// a new one.
//
// **Convention 1: `_tactus_<role>_<id>` prefix** — codegen-internal
// gensyms and theorem names. Reserved by virtue of leading underscore
// + `tactus_` prefix; Rust source can't produce these as identifiers.
// Examples:
//   * `_tactus_d_old_<loop_id>` — pre-body decrease snapshot per loop
//     (`build_wp_loop`).
//   * `_tactus_ret_<id>` — post-call ∀-bound return value
//     (`build_call_substitutions`).
//   * `_tactus_mut_post_<id>` — post-call existential for a `&mut`
//     arg (`build_call_substitutions`).
//   * (`_tactus_field_<idx>` was previously used for accessor-fn body's
//     field-extract local. Now both accessor-fn bodies and height-fn
//     pattern binders use the field's declared name directly via
//     `to_lean_fn::field_name` — same name the inductive's variant
//     ctor uses — so the synthetic convention is no longer needed.)
//   * `_tactus_<kind>_<fn>_at_<loc>_<id>` — per-obligation theorem
//     names (`build_theorem_name`).
//   * `_tactus_assoc_<X>_<N>` — fresh implicit type binder lifted
//     from a `<X as T>::N` projection in a blanket impl signature
//     (`impl_subst::ImplSubst::build`, Bug B step 2). One per
//     unique (X, T, N) triple discovered in the impl's signature
//     typs. Mapped to a synthesised `TypEquality` bound so existing
//     `trait_bounds_to_ast` machinery augments the trait bracket
//     (`[View A _tactus_assoc_A_V]`) from the same source.
//
// **Convention 2: `<x>_at_pre_tactus` SUFFIX** — pre-state references
// for `&mut` params in callee-spec inlining. The ONLY suffix-style
// reserved name; every other convention is a prefix. Justification:
// the suffix preserves the original param name `x` at the start of
// the identifier, which keeps Lean error messages readable
// (`x_at_pre_tactus = 5` is more legible than
// `_tactus_at_pre_x = 5`). See `varat_pre_name`.
//
// **Convention 3: `tactus_<name>` (no underscore prefix)** — user-
// visible Lean tactics defined in `TactusPrelude.lean`. Users may
// reference these in `proof { … }` blocks or via the
// `#[verifier::tactus_tactic("…")]` attribute. Examples:
//   `tactus_auto`, `tactus_first`,
//   `tactus_case_split`, `tactus_usize_bound`.
// No leading underscore because they're meant to be human-typed.
// (`tactus_peel` was deleted in B4: the emitter generates the peel
// structure explicitly instead of calling a recursive macro.)
//
// **Convention 4: Bare names in `TactusPrelude.lean`** — axioms /
// defs that are user-visible but read-only. Examples:
//   `arch_word_bits`, `arch_word_bits_valid`, `usize_hi`, `isize_hi`.
// These look unprotected but actually can't collide with user code:
// Tactus generates user definitions inside `namespace
// crate.module`, while these live at top-level in TactusPrelude.
// Lean's namespace resolution prevents the collision. Listed in
// `sanity::name_resolves`'s allowlist so the post-codegen check
// doesn't flag them as unresolved.
//
// **Convention 5: `<base>_α<N>` suffix** — alpha-rename freshness
// suffix produced by `lean_ast::fresh_name` (#116). When
// `substitute` detects that a binder would capture a free variable
// from the substitution, it generates a fresh name by appending
// `_α<N>` (smallest N ≥ 1 not in the forbidden set) and rewrites
// the binder + body in lockstep before applying the main
// substitution. The Greek letter α makes the alpha-renaming origin
// obvious in error messages and generated Lean. This is the only
// convention that uses Unicode — every other reserved name is
// ASCII. User code can technically produce identifiers containing
// Unicode α (Lean accepts them), but `<base>_α<N>` specifically is
// reserved for this purpose; if a user happened to define `x_α1`
// themselves, our forbidden-set check would skip it and pick `_α2`
// instead. See `lean_ast::fresh_name`.
//
// **Gensym mechanism choice**: when generating a `_tactus_<role>_<id>`
// name:
//   * Use Verus's stable identifier (e.g., `StmX::Loop::id`, a
//     `u64` per loop instance) when one is available — gives
//     deterministic output that's stable across runs.
//   * Fall back to `ObligationEmitter::next_id()` (per-fn
//     monotonic counter) when no stable upstream ID exists.
//     Theorem names are namespaced by `fn_name` so per-fn
//     uniqueness is sufficient.
//
// **`sanity::name_resolves` is the canonical allowlist** for names
// that resolve via the prelude rather than via emitted definitions.
// Adding a new prelude def means updating the allowlist.

/// Render a `VarAt(x, Pre)` reference (the post-`old(x)` form Verus
/// uses for pre-state references in `&mut` ensures clauses) as a
/// distinct Lean identifier.
///
/// Why distinct from `Var(x)`: in a callee with `fn bump(x: &mut u8)
/// requires *old(x) < 100 ensures *x == *old(x) + 1`, the VIR-AST
/// ensures contains both `Var(x)` (post-call value) and `VarAt(x,
/// Pre)` (pre-call value). If both rendered to the same Lean name,
/// the ensures would collapse to `x == x + 1` — vacuously false for
/// finite arithmetic, silent translation bug. Rendering `VarAt(x,
/// Pre)` to a syntactically distinct name lets the call-site
/// substitution map send it to the caller's pre-call value while
/// `Var(x)` goes to a fresh existential for the post-call value.
///
/// The `_at_pre_tactus` suffix is reserved (combined with the
/// already-documented `_tactus_` prefix convention, won't collide
/// with user identifiers — Rust source can't produce trailing
/// `_tactus`).
///
/// Shared between the VIR-AST and SST renderers so the rendering
/// rule lives in one place. Divergence would make the
/// substitution-key in `walk_call` (built against VIR-AST shape)
/// fail to match the SST renderer's output for the same VarAt.
pub(crate) fn varat_pre_name(name: &str) -> String {
    format!("{}_at_pre_tactus", name)
}

/// True when a parameter (or local) is an `&mut`-like reference whose
/// Lean binder type should be the `Tactus.MutRef` wrapper.
///
/// Covers three Verus shapes that all denote the same semantic thing
/// (a mutable reference to T):
/// * **Legacy mode**: `is_mut: true` with `typ` = plain `T`. Verus's
///   default mode produces this for `fn f(x: &mut T)`.
/// * **New-mut-ref mode after migration**: `is_mut: false` with
///   `typ` = `TypX::MutRef(T)`. Produced under `-V new-mut-ref` plus
///   `deprecated_postcondition_mut_ref_style(true)`.
/// * **Decorated**: `typ` = `Decorate(MutRef, _, T)`. The decoration-
///   level shape that appears at some VIR sites.
///
/// All three render uniformly as `(x : Tactus.MutRef T)` at the Lean
/// binder via [`crate::to_lean_type::param_binder_typ`]. The shared
/// predicate keeps every site that asks "is this an &mut?" in
/// lockstep — a future Verus-side change to how `&mut` is represented
/// updates one place rather than several. Used by:
/// * `to_lean_fn::wrap_body_with_param_derefs` (decides which params
///   need a body-deref shadow)
/// * `sst_to_lean::build_param_binders` (decides which binders get
///   wrapper-typed)
/// * `sst_to_lean::exec_fn_theorems_to_ast` (decides which params
///   populate `mut_param_names` for the SST rewrite + the pre-state
///   capture frames)
/// * `sst_to_lean::add_param_subst_entries` (decides which callee
///   params need pre/post substitution split)
pub(crate) fn is_mut_ref_typ(typ: &Typ, is_mut: bool) -> bool {
    if is_mut {
        return true;
    }
    match &**typ {
        TypX::MutRef(_) => true,
        TypX::Decorate(TypDecoration::MutRef, _, _) => true,
        _ => false,
    }
}

/// Wrapper name (e.g., `"Tactus.Ref"`) for a reference-like decoration,
/// or `None` for transparent ones (Ghost / Tracked / Never / ConstPtr).
/// Single source of truth — `to_lean_type::typ_to_node` and
/// `to_lean_expr`'s coercion machinery agree on this mapping. Adding
/// a new reference-like decoration is one edit.
pub(crate) fn decoration_wrapper(deco: TypDecoration) -> Option<&'static str> {
    match deco {
        TypDecoration::Ref => Some("Tactus.Ref"),
        TypDecoration::MutRef => Some("Tactus.MutRef"),
        TypDecoration::Box => Some("Tactus.Box"),
        TypDecoration::Rc => Some("Tactus.Rc"),
        TypDecoration::Arc => Some("Tactus.Arc"),
        TypDecoration::Ghost | TypDecoration::Tracked
        | TypDecoration::Never | TypDecoration::ConstPtr => None,
    }
}

/// Count the number of reference-decoration layers in a typ. Peels
/// `Boxed` transparently (Verus's poly encoding, not user-visible).
/// `TypX::MutRef` counts as one layer (new-mut-ref-mode's
/// non-Decorate shape).
///
/// Used by both `to_lean_expr::apply_ref_coercion_if_needed`
/// (wrapping with `.mk` for under-decorated rendered exprs) and
/// `apply_deref_chain` (unwrapping with `.deref` to reach inner T
/// for height-fn args and exec-fn body shadows).
pub(crate) fn count_ref_decorations(typ: &TypX) -> usize {
    let mut n = 0;
    let mut cur = typ;
    loop {
        match cur {
            TypX::Decorate(deco, _, inner) => {
                if decoration_wrapper(*deco).is_some() {
                    n += 1;
                }
                cur = &**inner;
            }
            TypX::Boxed(inner) => cur = &**inner,
            TypX::MutRef(_) => {
                n += 1;
                break;
            }
            _ => break,
        }
    }
    n
}

/// Apply N `.deref` field-projections to `base`, peeling N wrapper
/// layers to reach the inner value. Used wherever the rendered Lean
/// type has more `Tactus.X` wrappers than the call site expects:
///
/// * **Exec-fn body shadow**: a fn param `(s : Tactus.Ref Stack)`
///   needs `let s := s.deref` so body code sees `s : Stack`.
/// * **Height-fn recursive arg**: a field of type `Box<Stack>` has
///   binder type `Tactus.Box Stack`, but `Stack.height` expects
///   `Stack` — pass `<field_binder>.deref` instead of `<field_binder>`.
///
/// `n = 0` returns `base` unchanged.
pub(crate) fn apply_deref_chain(base: LExpr, n: usize) -> LExpr {
    let mut out = base;
    for _ in 0..n {
        out = LExpr::field_proj(out, "deref");
    }
    out
}

/// Collect the reference-decoration wrapper names from `typ`,
/// outermost-first. `Boxed` is transparent (Verus's poly encoding,
/// not user-visible); peeled silently. `MutRef` counts as one
/// (terminal — stops the walk).
///
/// Companion to [`count_ref_decorations`] — the count tells you "how
/// many", this tells you "which", in outermost-first order.
pub(crate) fn collect_ref_wraps(typ: &TypX) -> Vec<&'static str> {
    let mut out = Vec::new();
    let mut cur = typ;
    loop {
        match cur {
            TypX::Decorate(deco, _, inner) => {
                if let Some(w) = decoration_wrapper(*deco) {
                    out.push(w);
                }
                cur = &**inner;
            }
            TypX::Boxed(inner) => cur = &**inner,
            TypX::MutRef(_) => {
                out.push("Tactus.MutRef");
                break;
            }
            _ => break,
        }
    }
    out
}

/// Wrap `base` with N `.mk` constructors. `wraps[0]` is OUTERMOST
/// (last applied); `wraps[last]` is INNERMOST (first applied). So
/// `apply_wrap_chain(x, &["Tactus.Ref", "Tactus.Box"])` produces
/// `Tactus.Ref.mk (Tactus.Box.mk x)` — Box innermost, Ref outermost.
///
/// Dual of [`apply_deref_chain`]: deref peels wrappers off, wrap
/// puts them on. Both compose to identity when `wraps` matches the
/// peel order.
pub(crate) fn apply_wrap_chain(base: LExpr, wraps: &[&'static str]) -> LExpr {
    let mut out = base;
    for w in wraps.iter().rev() {
        out = LExpr::app1(LExpr::var_lit(&format!("{}.mk", w)), out);
    }
    out
}

/// Traits whose Lean `class` can't be emitted because some method decl
/// is absent from `fn_map` — i.e. stripped cross-crate (e.g.
/// `core::clone::Clone::clone`, dragged in by a `HashMap` bound). Both
/// `generate.rs` (class + instance emission gate) and `sst_to_lean.rs`
/// (broadcast-lemma bound filter) skip these so `trait_to_ast` never
/// panics on a missing method; the panic stays a tripwire for genuine
/// SAME-crate bugs. The whole-crate prune keeps every same-crate
/// function, so this only flags cross-crate-stripped traits. Single
/// source of truth for the "un-emittable trait" rule (#122).
/// Does this spec fn emit as a Lean AXIOM rather than a def? True
/// when it has no body (uninterp / external_body / cross-crate-
/// stripped) — OR when the body contains a `CallTarget::BuiltinSpecFun`
/// (`call_ensures` / `call_requires` over a function value), which the
/// renderer has no encoding for (it would emit the unresolvable
/// placeholder literal `builtinSpecFun` — vstd's `strictly_cloned`
/// poisoned every artifact whose dep set pulled it, found via
/// tactus-group-theory's apply_hom_symbol_exec). Dropping the body and
/// axiomatizing the SIGNATURE is sound — the constant becomes
/// uninterpreted, consumers elaborate, and reasoning that needed the
/// body's meaning simply isn't available (same trust shape as any
/// uninterp spec fn). Shared between `spec_fn_to_ast` (the emission
/// decision) and `nonempty::compute_nonempty_needs` Seed 2 (axioms
/// with param-mentioning ret typs need `[Nonempty]`).
pub(crate) fn spec_fn_emits_as_axiom(f: &vir::ast::FunctionX) -> bool {
    let Some(body) = &f.body else { return true };
    let mut found = false;
    crate::dep_order::walk_expr(body, &mut |e: &vir::ast::Expr| {
        if let vir::ast::ExprX::Call(vir::ast::CallTarget::BuiltinSpecFun(..), _, _) = &e.x {
            found = true;
        }
    });
    found
}

pub(crate) fn unemittable_traits(
    krate: &vir::ast::KrateX,
    fn_map: &std::collections::HashMap<&vir::ast::Fun, &vir::ast::FunctionX>,
) -> std::collections::HashSet<vir::ast::Path> {
    // Class/instance CONSISTENCY (2026-07-04): a class must be a
    // shell if ANY of its impls-to-be-emitted can't provide ALL its
    // method fields — else those instances elaborate as "Fields
    // missing" against the full class (vstd's Clone: extern
    // assume_specification impls for Vec/primitives have no bodied
    // TraitMethodImpl fns, while a user derive elsewhere in the
    // krate may be bodied — the MIXED case). Spec trait methods are
    // unaffected (impls provide spec bodies); user traits with real
    // Verus impl bodies stay full. Over-approximates across
    // krate.trait_impls (an impl that never emits still shells the
    // class) — safe, shells assert nothing.
    let impl_lacks_method = |tr: &vir::ast::TraitX| -> bool {
        krate.trait_impls.iter()
            .filter(|ti| ti.x.trait_path == tr.name)
            .any(|ti| {
                tr.methods.iter().any(|m| {
                    let decl_is_exec = fn_map.get(m)
                        .map(|d| matches!(d.mode, vir::ast::Mode::Exec))
                        .unwrap_or(false);
                    decl_is_exec
                        && !krate.functions.iter().any(|f| match &f.x.kind {
                            vir::ast::FunctionKind::TraitMethodImpl { method, impl_path, .. } =>
                                method == m
                                    && *impl_path == ti.x.impl_path
                                    && f.x.body.is_some(),
                            _ => false,
                        })
                })
            })
    };
    krate.traits.iter()
        .filter(|tr| {
            tr.x.methods.iter().any(|m| !fn_map.contains_key(m))
                || impl_lacks_method(&tr.x)
        })
        .map(|tr| tr.x.name.clone())
        .collect()
}

/// Bidirectional wrapper-kind-and-depth coercion. Bridge `value`
/// (currently at `from_typ`) to `to_typ` by inserting `.deref` chain
/// and/or `.mk` chain to match wrapper sequences.
///
/// Compares wrapper sequences (outermost-first) from both types:
///
/// * Sequences equal → no coercion.
/// * Sequences share a common inner suffix → peel only the
///   non-matching outer wraps of `from`, then wrap with the
///   non-matching outer wraps of `to`. Examples:
///   - `from=[Ref]`, `to=[]` → `value.deref` (depth shrink).
///   - `from=[]`, `to=[Ref]` → `Tactus.Ref.mk value` (depth grow).
///   - `from=[Box, Ref]`, `to=[Ref, Ref]` → `Tactus.Ref.mk value.deref`
///     (common suffix `[Ref]`; rewrap outer Box → Ref).
///   - `from=[MutRef]`, `to=[Ref]` → `Tactus.Ref.mk value.deref`
///     (kind mismatch at equal depth — peel one, wrap one).
///
/// This is the shared bidirectional helper that
/// `to_lean_expr::apply_ref_coercion_if_needed` and the SST-side
/// typed-composition machinery both delegate to. Centralising it
/// here means callers across the VIR-AST renderer, SST renderer,
/// substitution sites, and TypedExpr smart constructors all bridge
/// wrapper mismatches identically.
///
/// Coercion covers TWO dimensions (DESIGN-typed-renderer.md § D1):
///
/// * **Wrapper depth** — mismatched `Tactus.Ref`/`Box`/… chains bridge
///   via `.deref` (peel) / `.mk` (rewrap) chains.
/// * **Numeric render sort** — when both typs peel to integer ranges
///   whose Lean renderings differ (ℤ vs ℕ per
///   [`renders_as_lean_int`]), bridge via `Int.toNat`/`Int.ofNat`.
///   `Int.toNat` is faithful only for nonneg values — which the VIR
///   type system guarantees for any value flowing into a Nat-rendered
///   slot (and call-site bound hyps state explicitly; see
///   `push_ret_frames`).
///
/// Passthrough guarantee: when both dimensions already match, `value`
/// is returned byte-identical — migration to the unified bridge cannot
/// change output where today's output is right.
///
/// Beyond those two dimensions we don't model the inner type's
/// structure. If `from_typ` and `to_typ` have matching wrappers and
/// sorts but different inner types (e.g., `Box<MyS>` vs `Box<MyT>`),
/// this returns `value` unchanged — such mismatches at the inner
/// level are Lean's problem, not ours.
pub(crate) fn coerce_lexpr(value: LExpr, from_typ: &Typ, to_typ: &Typ) -> LExpr {
    let from_wraps = collect_ref_wraps(&**from_typ);
    let to_wraps = collect_ref_wraps(&**to_typ);
    // Numeric-sort reconciliation decision (int_range_of peels ALL
    // decorations, so this classifies the numeric core under any
    // wrappers).
    let sort_bridge: Option<(bool, bool)> =
        match (int_range_of(from_typ), int_range_of(to_typ)) {
            (Some(f), Some(t)) => {
                let (fi, ti) = (renders_as_lean_int(&f), renders_as_lean_int(&t));
                if fi != ti { Some((fi, ti)) } else { None }
            }
            _ => None,
        };
    if let Some((fi, ti)) = sort_bridge {
        // The numeric core needs an Int.toNat / Int.ofNat, which must
        // apply at the BARE value — full peel, bridge, full rewrap.
        // (The common case is no wrappers at all: spec-int values
        // flowing into nat/usize slots and vice versa.) The shared-
        // suffix optimization below can't apply a coercion under a
        // shared wrapper suffix, so it doesn't apply here.
        let peeled = apply_deref_chain(value, from_wraps.len());
        return apply_wrap_chain(apply_clip_coercion(fi, ti, peeled), &to_wraps);
    }
    if from_wraps == to_wraps {
        return value;
    }
    // Wrapper-only mismatch. Find longest common SUFFIX of the two
    // wrap sequences. The suffix corresponds to inner wraps that
    // already match — we leave those untouched. Only the non-matching
    // outer wraps need peel + rewrap.
    let suffix_len = from_wraps
        .iter()
        .rev()
        .zip(to_wraps.iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    let peel_n = from_wraps.len() - suffix_len;
    let wrap_slice = &to_wraps[..to_wraps.len() - suffix_len];
    let peeled = apply_deref_chain(value, peel_n);
    apply_wrap_chain(peeled, wrap_slice)
}

/// Lean accessor string for the `n`th element of an `arity`-tuple.
///
/// Lean 4 represents N-tuples as right-nested `Prod`:
/// `(a, b, c) : Int × Int × Int = Int × (Int × Int)`. The
/// auto-derived accessors are `.fst` (= `.1`) and `.snd` (= `.2`)
/// on each level — for an N-tuple, the j-th element (0-indexed)
/// requires `.2` (j times) followed by `.1`, except the last
/// element which is just `.2` repeated (arity-1) times. Examples:
///
/// | arity | n | result   | meaning                  |
/// |-------|---|----------|--------------------------|
/// | 2     | 0 | `1`      | `.1` (first of pair)     |
/// | 2     | 1 | `2`      | `.2` (second of pair)    |
/// | 3     | 0 | `1`      | first element            |
/// | 3     | 1 | `2.1`    | inner pair's first       |
/// | 3     | 2 | `2.2`    | inner pair's second      |
/// | 4     | 0 | `1`      |                          |
/// | 4     | 1 | `2.1`    |                          |
/// | 4     | 2 | `2.2.1`  |                          |
/// | 4     | 3 | `2.2.2`  |                          |
///
/// The result is intended to be appended to a base via
/// `<base>.<result>` — Lean parses `e.2.1` as `((e).2).1`, which
/// matches the desired projection.
///
/// Requires `arity >= 2`. Verus doesn't produce 0-tuples (unit type
/// lowers to no field access) or 1-tuples (degenerate case with
/// other lowerings); the assert guards against shape drift if a
/// future Verus rebase changes that.
pub(crate) fn tuple_field_accessor(arity: usize, n: usize) -> String {
    // Only genuinely-impossible shapes reach here: `field_access_name`
    // handles the 1-tuple identity case (field 0 of `(x,)`) upstream, and a
    // 0-tuple (unit) has no fields. So arity < 2 here means a 0-tuple field
    // access or a 1-tuple field n>0 — both shape drift. The prior fallback
    // `(n + 1).to_string()` would emit a probably-wrong accessor; surface it.
    assert!(
        arity >= 2,
        "tuple_field_accessor: arity {} < 2 — unit (0-tuple) has no fields and \
         a 1-tuple's field 0 is the identity (handled in field_access_name). \
         n={n}. If this fires, please open an issue (probable Verus rebase \
         shape drift).",
        arity,
    );
    if n + 1 >= arity {
        // Last position: `.2` repeated (arity - 1) times.
        // Arity-2 i=1 → "2"; arity-3 i=2 → "2.2"; etc.
        std::iter::repeat("2")
            .take(arity - 1)
            .collect::<Vec<_>>()
            .join(".")
    } else {
        // Non-last position: `.2` repeated n times, then `.1`.
        // Arity-3 i=0 → "1"; arity-3 i=1 → "2.1"; arity-4 i=2 → "2.2.1".
        let twos: Vec<&str> = std::iter::repeat("2").take(n).collect();
        if twos.is_empty() {
            "1".to_string()
        } else {
            format!("{}.1", twos.join("."))
        }
    }
}

/// Map a VIR field access to the Lean side's field name.
///
/// * Anonymous tuple (`Dt::Tuple`) uses 0-indexed numeric fields like
///   `"0"` / `"1"`; Lean's `Prod`-derived accessor is 1-indexed
///   (`.1`, `.2`), so `"0"` → `"1"`, `"1"` → `"2"`, etc.
/// * Single-variant struct (`Dt::Path` where the variant name equals
///   the type's short name) uses the structure-auto-derived accessor
///   names: numeric `"0"` → `"val0"`, named fields pass through
///   (after sanitization). Lean's `structure` auto-derives these.
/// * Multi-variant enum (`Dt::Path` where the variant name differs
///   from the type's short name) routes through the per-variant
///   accessor fns emitted by `datatype_to_cmds` — numeric field
///   becomes `"<Variant>_val<n>"`, named field becomes
///   `"<Variant>_<field>"`. Lean's `inductive` doesn't auto-derive
///   field accessors, so we synthesise `def Kind.Foo_val0 : Kind → …`
///   alongside the inductive declaration.
///
/// Shared between the VIR-AST and SST renderers so the naming rule
/// lives in one place. Divergence would make match-arm desugaring
/// (exec path) reference a field name that the accessor-fn emission
/// (preamble path) doesn't define — silent Lean "invalid field"
/// failure.
///
/// Returns `None` when the projection is the **identity** — field 0 of a
/// 1-tuple `(x,)`. Lean has no 1-tuple type (`(x)` ≡ `x`, `(T,)` ≡ `T`), so
/// the type renderer already flattens `Dt::Tuple(1)` to its element
/// (`to_lean_type::typ_to_expr`); the projection is therefore identity, and
/// callers render the base alone (see `field_proj_opr`). Verus produces
/// 1-tuples for the single-arg closure ABI (`Fn((a,))`) — e.g. the clone-spec
/// helpers in `vstd::pervasive` — so this is reachable, not shape drift.
pub(crate) fn field_access_name(field_opr: &FieldOpr) -> Option<String> {
    let raw = field_opr.field.as_str();
    let numeric = raw.parse::<usize>().ok();
    match (&field_opr.datatype, numeric) {
        // 1-tuple field 0 → identity (Lean flattens `(x,)` to `x`).
        (Dt::Tuple(1), Some(0)) => return None,
        (Dt::Tuple(arity), Some(n)) => return Some(tuple_field_accessor(*arity, n)),
        (Dt::Path(path), _) => {
            let type_short = short_name(path);
            let variant = field_opr.variant.as_str();
            let is_single_variant = variant == type_short;
            let field_seg = match numeric {
                Some(n) => format!("val{}", n),
                None => sanitize(raw),
            };
            Some(if is_single_variant {
                field_seg
            } else {
                format!("{}_{}", sanitize(variant), field_seg)
            })
        }
        // Tuple with non-numeric field name — Verus shouldn't produce
        // this (tuple fields are positional, named "0", "1", ...). If
        // it ever does, the previous defensive fallback (`sanitize(raw)`)
        // would silently produce a wrong field name. Surface it as a
        // shape-drift signal instead.
        (Dt::Tuple(_), None) => unreachable!(
            "field_access_name: tuple with non-numeric field `{}` — Verus's mode \
             check should reject this upstream. If this fires, please open an \
             issue (probable Verus rebase shape drift).",
            raw,
        ),
    }
}

/// Project `field_opr` from an already-rendered `base`, collapsing the
/// identity case (field 0 of a 1-tuple) to `base` itself. Use at any site
/// that turns a field access into `base.<accessor>` so the 1-tuple
/// flattening (Lean has no 1-tuple type) is applied uniformly — mirrors what
/// the type/ctor renderers already do. See `field_access_name`.
pub(crate) fn field_proj_opr(base: LExpr, field_opr: &FieldOpr) -> LExpr {
    match field_access_name(field_opr) {
        Some(accessor) => LExpr::field_proj(base, accessor),
        None => base,
    }
}

/// Assemble the Lean value of a Verus `choose` — the VIR (`ExprX::Choose`)
/// and SST (`BndX::Choose`) renderers both route here so the two paths
/// can't drift (DESIGN-lean-all-proofs-bugs.md B2).
///
/// Semantics (mirrors AIR `BindX::Choose`, `vir/src/sst_to_air.rs`): the
/// value of `body` at SOME binding of `binders` satisfying `cond`;
/// arbitrary when no witness exists — `Classical.epsilon` is total, the
/// Lean analog of AIR's `as_type` coercion on an unsatisfiable choose.
///
/// * `body: None` — the dominant `choose|x| P(x)` form (single binder,
///   body IS the bound var): `Classical.epsilon (fun x => cond)`.
/// * `body: Some(b)` — general form (multi-binder and/or compound body);
///   skolemize binder-by-binder, then evaluate the body:
///   `let x₁ := Classical.epsilon (fun x₁ => ∃ x₂ … xₙ, cond);
///    …
///    let xₙ := Classical.epsilon (fun xₙ => cond);
///    b`
///   Each εᵢ references the previously-chosen x₁…xᵢ₋₁ through the
///   enclosing lets — ordinary ∃-witness extraction. The let names are
///   the binder names, so `cond`/`b` rendered with the standard binder
///   naming reference them directly.
///
/// (The previous SST rendering, `epsilon (fun x => cond ∧ body)`,
/// conjoined a non-Prop body — ill-typed for every `choose` whose body
/// isn't a Prop: 2,596 errors / 440 fns on tactus-group-theory. The VIR
/// rendering ignored `body` entirely — correct only for the `body: None`
/// form here.)
///
/// `l_binders` and `names` run in parallel (same order); callers derive
/// both from the same VarBinders.
pub(crate) fn choose_node(
    l_binders: &[crate::lean_ast::Binder],
    names: &[LeanName],
    cond: LExpr,
    body: Option<LExpr>,
) -> ExprNode {
    let Some(body) = body else {
        debug_assert!(l_binders.len() == 1, "body: None is the single-binder form");
        return LExpr::app1(
            LExpr::var_lit("Classical.epsilon"),
            LExpr::lambda(l_binders.to_vec(), cond),
        )
        .node;
    };
    skolem_lets(l_binders, names, &cond, body).node
}

/// The ε-skolemization let-chain shared by `choose_node` and
/// `choose_witness_hyp`:
/// `let x₁ := ε(fun x₁ => ∃ x₂ … xₙ, cond); … let xₙ := ε(fun xₙ => cond);
///  inner`.
fn skolem_lets(
    l_binders: &[crate::lean_ast::Binder],
    names: &[LeanName],
    cond: &LExpr,
    inner: LExpr,
) -> LExpr {
    let mut out = inner;
    for i in (0..l_binders.len()).rev() {
        let eps_cond = if i + 1 < l_binders.len() {
            LExpr::exists_(l_binders[i + 1..].to_vec(), cond.clone())
        } else {
            cond.clone()
        };
        let eps = LExpr::app1(
            LExpr::var_lit("Classical.epsilon"),
            LExpr::lambda(vec![l_binders[i].clone()], eps_cond),
        );
        out = LExpr::let_bind(names[i].clone(), eps, out);
    }
    out
}

/// The witness fact a `choose` carries (DESIGN-lean-all-proofs-bugs.md B2):
/// `(∃ bs, cond) → (let x₁ := ε₁; …; let xₙ := εₙ; cond)`.
///
/// This is `Classical.epsilon_spec` instantiated at the exact ε-terms
/// `choose_node` renders (single binder: `(∃ x, cond) → cond[ε/x]` up to
/// zeta-reduction), so assuming it as an obligation hypothesis adds no
/// axiomatic strength — it mirrors the conditional witness axiom Verus's
/// Z3 path gets from AIR's `BindX::Choose` skolemization. The ∃'s binders
/// scope over the antecedent only; the lets rebuild the same skolem terms
/// in the consequent, closed.
pub(crate) fn choose_witness_hyp(
    l_binders: &[crate::lean_ast::Binder],
    names: &[LeanName],
    cond: &LExpr,
) -> LExpr {
    LExpr::implies(
        LExpr::exists_(l_binders.to_vec(), cond.clone()),
        skolem_lets(l_binders, names, cond, cond.clone()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use vir::ast::VariantCheck;

    fn opr(dt: Dt, field: &str) -> FieldOpr {
        FieldOpr {
            datatype: dt,
            variant: Arc::new("tuple%1".to_string()),
            field: Arc::new(field.to_string()),
            get_variant: false,
            check: VariantCheck::None,
        }
    }

    #[test]
    fn one_tuple_field0_is_identity() {
        // Lean has no 1-tuple type (`(x,)` ≡ `x`), so field-0 of a 1-tuple is
        // identity — `field_access_name` returns None and `field_proj_opr`
        // collapses to the base. Verus produces 1-tuples for the single-arg
        // closure ABI (BUG-vec-copy-datatype-index-lean-panic.md).
        assert_eq!(field_access_name(&opr(Dt::Tuple(1), "0")), None);
        let base = LExpr::var(crate::lean_name::LeanName::synthetic("t".to_string()));
        let projected = field_proj_opr(base, &opr(Dt::Tuple(1), "0"));
        assert!(
            matches!(projected.node, ExprNode::Var(_)),
            "1-tuple field-0 must collapse to the base, got {:?}", projected.node,
        );
    }

    #[test]
    fn two_tuple_still_projects() {
        // Regression guard: arity-2 is unaffected (Prod accessors `.1` / `.2`).
        assert_eq!(field_access_name(&opr(Dt::Tuple(2), "0")), Some("1".to_string()));
        assert_eq!(field_access_name(&opr(Dt::Tuple(2), "1")), Some("2".to_string()));
    }

    // ── coerce_lexpr numeric-sort reconciliation (P0, D1) ───────────

    fn t_int() -> Typ {
        Arc::new(TypX::Int(IntRange::Int))
    }
    fn t_usize() -> Typ {
        Arc::new(TypX::Int(IntRange::USize))
    }
    fn t_nat() -> Typ {
        Arc::new(TypX::Int(IntRange::Nat))
    }
    fn t_u32() -> Typ {
        Arc::new(TypX::Int(IntRange::U(32)))
    }
    fn t_bool() -> Typ {
        Arc::new(TypX::Bool)
    }
    fn t_ref(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(TypDecoration::Ref, None, inner))
    }
    fn v() -> LExpr {
        LExpr::var(crate::lean_name::LeanName::synthetic("v".to_string()))
    }
    fn rendered(e: LExpr) -> String {
        format!("{:?}", e.node)
    }

    #[test]
    fn sort_bridge_int_to_nat_side() {
        // ℤ value into a ℕ-rendered slot (usize / nat) → Int.toNat.
        // The Exhibit B shape (DESIGN-typed-renderer.md).
        for dst in [t_usize(), t_nat()] {
            let out = coerce_lexpr(v(), &t_int(), &dst);
            assert!(
                rendered(out).contains("Int.toNat"),
                "int → {dst:?} must insert Int.toNat",
            );
        }
    }

    #[test]
    fn sort_bridge_nat_side_to_int() {
        // ℕ-rendered value into an ℤ slot → Int.ofNat.
        let out = coerce_lexpr(v(), &t_usize(), &t_int());
        assert!(rendered(out).contains("Int.ofNat"));
    }

    #[test]
    fn sort_passthrough_same_side() {
        // Passthrough guarantee: same render sort in both dimensions →
        // byte-identical value. u32 renders Int, so u32↔int is
        // sort-transparent; usize↔nat both render Nat.
        for (from, to) in [
            (t_int(), t_int()),
            (t_u32(), t_int()),
            (t_int(), t_u32()),
            (t_usize(), t_nat()),
            (t_usize(), t_usize()),
            (t_bool(), t_bool()),
        ] {
            let out = coerce_lexpr(v(), &from, &to);
            assert!(
                matches!(out.node, ExprNode::Var(_)),
                "{from:?} → {to:?} must be passthrough, got {:?}", out.node,
            );
        }
    }

    #[test]
    fn sort_bridge_composes_with_wrapper_peel() {
        // `&int` value into a bare usize slot: peel the Ref wrapper,
        // THEN Int.toNat at the numeric core.
        let out = coerce_lexpr(v(), &t_ref(t_int()), &t_usize());
        let s = rendered(out);
        assert!(s.contains("Int.toNat") && s.contains("deref"), "got {s}");
    }

    #[test]
    fn sort_bridge_composes_with_rewrap() {
        // Bare ℤ value into a `&usize` slot: Int.toNat, then rewrap.
        let out = coerce_lexpr(v(), &t_int(), &t_ref(t_usize()));
        let s = rendered(out);
        assert!(s.contains("Int.toNat") && s.contains(".mk"), "got {s}");
    }

    #[test]
    fn wrapper_only_path_unchanged() {
        // Sorts match → the wrapper-only suffix-optimized path is
        // untouched (deref, no clip head).
        let out = coerce_lexpr(v(), &t_ref(t_int()), &t_int());
        let s = rendered(out);
        assert!(s.contains("deref") && !s.contains("toNat") && !s.contains("ofNat"));
    }

    #[test]
    fn sort_bridge_under_equal_wraps() {
        // EQUAL, NONEMPTY wrap chains with differing inner sorts
        // (`&int` value into a `&usize` slot): the shared-suffix
        // optimization can't apply a coercion under a shared wrapper,
        // so the bridge must full-peel, sort-coerce at the bare core,
        // and rewrap (2026-07-03 self-review: this path was
        // implemented in P0 but unpinned).
        let out = coerce_lexpr(v(), &t_ref(t_int()), &t_ref(t_usize()));
        let s = rendered(out);
        assert!(
            s.contains("deref") && s.contains("Int.toNat") && s.contains(".mk"),
            "expected peel + toNat + rewrap, got {s}",
        );
    }
}

#[cfg(test)]
mod choose_tests {
    use super::*;

    fn bind(name: &str) -> crate::lean_ast::Binder {
        crate::lean_ast::Binder::explicit(
            crate::lean_name::LeanName::synthetic(name.to_string()),
            LExpr::var_lit("Int"),
        )
    }
    fn nm(name: &str) -> LeanName {
        crate::lean_name::LeanName::synthetic(name.to_string())
    }
    fn cond() -> LExpr {
        // stand-in for `P x` — an application, definitely a Prop shape
        LExpr::app1(LExpr::var_lit("P"), LExpr::var_lit("x"))
    }

    #[test]
    fn choose_single_var_body_is_bare_epsilon() {
        // `choose|x| P(x)` (body IS the bound var → passed as None):
        // `Classical.epsilon (fun x => cond)`. The pre-B2 rendering
        // conjoined the (Int-typed!) body onto the condition —
        // `epsilon (fun x => cond ∧ x)` — ill-typed for every choose
        // whose body isn't a Prop (2,596 errors on tactus-group-theory).
        let out = LExpr::new(choose_node(&[bind("x")], &[nm("x")], cond(), None));
        let s = format!("{:?}", out.node);
        assert!(s.contains("Classical.epsilon"), "epsilon head: {s}");
        assert!(!s.contains("And"), "no body conjunction: {s}");
    }

    #[test]
    fn choose_multi_binder_skolemizes() {
        // `choose|a, b| P` with compound body: nested epsilons via
        // `let a := ε(fun a => ∃ b, cond); let b := ε(fun b => cond); body`.
        let out = LExpr::new(choose_node(
            &[bind("a"), bind("b")],
            &[nm("a"), nm("b")],
            cond(),
            Some(LExpr::var_lit("body")),
        ));
        let s = format!("{:?}", out.node);
        assert_eq!(s.matches("Classical.epsilon").count(), 2, "one ε per binder: {s}");
        assert!(s.contains("Exists"), "inner ∃ for later binders: {s}");
        assert!(s.contains("Let"), "skolem lets: {s}");
    }

    #[test]
    fn choose_witness_hyp_shape() {
        // `(∃ x, cond) → (let x := ε(fun x => cond); cond)` — B2b's
        // hypothesis; Classical.epsilon_spec at the value's exact ε-term.
        let out = choose_witness_hyp(&[bind("x")], &[nm("x")], &cond());
        let s = format!("{:?}", out.node);
        assert!(s.contains("Exists"), "antecedent ∃: {s}");
        assert!(s.contains("Classical.epsilon"), "ε in consequent: {s}");
        assert!(s.contains("Implies") || s.contains("Imp"), "implication: {s}");
    }
}
