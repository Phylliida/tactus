//! Typed wrapper around `lean_ast::Expr` for composition-time coercion.
//!
//! ## What and why
//!
//! `lean_ast::Expr` is untyped — it's just a syntax tree. When we compose
//! two expressions (apply, field-project, substitute, ...) and the value
//! has different wrapper depth than the slot expects, we have to insert
//! a `.deref` chain or a `.mk` chain to bridge. Today this is done ad
//! hoc at each composition site, which has been the source of recurring
//! wrapper-arch typing bugs (β refactor, U2, three SST clusters in 2026-05).
//!
//! `TypedExpr` carries the Lean-level Typ alongside the Expr. Smart
//! constructors that compose typed values automatically coerce inputs
//! to the slot typ via [`expr_shared::coerce_lexpr`]. The bridge happens
//! at composition time, not at later use sites.
//!
//! ## Scope
//!
//! Phase 1 (the scaffolding): TypedExpr type + a minimal set of smart
//! constructors covering the cases the SST renderer's typing-sensitive
//! sites need. Raw `Expr` stays public — TypedExpr is opt-in. Migration
//! happens at the sites where wrapper-depth typing matters (SST call
//! args, projection sites, post-call existentials).
//!
//! Phase 2 (the migration): convert the three SST clusters (mut-ref +
//! trait dispatch, wrapper-arch probes, new-mut-ref edges) to use
//! TypedExpr at their typing-sensitive sites.
//!
//! ## What this is not
//!
//! Not a full elaborator. We don't model polymorphism with metavariable
//! unification, typeclass dispatch, or dependent typing. The typing
//! rules cover only wrapper-depth bridging — the dimension we have
//! actual bugs in. Inner types (Int, struct fields, etc.) are opaque
//! pass-through.
//!
//! Not type-enforced. `TypedExpr::new(expr, typ)` trusts the caller's
//! claim that `expr`'s actual Lean type matches `typ`. Same risk as
//! today's untyped Expr: a site that lies about typ produces wrong
//! coercion. The difference is that TypedExpr concentrates the typing
//! claim at construction sites (which are fewer and reviewable) rather
//! than scattering it across every composition.
//!
//! See DESIGN.md § "TypedExpr-with-smart-ctor" for the full design
//! analysis and the rejected alternatives (full elaborator, phantom
//! typing, Lean `Coe` delegation).

use vir::ast::Typ;

use crate::expr_shared::coerce_lexpr;
use crate::lean_ast::Expr;
use crate::lean_name::LeanName;

/// An [`Expr`] together with its declared Lean-level [`Typ`]. The typ
/// is metadata used by composition methods to decide coercion; it's
/// not enforced by the type system (we don't have Lean's elaborator
/// in Rust). The discipline is at construction sites — every
/// `TypedExpr::var` / `from_untyped` / etc. site must provide a
/// correct typ.
///
/// `inner` is the untyped Lean expression. After composition through
/// smart constructors, it may have `.deref` / `.mk` coercions inserted
/// to bridge wrapper-depth mismatches.
#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub inner: Expr,
    pub typ: Typ,
    /// Does `typ` come from a TRUSTED source — one that describes the
    /// rendered Lean value definitionally (a binder's declared typ, a
    /// render-time substitution bridged by construction, a declared
    /// callee ret typ, a definitional coercion) — rather than from
    /// the node's CLAIMED SST typ, which VIR's poly-boxing can shift
    /// by a ref-decoration?
    ///
    /// Computed per-arm in `exp_to_typed` alongside the render — the
    /// single source of truth (2026-07-26, decision #6-2; replaces
    /// the separate `actual_is_trusted` walk that had to hand-mirror
    /// `exp_to_typed`'s arm structure). Consumers: the Box/Unbox arm
    /// (propagate the child's actual only when trusted) and the
    /// walker's let-binder env (P2 trust bit).
    pub trusted: bool,
}

impl TypedExpr {
    // ── Construction ────────────────────────────────────────────────

    /// Wrap a raw [`Expr`] with a stated typ. Caller asserts that
    /// `inner`'s actual Lean-level type is `typ`. Use when adapting
    /// pre-rendered Expr values (e.g., from `vir_expr_to_ast`) into
    /// the typed composition pipeline. Untrusted by default — chain
    /// [`with_trust`] where the typ source is definitional.
    pub fn from_untyped(inner: Expr, typ: Typ) -> Self {
        Self { inner, typ, trusted: false }
    }

    /// Typed variable reference. `typ` is the binder's declared typ
    /// in the current scope (post-shadow if the binder was shadowed).
    /// Untrusted by default — chain [`with_trust`].
    pub fn var(name: LeanName, typ: Typ) -> Self {
        Self {
            inner: Expr::var(name),
            typ,
            trusted: false,
        }
    }

    /// Set the trust bit (builder-style). See the field doc.
    pub fn with_trust(mut self, trusted: bool) -> Self {
        self.trusted = trusted;
        self
    }

    // ── Coercion / unwrapping ───────────────────────────────────────

    /// Coerce to `target_typ` and unwrap to raw [`Expr`]. The most
    /// common terminal operation — use when composing into a slot
    /// (call arg, field projection base, etc.) where the surrounding
    /// LExpr expects the target typ.
    ///
    /// If `self.typ` and `target_typ` have matching wrapper depth,
    /// returns the raw Expr unchanged. Otherwise inserts `.deref`
    /// chain (depth >) or `.mk` chain (depth <).
    pub fn into_slot(self, target_typ: &Typ) -> Expr {
        coerce_lexpr(self.inner, &self.typ, target_typ)
    }

    /// Coerce to `target_typ` and return the result as a new
    /// `TypedExpr`. Use when the coerced value is itself composed
    /// further (e.g., as the head of an App).
    pub fn coerce_to(self, target_typ: &Typ) -> Self {
        let coerced = coerce_lexpr(self.inner, &self.typ, target_typ);
        Self {
            inner: coerced,
            typ: target_typ.clone(),
            // The coercion makes the value inhabit `target_typ`
            // definitionally (deref/mk chains are type-directed) —
            // the result's typ describes the rendered value by
            // construction (the Clip arm relies on this).
            trusted: true,
        }
    }

    /// Drop the typing wrapper, return raw [`Expr`] WITHOUT any
    /// coercion. Use when the value is being placed in a typing-
    /// irrelevant slot (e.g., a Prop conjunction, an untyped
    /// theorem goal). Coercion at typing-relevant slots should go
    /// through [`into_slot`] instead.
    pub fn into_untyped(self) -> Expr {
        self.inner
    }

    // ── Inspection ──────────────────────────────────────────────────

    /// Read the typ. Useful for callers that need to inspect typ
    /// without consuming the TypedExpr (e.g., for branching logic
    /// based on wrapper depth).
    pub fn typ(&self) -> &Typ {
        &self.typ
    }

    // ── Composition (smart constructors) ────────────────────────────

    /// Field projection. Auto-derefs the base to inner-typed before
    /// projecting (the field belongs to the inner type, not the
    /// wrapper). `field_name` is the Lean-side field accessor (e.g.,
    /// `"val0"` for tuple-style or `"x"` for named struct field).
    /// `inner_typ` is the type after peeling all wrapper decorations
    /// (used for the deref count). `field_typ` is the projection's
    /// result typ.
    ///
    /// We require `inner_typ` and `field_typ` explicitly rather than
    /// deriving from a datatype environment because TypedExpr doesn't
    /// model the datatype env — caller knows the field info from the
    /// VIR/SST Field opr.
    pub fn field(
        self,
        field_name: impl Into<String>,
        inner_typ: &Typ,
        field_typ: Typ,
    ) -> Self {
        // Deref to inner first, then project.
        let derefed = coerce_lexpr(self.inner, &self.typ, inner_typ);
        Self {
            inner: Expr::field_proj(derefed, field_name),
            typ: field_typ,
            // Caller-claimed projection typ — not definitional.
            trusted: false,
        }
    }

    /// Apply `self` as a function to `args`. Each arg is coerced to
    /// its corresponding param typ via [`into_slot`]. `param_typs`
    /// and `ret_typ` are caller-provided (TypedExpr doesn't derive
    /// from arrow shapes — we'd need full type inference for that;
    /// caller knows from the callee's `FunctionX`).
    ///
    /// `param_typs.len()` must equal `args.len()`; mismatch is a
    /// caller bug (codegen produced wrong-arity application).
    pub fn apply(self, args: Vec<TypedExpr>, param_typs: &[Typ], ret_typ: Typ) -> Self {
        assert_eq!(
            args.len(),
            param_typs.len(),
            "TypedExpr::apply: arg count {} != param count {} — caller bug",
            args.len(),
            param_typs.len(),
        );
        let coerced_args: Vec<Expr> = args
            .into_iter()
            .zip(param_typs.iter())
            .map(|(a, p)| a.into_slot(p))
            .collect();
        Self {
            inner: Expr::app(self.inner, coerced_args),
            typ: ret_typ,
            // The declared ret typ describes the rendered application
            // by construction (same rule as the plain-call arm).
            trusted: true,
        }
    }
}

#[cfg(test)]
#[path = "tests/typed_expr.rs"]
mod tests;
