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
}

impl TypedExpr {
    // ── Construction ────────────────────────────────────────────────

    /// Wrap a raw [`Expr`] with a stated typ. Caller asserts that
    /// `inner`'s actual Lean-level type is `typ`. Use when adapting
    /// pre-rendered Expr values (e.g., from `vir_expr_to_ast`) into
    /// the typed composition pipeline.
    pub fn from_untyped(inner: Expr, typ: Typ) -> Self {
        Self { inner, typ }
    }

    /// Typed variable reference. `typ` is the binder's declared typ
    /// in the current scope (post-shadow if the binder was shadowed).
    pub fn var(name: LeanName, typ: Typ) -> Self {
        Self {
            inner: Expr::var(name),
            typ,
        }
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_ast::ExprNode;
    use std::sync::Arc;
    use vir::ast::{Typ, TypDecoration, TypX};

    fn int_typ() -> Typ {
        Arc::new(TypX::Int(vir::ast::IntRange::Int))
    }

    fn ref_typ(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(
            TypDecoration::Ref,
            None,
            inner,
        ))
    }

    fn box_typ(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(
            TypDecoration::Box,
            None,
            inner,
        ))
    }

    fn mut_ref_typ(inner: Typ) -> Typ {
        Arc::new(TypX::MutRef(inner))
    }

    fn rc_typ(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(TypDecoration::Rc, None, inner))
    }

    fn arc_typ(inner: Typ) -> Typ {
        Arc::new(TypX::Decorate(TypDecoration::Arc, None, inner))
    }

    /// Did `expr` end up as `base.deref` (one deref chain)?
    fn is_single_deref(expr: &Expr) -> bool {
        matches!(&expr.node, ExprNode::FieldProj { field, .. } if field == "deref")
    }

    /// Count consecutive `.deref` projections wrapping `expr`. Returns
    /// the count and the base (the inner-most non-deref expression).
    fn count_derefs(expr: &Expr) -> (usize, &Expr) {
        let mut n = 0;
        let mut cur = expr;
        while let ExprNode::FieldProj { expr: inner, field } = &cur.node {
            if field != "deref" {
                break;
            }
            n += 1;
            cur = inner;
        }
        (n, cur)
    }

    /// Peel `<Wrapper>.mk` apps off `expr` from the outside in. Returns
    /// the wrapper names (outermost-first) and the inner-most argument.
    /// E.g. `Ref.mk (Box.mk x)` → (["Tactus.Ref", "Tactus.Box"], x).
    fn collect_mk_wraps(expr: &Expr) -> (Vec<String>, &Expr) {
        let mut wraps = Vec::new();
        let mut cur = expr;
        loop {
            let ExprNode::App { head, args } = &cur.node else { break };
            let ExprNode::Var(name) = &head.node else { break };
            let name_str = name.as_str();
            if !name_str.ends_with(".mk") || args.len() != 1 {
                break;
            }
            let wrapper = name_str.trim_end_matches(".mk").to_string();
            wraps.push(wrapper);
            cur = &args[0];
        }
        (wraps, cur)
    }

    /// Did `expr` end up as `Wrapper.mk arg` (one wrap)?
    fn is_single_wrap(expr: &Expr, wrapper: &str) -> bool {
        if let ExprNode::App { head, args } = &expr.node {
            if let ExprNode::Var(name) = &head.node {
                let mk_name = format!("{}.mk", wrapper);
                return name.as_str() == mk_name && args.len() == 1;
            }
        }
        false
    }

    #[test]
    fn from_untyped_preserves_expr() {
        let raw = Expr::lit_int("42");
        let typed = TypedExpr::from_untyped(raw.clone(), int_typ());
        let unwrapped = typed.into_untyped();
        // Both should be the same shape.
        assert!(matches!(&unwrapped.node, ExprNode::Lit(s) if s == "42"));
    }

    #[test]
    fn into_slot_no_coercion_when_typs_match() {
        let typed = TypedExpr::var(LeanName::synthetic("x"), int_typ());
        let result = typed.into_slot(&int_typ());
        // No deref, no wrap.
        assert!(matches!(&result.node, ExprNode::Var(_)));
    }

    #[test]
    fn into_slot_inserts_deref_when_value_is_wrapper_typed() {
        // value: Tactus.Ref Int; slot: Int → expect .deref
        let typed = TypedExpr::var(LeanName::synthetic("r"), ref_typ(int_typ()));
        let result = typed.into_slot(&int_typ());
        assert!(is_single_deref(&result));
    }

    #[test]
    fn into_slot_inserts_wrap_when_slot_is_wrapper_typed() {
        // value: Int; slot: Tactus.Ref Int → expect Tactus.Ref.mk
        let typed = TypedExpr::var(LeanName::synthetic("x"), int_typ());
        let result = typed.into_slot(&ref_typ(int_typ()));
        assert!(is_single_wrap(&result, "Tactus.Ref"));
    }

    #[test]
    fn into_slot_handles_two_layer_deref() {
        // value: Tactus.Ref (Tactus.Box Int); slot: Int → expect .deref.deref
        let typed = TypedExpr::var(
            LeanName::synthetic("r"),
            ref_typ(box_typ(int_typ())),
        );
        let result = typed.into_slot(&int_typ());
        // Two field projs, both named "deref".
        let ExprNode::FieldProj { expr: outer_base, field: outer_field } = &result.node else {
            panic!("expected outer FieldProj, got {:?}", result.node);
        };
        assert_eq!(outer_field, "deref");
        let ExprNode::FieldProj { field: inner_field, .. } = &outer_base.node else {
            panic!("expected inner FieldProj, got {:?}", outer_base.node);
        };
        assert_eq!(inner_field, "deref");
    }

    #[test]
    fn coerce_to_returns_typed_with_target() {
        let typed = TypedExpr::var(LeanName::synthetic("r"), ref_typ(int_typ()));
        let coerced = typed.coerce_to(&int_typ());
        // typ is now Int (the target).
        assert!(matches!(&*coerced.typ, TypX::Int(_)));
        // inner has the .deref.
        assert!(is_single_deref(&coerced.inner));
    }

    #[test]
    fn into_untyped_drops_typ_no_coercion() {
        // Even with wrapper mismatch, into_untyped doesn't coerce.
        let typed = TypedExpr::var(LeanName::synthetic("r"), ref_typ(int_typ()));
        let result = typed.into_untyped();
        assert!(matches!(&result.node, ExprNode::Var(_)));
    }

    #[test]
    fn field_projection_auto_derefs_base() {
        // base : Tactus.Box Holder; project .val0 with inner_typ Holder
        let holder_path = vir::ast::PathX {
            krate: None,
            segments: Arc::new(vec![Arc::new("Holder".to_string())]),
        };
        let holder_typ = Arc::new(TypX::Datatype(
            vir::ast::Dt::Path(Arc::new(holder_path)),
            Arc::new(vec![]),
            Arc::new(vec![]),
        ));
        let base = TypedExpr::var(LeanName::synthetic("h"), box_typ(holder_typ.clone()));
        let projected = base.field("val0", &holder_typ, int_typ());
        // Should be: h.deref.val0
        let ExprNode::FieldProj { expr: inner_base, field: outer_field } = &projected.inner.node else {
            panic!("expected outer FieldProj");
        };
        assert_eq!(outer_field, "val0");
        assert!(is_single_deref(inner_base), "expected base to be `h.deref`");
        // Resulting typ is the field typ.
        assert!(matches!(&*projected.typ, TypX::Int(_)));
    }

    #[test]
    fn apply_coerces_args_to_param_typs() {
        // head : Int → Int → Int (we don't care about head typ here;
        // we just want to test arg coercion)
        // arg1 : Tactus.Ref Int, param1 : Int → expect .deref
        // arg2 : Int, param2 : Tactus.Ref Int → expect .mk
        let head = TypedExpr::var(LeanName::synthetic("f"), int_typ()); // typ wrong but irrelevant
        let arg1 = TypedExpr::var(LeanName::synthetic("a"), ref_typ(int_typ()));
        let arg2 = TypedExpr::var(LeanName::synthetic("b"), int_typ());
        let result = head.apply(
            vec![arg1, arg2],
            &[int_typ(), ref_typ(int_typ())],
            int_typ(),
        );
        let ExprNode::App { args, .. } = &result.inner.node else {
            panic!("expected App");
        };
        assert_eq!(args.len(), 2);
        assert!(is_single_deref(&args[0]), "arg1 should be derefed");
        assert!(is_single_wrap(&args[1], "Tactus.Ref"), "arg2 should be wrapped");
    }

    #[test]
    fn into_slot_handles_kind_mismatch_at_equal_depth() {
        // value : Tactus.MutRef Holder; slot : Tactus.Ref Holder.
        // Equal depth (1), different kinds. Expect peel + wrap:
        // `Tactus.Ref.mk value.deref`.
        let typed = TypedExpr::var(LeanName::synthetic("m"), mut_ref_typ(int_typ()));
        let result = typed.into_slot(&ref_typ(int_typ()));
        // Outer is Tactus.Ref.mk applied to inner.
        let ExprNode::App { head, args } = &result.node else {
            panic!("expected App, got {:?}", result.node);
        };
        let ExprNode::Var(head_name) = &head.node else {
            panic!("expected Var head");
        };
        assert_eq!(head_name.as_str(), "Tactus.Ref.mk");
        assert_eq!(args.len(), 1);
        // The arg is `value.deref` (peeled MutRef).
        assert!(is_single_deref(&args[0]),
            "expected inner to be `value.deref`, got {:?}", args[0].node);
    }

    #[test]
    fn into_slot_preserves_common_inner_suffix() {
        // value : Tactus.Box (Tactus.Ref Int); slot : Tactus.Ref (Tactus.Ref Int).
        // Common inner suffix [Ref]. Expect: peel outer Box, wrap outer Ref.
        // Result: `Tactus.Ref.mk value.deref`.
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(ref_typ(int_typ())),
        );
        let result = typed.into_slot(&ref_typ(ref_typ(int_typ())));
        let ExprNode::App { head, args } = &result.node else {
            panic!("expected App, got {:?}", result.node);
        };
        let ExprNode::Var(head_name) = &head.node else {
            panic!("expected Var head");
        };
        assert_eq!(head_name.as_str(), "Tactus.Ref.mk");
        // The arg is `value.deref` — only ONE peel (outer Box), not two.
        // If we peeled fully (two derefs) it'd be `value.deref.deref`.
        assert!(is_single_deref(&args[0]),
            "expected single deref (common suffix preserved), got {:?}", args[0].node);
    }

    #[test]
    fn into_slot_disjoint_wraps_peels_fully_then_wraps_fully() {
        // value : Tactus.Box Int; slot : Tactus.Ref Int.
        // Disjoint wraps (no common suffix). Equal depth 1.
        // Expect: peel one, wrap one.
        let typed = TypedExpr::var(LeanName::synthetic("b"), box_typ(int_typ()));
        let result = typed.into_slot(&ref_typ(int_typ()));
        let ExprNode::App { head, args } = &result.node else {
            panic!("expected App");
        };
        let ExprNode::Var(head_name) = &head.node else {
            panic!("expected Var head");
        };
        assert_eq!(head_name.as_str(), "Tactus.Ref.mk");
        assert!(is_single_deref(&args[0]));
    }

    // ── Targeted coverage for the kind-aware coercion path. ─────────
    // These tests pin behaviour the depth-only version got wrong;
    // they exercise the full cross-product of wrapper-kind pairs
    // we emit (Ref, MutRef, Box, Rc, Arc) plus multi-layer + common
    // suffix preservation.

    #[test]
    fn into_slot_no_coercion_matching_double_wrappers() {
        // value : Tactus.Box (Tactus.Ref Int); slot : same.
        // Both wraps match exactly → no-op even at depth 2.
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(ref_typ(int_typ())),
        );
        let result = typed.into_slot(&box_typ(ref_typ(int_typ())));
        // Bare Var — no FieldProj, no App.
        assert!(matches!(&result.node, ExprNode::Var(_)),
            "expected bare Var (no coercion), got {:?}", result.node);
    }

    #[test]
    fn into_slot_kind_mismatch_outer_only_preserves_inner() {
        // value : Tactus.Box (Tactus.Ref Int); slot : Tactus.Rc (Tactus.Ref Int).
        // Common inner suffix [Ref] — only outer Box/Rc differs.
        // Expect: peel one (outer Box), wrap one (outer Rc), preserve inner Ref.
        // Result: `Tactus.Rc.mk value.deref`. Critically NOT `Tactus.Rc.mk (Tactus.Ref.mk value.deref.deref)`.
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(ref_typ(int_typ())),
        );
        let result = typed.into_slot(&rc_typ(ref_typ(int_typ())));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Rc"], "expected one outer Rc wrap only");
        let (deref_count, _) = count_derefs(inner);
        assert_eq!(deref_count, 1, "expected exactly one deref (outer Box peeled)");
    }

    #[test]
    fn into_slot_rc_to_arc_at_depth_one() {
        // value : Tactus.Rc Int; slot : Tactus.Arc Int.
        // Kind mismatch, disjoint at depth 1. Peel one, wrap one.
        let typed = TypedExpr::var(LeanName::synthetic("r"), rc_typ(int_typ()));
        let result = typed.into_slot(&arc_typ(int_typ()));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Arc"]);
        assert!(is_single_deref(inner));
    }

    #[test]
    fn into_slot_mut_ref_to_box_at_depth_one() {
        // value : Tactus.MutRef Int; slot : Tactus.Box Int.
        // Different-kind bridge through a non-Ref wrapper pair.
        let typed = TypedExpr::var(LeanName::synthetic("m"), mut_ref_typ(int_typ()));
        let result = typed.into_slot(&box_typ(int_typ()));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Box"]);
        assert!(is_single_deref(inner));
    }

    #[test]
    fn into_slot_three_layer_preserve_two_inner() {
        // value : Tactus.Box (Tactus.Rc (Tactus.Ref Int));
        // slot  : Tactus.Arc (Tactus.Rc (Tactus.Ref Int)).
        // Common inner suffix [Rc, Ref] (length 2). Only outermost differs.
        // Peel 1 (Box), wrap 1 (Arc). Inner two wraps untouched.
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(rc_typ(ref_typ(int_typ()))),
        );
        let result = typed.into_slot(&arc_typ(rc_typ(ref_typ(int_typ()))));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Arc"]);
        let (deref_count, _) = count_derefs(inner);
        assert_eq!(deref_count, 1, "expected single deref (one outer peel)");
    }

    #[test]
    fn into_slot_three_layer_fully_disjoint() {
        // value : Tactus.Box (Tactus.Rc (Tactus.Ref Int));
        // slot  : Tactus.Ref (Tactus.Arc (Tactus.MutRef Int)).
        // No common suffix. Full peel (3) + full wrap (3).
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(rc_typ(ref_typ(int_typ()))),
        );
        let result = typed.into_slot(&ref_typ(arc_typ(mut_ref_typ(int_typ()))));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Ref", "Tactus.Arc", "Tactus.MutRef"],
            "expected outer→inner wraps [Ref, Arc, MutRef]");
        let (deref_count, _) = count_derefs(inner);
        assert_eq!(deref_count, 3, "expected three derefs (full peel)");
    }

    #[test]
    fn into_slot_growing_depth_preserves_existing_inner() {
        // value : Tactus.Ref Int; slot : Tactus.Box (Tactus.Ref Int).
        // Common inner suffix [Ref]. Wrap outer Box only.
        let typed = TypedExpr::var(LeanName::synthetic("r"), ref_typ(int_typ()));
        let result = typed.into_slot(&box_typ(ref_typ(int_typ())));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Box"]);
        // Inner is just `r` — no derefs, no further wraps.
        assert!(matches!(&inner.node, ExprNode::Var(_)),
            "expected bare Var inner, got {:?}", inner.node);
    }

    #[test]
    fn into_slot_shrinking_depth_preserves_existing_inner() {
        // value : Tactus.Box (Tactus.Ref Int); slot : Tactus.Ref Int.
        // Common inner suffix [Ref]. Peel outer Box only.
        let typed = TypedExpr::var(
            LeanName::synthetic("v"),
            box_typ(ref_typ(int_typ())),
        );
        let result = typed.into_slot(&ref_typ(int_typ()));
        // Result should be bare `.deref` (no wrap chain).
        assert!(is_single_deref(&result),
            "expected single deref, got {:?}", result.node);
    }

    #[test]
    fn into_slot_no_coercion_when_wraps_match_with_different_inner_typs() {
        // value : Tactus.Ref Int; slot : Tactus.Ref Bool.
        // Wrappers match exactly; inner types differ but we don't
        // model inner. Returns value unchanged — Lean's type checker
        // is responsible for the inner-mismatch error at use site.
        let bool_typ = Arc::new(TypX::Bool);
        let typed = TypedExpr::var(LeanName::synthetic("r"), ref_typ(int_typ()));
        let result = typed.into_slot(&ref_typ(bool_typ));
        assert!(matches!(&result.node, ExprNode::Var(_)),
            "expected bare Var (no coercion), got {:?}", result.node);
    }

    #[test]
    fn coerce_to_updates_typ_after_kind_bridge() {
        // After coerce_to with kind mismatch, the resulting TypedExpr's
        // typ field reflects the target — important because callers may
        // chain further compositions that rely on the new typ.
        let typed = TypedExpr::var(LeanName::synthetic("m"), mut_ref_typ(int_typ()));
        let target = ref_typ(int_typ());
        let coerced = typed.coerce_to(&target);
        // Typ field updated to Ref.
        let TypX::Decorate(deco, _, _) = &*coerced.typ else {
            panic!("expected Decorate typ, got {:?}", coerced.typ);
        };
        assert!(matches!(deco, TypDecoration::Ref));
        // Inner expr has peel + wrap structure.
        let (wraps, inner) = collect_mk_wraps(&coerced.inner);
        assert_eq!(wraps, vec!["Tactus.Ref"]);
        assert!(is_single_deref(inner));
    }

    #[test]
    fn apply_handles_kind_mismatch_in_args() {
        // head : opaque function head; apply with one arg whose typ
        // mismatches the param typ via wrapper KIND (not just depth).
        let head = TypedExpr::var(LeanName::synthetic("f"), int_typ());
        let arg = TypedExpr::var(LeanName::synthetic("m"), mut_ref_typ(int_typ()));
        let param_typs = vec![ref_typ(int_typ())];
        let result = head.apply(vec![arg], &param_typs, int_typ());
        let ExprNode::App { args, .. } = &result.inner.node else {
            panic!("expected App, got {:?}", result.inner.node);
        };
        // The arg should be coerced: MutRef → Ref via peel + wrap.
        let (wraps, inner) = collect_mk_wraps(&args[0]);
        assert_eq!(wraps, vec!["Tactus.Ref"]);
        assert!(is_single_deref(inner));
    }

    #[test]
    fn wrap_chain_order_outermost_last_applied() {
        // Regression guard for apply_wrap_chain's reverse-iteration
        // detail: wraps slice is outermost-first, but applied
        // innermost-first to build the right structure.
        // value : Int; slot : Tactus.Box (Tactus.Ref Int).
        // Expected: `Tactus.Box.mk (Tactus.Ref.mk val)` —
        // Box outermost (last applied = outermost in the result tree).
        let typed = TypedExpr::var(LeanName::synthetic("x"), int_typ());
        let result = typed.into_slot(&box_typ(ref_typ(int_typ())));
        let (wraps, inner) = collect_mk_wraps(&result);
        assert_eq!(wraps, vec!["Tactus.Box", "Tactus.Ref"],
            "expected outer→inner [Box, Ref]");
        // No derefs (depth-0 to depth-2 → pure wrap chain).
        let (deref_count, base) = count_derefs(inner);
        assert_eq!(deref_count, 0);
        assert!(matches!(&base.node, ExprNode::Var(_)));
    }
}
