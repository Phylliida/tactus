//! Translate VIR types to `lean_ast::Expr` (in Lean, types are expressions).

use vir::ast::{Dt, IntRange, Path, Typ, TypDecoration, TypX};
use crate::lean_ast::{BinOp, Expr, ExprNode};
use crate::lean_name::LeanName;

/// Canonical VIR-type → Lean-AST translator.
pub fn typ_to_expr(typ: &TypX) -> Expr {
    Expr::new(typ_to_node(typ))
}

/// Render a fn parameter's type at the Lean theorem-binder level,
/// uniformly wrapping `&mut` references through `Tactus.MutRef`
/// regardless of which Verus mode produced the param.
///
/// Verus represents `&mut T` params in two distinct shapes depending
/// on mode:
/// * Legacy mode (default): `is_mut: true`, typ = plain `T`.
/// * New-mut-ref mode: `is_mut: false`, typ = `TypX::MutRef(T)`.
///
/// The new-mode shape's `TypX::MutRef` arm of `typ_to_node` already
/// emits `Tactus.MutRef T`. For the legacy shape, the plain typ would
/// emit just `T` — we wrap it here so both modes converge at the
/// binder level. Downstream machinery (body-deref shadow, pre-state
/// capture, call-site substitution) then treats both modes uniformly.
///
/// `is_mut_ref_typ` (in `expr_shared`) is the canonical predicate.
pub(crate) fn param_binder_typ(typ: &Typ, is_mut: bool) -> Expr {
    let rendered = typ_to_expr(typ);
    // If typ already renders through a MutRef wrapper (new mode or
    // decorated shape), no extra wrap needed.
    let already_wrapped = matches!(
        &**typ,
        TypX::MutRef(_) | TypX::Decorate(TypDecoration::MutRef, _, _)
    );
    if is_mut && !already_wrapped {
        Expr::new(ExprNode::App {
            head: Box::new(Expr::new(ExprNode::Var(LeanName::lit("Tactus.MutRef")))),
            args: vec![rendered],
        })
    } else {
        rendered
    }
}

/// True when `typ` is the unit type (`()` in Verus). After
/// `ast_simplify`, tuple types are represented as
/// `TypX::Datatype(Dt::Tuple(n), ...)` — the 0-arity tuple is unit.
///
/// Used to discriminate unit-return proof fns (the common case — pure
/// lemma) from value-returning proof fns (the "extract a witness"
/// shape, which needs subtype rendering for the class method type).
/// Lives in `to_lean_type.rs` rather than `to_lean_fn.rs` because both
/// `to_lean_fn` and `dep_order` need to discriminate the same way; a
/// shared helper avoids subtle drift in what counts as "unit" across
/// the two paths.
pub(crate) fn is_unit_typ(typ: &TypX) -> bool {
    matches!(typ, TypX::Datatype(Dt::Tuple(0), _, _))
}

/// Peel `TypX::Boxed` (poly coercion) and `TypX::Decorate` (Rust
/// decorations like `Box<T>`, `&T`, `&mut T`) to reach the
/// underlying type. These are transparent at the Lean level —
/// `typ_to_expr` also peels both — so multiple distinct checks
/// (is-int, is-user-datatype, is-self-referential-field) share
/// this helper. Single edit site if Verus adds a new transparent
/// wrapper.
pub(crate) fn peel_typ_wrappers(typ: &Typ) -> &Typ {
    match &**typ {
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => peel_typ_wrappers(inner),
        _ => typ,
    }
}

fn typ_to_node(typ: &TypX) -> ExprNode {
    // Helper: build `App { head: Var(LeanName::lit(name)), args }`.
    // Type-position names (`Int`, `Prop`, `Array`, etc.) are hardcoded
    // Lean type constructors — the `lit` constructor is correct here.
    let applied = |name: &str, args: Vec<Expr>| {
        if args.is_empty() {
            ExprNode::Var(LeanName::lit(name))
        } else {
            ExprNode::App {
                head: Box::new(Expr::new(ExprNode::Var(LeanName::lit(name)))),
                args,
            }
        }
    };
    let lit_var = |s: &str| ExprNode::Var(LeanName::lit(s));
    match typ {
        TypX::Bool => lit_var("Prop"),
        TypX::Int(range) => lit_var(match range {
            // Fixed-width u-types and i-types render as `Int` so that
            // their spec-mode subtraction is mathematical (can go
            // negative); `HasType` bounds then catch underflow.
            IntRange::Int | IntRange::I(_) | IntRange::ISize
            | IntRange::U(_) => "Int",
            // `nat` maps directly to Lean `Nat` — matching semantics.
            // `USize` stays `Nat` too (rather than `Int`) because
            // Verus elides `as nat` casts from `usize` in spec
            // contexts — const-generic bodies like `N as nat`
            // render as just `N`, so the param's Lean type has to
            // BE `Nat` or we get a type mismatch. Same reason for
            // `Char`. The upper bound still gets emitted via the
            // `usize_hi` prelude axiom in `type_bound_predicate`;
            // the subtraction-truncation risk that motivated u8→Int
            // exists here but is rare in practice for usize and
            // accepted as a known gap pending a deeper fix.
            IntRange::Nat | IntRange::USize | IntRange::Char => "Nat",
        }),
        // Type parameter names are user-named generic params (`A`, `T`,
        // etc.). They come from VIR as plain `Ident`, no disambiguator —
        // emit via `lit` since they're already valid identifiers.
        TypX::TypParam(name) => ExprNode::Var(LeanName::lit(name.as_str())),
        TypX::Boxed(inner) => typ_to_node(inner),
        TypX::MutRef(inner) => {
            // New-mut-ref-mode shape (`TypX::MutRef`, distinct from the
            // legacy `Decorate(MutRef, _, _)`). Render through the same
            // wrapper as legacy mode for uniformity.
            applied("Tactus.MutRef", vec![typ_to_expr(inner)])
        }
        TypX::Datatype(dt, args, _) => match dt {
            Dt::Path(path) => applied(&lean_name(path), args.iter().map(|a| typ_to_expr(a)).collect()),
            // Anonymous Rust tuple → Lean product type `T₁ × T₂ × … × Tₙ`.
            // Zero-element → `Unit`; single-element → the element itself
            // (Verus doesn't produce 1-tuples, but handle it defensively).
            Dt::Tuple(_) => match args.len() {
                0 => lit_var("Unit"),
                1 => typ_to_node(&args[0]),
                _ => {
                    let mut iter = args.iter().rev();
                    let mut acc = typ_to_expr(iter.next().unwrap());
                    for a in iter {
                        acc = Expr::new(ExprNode::BinOp {
                            op: BinOp::Prod,
                            lhs: Box::new(typ_to_expr(a)),
                            rhs: Box::new(acc),
                        });
                    }
                    acc.node
                }
            },
        },
        TypX::SpecFn(params, ret) => {
            // Fold params right-to-left into nested → so the AST reflects
            // Lean's right-associative arrow.
            let mut out = typ_to_expr(ret);
            for p in params.iter().rev() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Implies,
                    lhs: Box::new(typ_to_expr(p)),
                    rhs: Box::new(out),
                });
            }
            out.node
        }
        TypX::Decorate(deco, _, inner) => {
            // Reference-like decorations preserve type identity at the
            // Lean level so trait dispatch can distinguish `Ref A` from
            // `A`. Verus's Z3 path handles this via DECORATE=true type-IDs
            // in `sst_to_air::monotyp_to_id` (two-component `(REF, basic
            // A)` vs `(NIL_SIZED, basic A)`). Lean has no separate type-
            // ID channel; we use real distinct opaque types from the
            // prelude.
            //
            // Other decorations (Ghost, Tracked, Never, ConstPtr) stay
            // transparent — they're verification metadata or zero-cost
            // markers, not types user code observes at the spec level.
            use vir::ast::TypDecoration;
            match deco {
                TypDecoration::Ref => applied("Tactus.Ref", vec![typ_to_expr(inner)]),
                TypDecoration::MutRef => applied("Tactus.MutRef", vec![typ_to_expr(inner)]),
                TypDecoration::Box => applied("Tactus.Box", vec![typ_to_expr(inner)]),
                TypDecoration::Rc => applied("Tactus.Rc", vec![typ_to_expr(inner)]),
                TypDecoration::Arc => applied("Tactus.Arc", vec![typ_to_expr(inner)]),
                TypDecoration::Ghost | TypDecoration::Tracked
                | TypDecoration::Never | TypDecoration::ConstPtr => typ_to_node(inner),
            }
        }
        TypX::Projection { trait_typ_args, trait_path, name } => {
            // <Self as Trait>::AssocType → Trait.AssocType Self …
            let head = format!("{}.{}", lean_name(trait_path), name);
            applied(&head, trait_typ_args.iter().map(|t| typ_to_expr(t)).collect())
        }
        TypX::Primitive(prim, args) => {
            let head = match prim {
                vir::ast::Primitive::Array => "Array",
                vir::ast::Primitive::Slice => "List",
                vir::ast::Primitive::StrSlice => "String",
                vir::ast::Primitive::Ptr => "USize",
                vir::ast::Primitive::Global => "Unit",
            };
            // Lean's `Array α` and `List α` are unary type
            // constructors; Verus's `[T; N]` carries `[T, N]` as args
            // (element type + const-length), and we drop the length
            // because Lean has no length-indexed Array. Bounds are
            // tracked separately via spec-level `len()` queries.
            // Slice has just `[T]`, but applying defensively for both.
            let type_args: Vec<_> = match prim {
                vir::ast::Primitive::Array | vir::ast::Primitive::Slice => {
                    args.iter().take(1).map(|a| typ_to_expr(a)).collect()
                }
                _ => args.iter().map(|a| typ_to_expr(a)).collect(),
            };
            applied(head, type_args)
        }
        TypX::ConstInt(n) => ExprNode::Lit(n.to_string()),
        TypX::ConstBool(b) => lit_var(if *b { "true" } else { "false" }),
        TypX::Real => lit_var("Real"),
        TypX::Float(_) => lit_var("Float"),
        TypX::TypeId => lit_var("Nat"),
        TypX::FnDef(_, typs, _) => {
            // Zero-sized identifier type → `Unit` (possibly paired with
            // extra type args for disambiguation as `Unit × T₁ × T₂ …`).
            // `×` is right-associative, so folding from the right gives
            // the pp the shape Lean expects without defensive parens.
            let mut out = Expr::new(lit_var("Unit"));
            for t in typs.iter() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Prod,
                    lhs: Box::new(out),
                    rhs: Box::new(typ_to_expr(t)),
                });
            }
            out.node
        }
        TypX::AnonymousClosure(params, ret, _, _) => {
            let mut out = typ_to_expr(ret);
            for p in params.iter().rev() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Implies,
                    lhs: Box::new(typ_to_expr(p)),
                    rhs: Box::new(out),
                });
            }
            out.node
        }
        TypX::Dyn(path, args, _) => {
            applied(&lean_name(path), args.iter().map(|a| typ_to_expr(a)).collect())
        }
        TypX::Opaque { def_path, args } => {
            applied(&lean_name(def_path), args.iter().map(|a| typ_to_expr(a)).collect())
        }
        TypX::PointeeMetadata(_) => lit_var("Nat"),
        TypX::Air(_) => panic!("TypX::Air should not appear in Tactus translation"),
    }
}

/// Get the short name (last path segment) from a VIR path.
pub(crate) fn short_name(path: &Path) -> &str {
    path.segments.last().map(|s| s.as_str()).unwrap_or("_")
}

/// Derive a single-segment "type name" suitable for use as a Lean
/// namespace prefix, peeling transparent decoration. Returns `None`
/// for shapes without an obvious type name (closures, anonymous
/// tuples, primitives without a clean ID), in which case the impl-
/// method naturalisation should fall back to the synthetic
/// `impl__N` form.
///
/// Used by `impl_subst::set_method_context` to compute the natural
/// name `<self>.<trait>.<method>` for impl method standalone defs.
pub(crate) fn type_short_name(typ: &vir::ast::Typ) -> Option<String> {
    use vir::ast::TypX;
    let mut cur = typ.clone();
    loop {
        match &*cur.clone() {
            TypX::Decorate(_, _, inner) | TypX::Boxed(inner)
            | TypX::MutRef(inner) => cur = inner.clone(),
            TypX::Datatype(dt, _, _) => return match dt {
                vir::ast::Dt::Path(p) => Some(short_name(p).to_string()),
                vir::ast::Dt::Tuple(_) => None,
            },
            TypX::Primitive(p, _) => return Some(match p {
                vir::ast::Primitive::Array => "Array".to_string(),
                vir::ast::Primitive::Slice => "Slice".to_string(),
                vir::ast::Primitive::StrSlice => "StrSlice".to_string(),
                vir::ast::Primitive::Ptr => "Ptr".to_string(),
                vir::ast::Primitive::Global => "Global".to_string(),
            }),
            TypX::TypParam(name) => return Some(name.as_str().to_string()),
            TypX::Dyn(p, _, _) | TypX::Opaque { def_path: p, .. } =>
                return Some(short_name(p).to_string()),
            TypX::Int(_) | TypX::Bool | TypX::Real | TypX::Float(_)
            | TypX::TypeId | TypX::ConstInt(_) | TypX::ConstBool(_)
            | TypX::SpecFn(..) | TypX::AnonymousClosure(..) | TypX::FnDef(..)
            | TypX::PointeeMetadata(_) | TypX::Air(_) | TypX::Projection { .. } =>
                return None,
        }
    }
}

/// Convert a VIR path to a Lean dotted name, skipping the crate prefix.
/// `crate::module::name` → `module.name`
/// Names are sanitized (@ # → _) and keywords are escaped with «».
pub(crate) fn lean_name(path: &Path) -> String {
    // Sanitize every segment, including synthetic impl markers
    // (`impl&%0` → `impl__0`). The marker segments are load-bearing:
    // they disambiguate impl method names so multiple impls of the
    // same trait method don't collide on the bare method name. Pre-
    // 2026-05-17 this function filtered them out (a cosmetic
    // simplification that worked when the dep walk only ever pulled
    // one impl per file into scope); BUG-no-helper-proof-fn-call-
    // from-exec.md's helper-proof-fn emission widened the dep walk
    // and surfaced the underlying naming collision. Keeping the
    // markers produces names like `impl__0.is_zero` /
    // `impl__1.is_zero` — uglier but unique. Strip then rewrites
    // class-qualified sibling refs to these disambiguated forms
    // (see `strip_class_qualifier`).
    let segments: Vec<String> = path.segments.iter()
        .map(|s| sanitize(s))
        .collect();
    if segments.len() == 1 && !needs_sanitization(&path.segments[0]) {
        return path.segments[0].to_string();
    }
    segments.join(".")
}

fn needs_sanitization(s: &str) -> bool {
    is_lean_keyword(s) || s.bytes().any(|b|
        b == b'@' || b == b'#' || b == b'%' || b == b'&'
    )
}

/// Make a raw identifier safe to emit as a Lean identifier: keyword-quote
/// with `«…»` if it collides with a Lean reserved word, otherwise squash
/// Verus-internal punctuation to `_`:
/// * `%` from `assert(P)` desugaring
/// * `@` / `#` from VIR disambiguation
/// * `&` from synthetic impl markers (`impl&%0` → `impl__0`)
///
/// No-op fast path for the common case of already-safe names.
pub(crate) fn sanitize(s: &str) -> String {
    if !needs_sanitization(s) {
        return s.to_string();
    }
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        s.chars().map(|c| match c { '@' | '#' | '%' | '&' => '_', _ => c }).collect()
    }
}

fn is_lean_keyword(s: &str) -> bool {
    matches!(s,
        "def" | "theorem" | "lemma" | "example" | "abbrev" | "instance" | "class"
        | "structure" | "inductive" | "where" | "with" | "match" | "do" | "return"
        | "if" | "then" | "else" | "let" | "have" | "show" | "by" | "at" | "fun"
        | "forall" | "exists" | "Type" | "Prop" | "Sort" | "import" | "open"
        | "namespace" | "section" | "end" | "variable" | "universe"
    )
}

/// Walk a TypX recursively, calling `visit` at each node.
/// Preserves the input lifetime `'a` so callers can borrow from the AST.
pub(crate) fn walk_typ<'a>(typ: &'a TypX, visit: &mut impl FnMut(&'a TypX)) {
    visit(typ);
    match typ {
        TypX::Datatype(_, args, _) => {
            for arg in args.iter() { walk_typ(arg, visit); }
        }
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => walk_typ(inner, visit),
        TypX::SpecFn(params, ret) => {
            for p in params.iter() { walk_typ(p, visit); }
            walk_typ(ret, visit);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_pp::pp_expr;
    use std::sync::Arc;

    fn render(t: &TypX) -> String { pp_expr(&typ_to_expr(t)) }

    #[test]
    fn test_basic_types() {
        assert_eq!(render(&TypX::Bool), "Prop");
        assert_eq!(render(&TypX::Int(IntRange::Int)), "Int");
        assert_eq!(render(&TypX::Int(IntRange::Nat)), "Nat");
        assert_eq!(render(&TypX::Int(IntRange::U(32))), "Int");
        assert_eq!(render(&TypX::Int(IntRange::I(64))), "Int");
    }

    #[test]
    fn test_type_param() {
        assert_eq!(render(&TypX::TypParam(Arc::new("T".into()))), "T");
    }

    #[test]
    fn test_boxed_transparent() {
        assert_eq!(render(&TypX::Boxed(Arc::new(TypX::Int(IntRange::Nat)))), "Nat");
    }

    // ── is_unit_typ shape-drift guards ─────────────────────────────

    /// After `ast_simplify`, Verus represents the unit type `()` as
    /// `TypX::Datatype(Dt::Tuple(0), [], _)`. `is_unit_typ` is used in
    /// two places (proof_fn_method_type emission dispatch, dep_order
    /// pre-seeding) — both rely on this exact shape. If Verus ever
    /// changes how the post-simplify unit type is represented, this
    /// test fails with a clear pointer to `is_unit_typ` as the fix
    /// site.
    #[test]
    fn is_unit_typ_recognizes_post_simplify_unit() {
        let unit = TypX::Datatype(
            Dt::Tuple(0),
            Arc::new(vec![]),
            Arc::new(vec![]),
        );
        assert!(is_unit_typ(&unit),
            "Verus's post-simplify unit shape changed; update is_unit_typ");
    }

    #[test]
    fn is_unit_typ_rejects_non_unit_types() {
        assert!(!is_unit_typ(&TypX::Bool));
        assert!(!is_unit_typ(&TypX::Int(IntRange::Int)));
        // Non-zero tuple: NOT unit.
        let pair = TypX::Datatype(
            Dt::Tuple(2),
            Arc::new(vec![Arc::new(TypX::Bool), Arc::new(TypX::Bool)]),
            Arc::new(vec![]),
        );
        assert!(!is_unit_typ(&pair));
    }

    #[test]
    fn test_spec_fn_type() {
        let t = TypX::SpecFn(
            Arc::new(vec![Arc::new(TypX::Int(IntRange::Nat))]),
            Arc::new(TypX::Int(IntRange::Nat)),
        );
        assert_eq!(render(&t), "Nat → Nat");
    }
}
