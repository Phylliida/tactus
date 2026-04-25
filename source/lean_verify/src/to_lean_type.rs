//! Translate VIR types to `lean_ast::Expr` (in Lean, types are expressions).

use vir::ast::{Dt, IntRange, Path, Typ, TypX};
use crate::lean_ast::{BinOp, Expr, ExprNode};

/// Canonical VIR-type → Lean-AST translator.
pub fn typ_to_expr(typ: &TypX) -> Expr {
    Expr::new(typ_to_node(typ))
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
    // Helper: build `App { head: Var(name), args }`.
    let applied = |name: &str, args: Vec<Expr>| {
        if args.is_empty() {
            ExprNode::Var(name.to_string())
        } else {
            ExprNode::App {
                head: Box::new(Expr::new(ExprNode::Var(name.to_string()))),
                args,
            }
        }
    };
    match typ {
        TypX::Bool => ExprNode::Var("Prop".into()),
        TypX::Int(range) => ExprNode::Var(match range {
            // Fixed-width u-types and i-types render as `Int` so that
            // their spec-mode subtraction is mathematical (can go
            // negative); `HasType` bounds then catch underflow.
            IntRange::Int | IntRange::I(_) | IntRange::ISize
            | IntRange::U(_) => "Int".into(),
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
            IntRange::Nat | IntRange::USize | IntRange::Char => "Nat".into(),
        }),
        TypX::TypParam(name) => ExprNode::Var(name.to_string()),
        TypX::Boxed(inner) => typ_to_node(inner),
        TypX::Datatype(dt, args, _) => match dt {
            Dt::Path(path) => applied(&lean_name(path), args.iter().map(|a| typ_to_expr(a)).collect()),
            // Anonymous Rust tuple → Lean product type `T₁ × T₂ × … × Tₙ`.
            // Zero-element → `Unit`; single-element → the element itself
            // (Verus doesn't produce 1-tuples, but handle it defensively).
            Dt::Tuple(_) => match args.len() {
                0 => ExprNode::Var("Unit".into()),
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
        TypX::Decorate(_, _, inner) => typ_to_node(inner),
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
            applied(head, args.iter().map(|a| typ_to_expr(a)).collect())
        }
        TypX::ConstInt(n) => ExprNode::Lit(n.to_string()),
        TypX::ConstBool(b) => ExprNode::Var(if *b { "true".into() } else { "false".into() }),
        TypX::Real => ExprNode::Var("Real".into()),
        TypX::Float(_) => ExprNode::Var("Float".into()),
        TypX::TypeId => ExprNode::Var("Nat".into()),
        TypX::FnDef(_, typs, _) => {
            // Zero-sized identifier type → `Unit` (possibly paired with
            // extra type args for disambiguation as `Unit × T₁ × T₂ …`).
            // `×` is right-associative, so folding from the right gives
            // the pp the shape Lean expects without defensive parens.
            let mut out = Expr::new(ExprNode::Var("Unit".into()));
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
        TypX::PointeeMetadata(_) => ExprNode::Var("Nat".into()),
        TypX::MutRef(inner) => typ_to_node(inner),
        TypX::Air(_) => panic!("TypX::Air should not appear in Tactus translation"),
    }
}

/// Get the short name (last path segment) from a VIR path.
pub(crate) fn short_name(path: &Path) -> &str {
    path.segments.last().map(|s| s.as_str()).unwrap_or("_")
}

/// Convert a VIR path to a Lean dotted name, skipping the crate prefix.
/// `crate::module::name` → `module.name`
/// Names are sanitized (@ # → _) and keywords are escaped with «».
pub(crate) fn lean_name(path: &Path) -> String {
    // Filter out synthetic impl segments (e.g., "impl&%0") — these are VIR-internal
    // names for trait impl blocks, not user-visible names. They always contain
    // non-alphanumeric characters like & or %.
    let relevant: Vec<_> = path.segments.iter()
        .filter(|s| !(s.starts_with("impl") && s.bytes().any(|b| b == b'&' || b == b'%')))
        .collect();
    if relevant.len() == 1 && !needs_sanitization(&relevant[0]) {
        return relevant[0].to_string();
    }
    relevant.iter().map(|s| sanitize(s)).collect::<Vec<_>>().join(".")
}

fn needs_sanitization(s: &str) -> bool {
    is_lean_keyword(s) || s.bytes().any(|b| b == b'@' || b == b'#' || b == b'%')
}

/// Make a raw identifier safe to emit as a Lean identifier: keyword-quote
/// with `«…»` if it collides with a Lean reserved word, otherwise squash
/// Verus-internal punctuation (`%` from `assert(P)` desugaring, `@`/`#`
/// from VIR disambiguation) to `_`. No-op fast path for the common case
/// of already-safe names.
pub(crate) fn sanitize(s: &str) -> String {
    if !needs_sanitization(s) {
        return s.to_string();
    }
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        s.chars().map(|c| match c { '@' | '#' | '%' => '_', _ => c }).collect()
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

    #[test]
    fn test_spec_fn_type() {
        let t = TypX::SpecFn(
            Arc::new(vec![Arc::new(TypX::Int(IntRange::Nat))]),
            Arc::new(TypX::Int(IntRange::Nat)),
        );
        assert_eq!(render(&t), "Nat → Nat");
    }
}
