//! Translate VIR types to Lean 4 type syntax.
//!
//! `typ_to_expr` is the canonical API — it returns a `lean_ast::Expr` (in
//! Lean, types are expressions). `write_typ` is a thin compatibility wrapper
//! that pretty-prints into a `String` buffer; callers are gradually moving
//! off it.

use vir::ast::{Dt, IntRange, Path, TypX};
use crate::lean_ast::{BinOp, Expr, ExprNode};
use crate::lean_pp::pp_expr;

/// Write a VIR type as Lean 4 syntax by way of the AST + pretty-printer.
/// Preserved for callers that still emit into a shared `String` buffer.
pub fn write_typ(out: &mut String, typ: &TypX) {
    out.push_str(&pp_expr(&typ_to_expr(typ)));
}

/// Canonical VIR-type → Lean-AST translator.
pub fn typ_to_expr(typ: &TypX) -> Expr {
    Expr::new(typ_to_node(typ))
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
            IntRange::Int | IntRange::I(_) | IntRange::ISize => "Int".into(),
            IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char => "Nat".into(),
        }),
        TypX::TypParam(name) => ExprNode::Var(name.to_string()),
        TypX::Boxed(inner) => typ_to_node(inner),
        TypX::Datatype(dt, args, _) => {
            let name = match dt {
                Dt::Path(path) => lean_name(path),
                Dt::Tuple(n) => format!("Tuple{}", n),
            };
            applied(&name, args.iter().map(|a| typ_to_expr(a)).collect())
        }
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
            // Zero-sized identifier type → Unit (possibly paired with extra
            // type args for disambiguation).
            if typs.is_empty() {
                ExprNode::Var("Unit".into())
            } else {
                // `(Unit × T₁ × T₂ …)` — emitted as Raw since `×` is not in
                // our BinOp set (no need to add it just for this one case).
                let mut s = String::from("(Unit");
                for t in typs.iter() {
                    s.push_str(" × ");
                    s.push_str(&pp_expr(&typ_to_expr(t)));
                }
                s.push(')');
                ExprNode::Raw(s)
            }
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
    relevant.iter()
        .map(|s| sanitize_ident(s))
        .collect::<Vec<_>>()
        .join(".")
}

pub(crate) fn needs_sanitization(s: &str) -> bool {
    is_lean_keyword(s) || s.bytes().any(|b| b == b'@' || b == b'#' || b == b'%')
}

pub(crate) fn sanitize_ident(s: &str) -> String {
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        // `%` appears in Verus-synthetic identifiers (e.g., `tmp%` from
        // desugared `assert(P)`). `@`/`#` come from VIR's disambiguation
        // suffixes. All three get squashed to `_` since Lean identifiers
        // accept underscores.
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

/// Convenience: return type as String.
pub fn typ_to_lean(typ: &TypX) -> String {
    let mut s = String::new();
    write_typ(&mut s, typ);
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_basic_types() {
        assert_eq!(typ_to_lean(&TypX::Bool), "Prop");
        assert_eq!(typ_to_lean(&TypX::Int(IntRange::Int)), "Int");
        assert_eq!(typ_to_lean(&TypX::Int(IntRange::Nat)), "Nat");
        assert_eq!(typ_to_lean(&TypX::Int(IntRange::U(32))), "Nat");
        assert_eq!(typ_to_lean(&TypX::Int(IntRange::I(64))), "Int");
    }

    #[test]
    fn test_type_param() {
        assert_eq!(typ_to_lean(&TypX::TypParam(Arc::new("T".into()))), "T");
    }

    #[test]
    fn test_boxed_transparent() {
        assert_eq!(typ_to_lean(&TypX::Boxed(Arc::new(TypX::Int(IntRange::Nat)))), "Nat");
    }

    #[test]
    fn test_spec_fn_type() {
        let t = TypX::SpecFn(
            Arc::new(vec![Arc::new(TypX::Int(IntRange::Nat))]),
            Arc::new(TypX::Int(IntRange::Nat)),
        );
        assert_eq!(typ_to_lean(&t), "Nat → Nat");
    }
}
