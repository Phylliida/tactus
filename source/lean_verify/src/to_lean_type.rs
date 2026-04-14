//! Translate VIR types to Lean 4 type syntax.

use vir::ast::{Dt, IntRange, Path, TypX};

/// Write a VIR type as Lean 4 syntax.
pub fn write_typ(out: &mut String, typ: &TypX) {
    match typ {
        TypX::Bool => out.push_str("Prop"),
        TypX::Int(range) => out.push_str(match range {
            IntRange::Int | IntRange::I(_) | IntRange::ISize => "Int",
            IntRange::Nat | IntRange::U(_) | IntRange::USize | IntRange::Char => "Nat",
        }),
        TypX::TypParam(name) => out.push_str(name),
        TypX::Boxed(inner) => write_typ(out, inner),
        TypX::Datatype(dt, args, _) => {
            match dt {
                Dt::Path(path) => out.push_str(&lean_name(path)),
                Dt::Tuple(n) => { out.push_str("Tuple"); out.push_str(&n.to_string()); }
            }
            for arg in args.iter() {
                out.push(' ');
                let needs_parens = matches!(&**arg, TypX::Datatype(_, a, _) if !a.is_empty());
                if needs_parens { out.push('('); }
                write_typ(out, arg);
                if needs_parens { out.push(')'); }
            }
        }
        TypX::SpecFn(params, ret) => {
            for param in params.iter() {
                write_typ(out, param);
                out.push_str(" → ");
            }
            write_typ(out, ret);
        }
        // Decorations (references, etc.) are transparent in spec mode
        TypX::Decorate(_, _, inner) => write_typ(out, inner),
        TypX::Projection { name, .. } => out.push_str(name),
        TypX::Primitive(prim, args) => {
            out.push_str(match prim {
                vir::ast::Primitive::Array => "Array",
                vir::ast::Primitive::Slice => "List",
                vir::ast::Primitive::StrSlice => "String",
                vir::ast::Primitive::Ptr => "USize",   // opaque pointer, use Nat-sized
                vir::ast::Primitive::Global => "Unit",  // global state, erased in spec
            });
            for arg in args.iter() {
                out.push(' ');
                write_typ(out, arg);
            }
        }
        TypX::ConstInt(n) => out.push_str(&n.to_string()),
        TypX::ConstBool(b) => out.push_str(if *b { "true" } else { "false" }),
        TypX::Real => out.push_str("Real"),
        TypX::Float(_) => out.push_str("Float"),
        TypX::TypeId => out.push_str("Nat"),
        // Function-as-value types: erase to a function type placeholder
        TypX::FnDef(_, typs, _) => {
            // FnDef is a zero-sized type identifying a specific function.
            // In spec mode, treat as Unit (the function is called by name, not by value).
            if typs.is_empty() { out.push_str("Unit"); }
            else {
                out.push_str("(Unit");
                for t in typs.iter() { out.push_str(" × "); write_typ(out, t); }
                out.push(')');
            }
        }
        TypX::AnonymousClosure(params, ret, _, _) => {
            for p in params.iter() { write_typ(out, p); out.push_str(" → "); }
            write_typ(out, ret);
        }
        TypX::Dyn(path, args, _) => {
            out.push_str(&lean_name(path));
            for arg in args.iter() { out.push(' '); write_typ(out, arg); }
        }
        TypX::Opaque { def_path, args } => {
            out.push_str(&lean_name(def_path));
            for arg in args.iter() { out.push(' '); write_typ(out, arg); }
        }
        TypX::PointeeMetadata(_) => out.push_str("Nat"),
        TypX::MutRef(inner) => write_typ(out, inner), // transparent in spec mode
        // Air types are generated during sst_to_air (which Tactus skips).
        // If one appears here, it's a bug in VIR pipeline ordering.
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
    let segs = &path.segments;
    // Skip the crate segment (first), use the rest as dotted name
    let start = if segs.len() > 1 { 1 } else { 0 };
    segs[start..].iter()
        .map(|s| sanitize_ident(s))
        .collect::<Vec<_>>()
        .join(".")
}

pub(crate) fn sanitize_ident(s: &str) -> String {
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        s.chars().map(|c| match c { '@' | '#' => '_', _ => c }).collect()
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

/// Write items separated by a delimiter.
pub(crate) fn write_sep<T>(
    out: &mut String, items: &[T], sep: &str, mut f: impl FnMut(&mut String, &T),
) {
    for (i, item) in items.iter().enumerate() {
        if i > 0 { out.push_str(sep); }
        f(out, item);
    }
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
