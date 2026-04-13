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
                Dt::Path(path) => out.push_str(short_name(path)),
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
                vir::ast::Primitive::Ptr => "sorry /- Ptr -/",
                vir::ast::Primitive::Global => "sorry /- Global -/",
            });
            for arg in args.iter() {
                out.push(' ');
                write_typ(out, arg);
            }
        }
        TypX::ConstInt(n) => { out.push_str(&n.to_string()); }
        TypX::ConstBool(b) => { out.push_str(if *b { "true" } else { "false" }); }
        TypX::Real => out.push_str("Real"),
        TypX::TypeId => out.push_str("Nat"), // TypeId has no Lean equivalent, use Nat as placeholder
        _ => write_todo(out, "type"),
    }
}

/// Get the short name (last path segment) from a VIR path.
pub(crate) fn short_name(path: &Path) -> &str {
    path.segments.last().map(|s| s.as_str()).unwrap_or("_")
}

/// Resolve a VIR path to a Lean name, using more segments if short name collides.
pub(crate) fn resolve_name(path: &Path, collisions: &std::collections::HashSet<String>) -> String {
    let short = short_name(path);
    if !collisions.contains(short) {
        return short.to_string();
    }
    // Use last two segments: module.name
    let segs = &path.segments;
    if segs.len() >= 2 {
        format!("{}.{}", segs[segs.len() - 2], segs[segs.len() - 1])
    } else {
        short.to_string()
    }
}

/// Build the set of short names that appear more than once across all declarations.
pub(crate) fn find_collisions<'a>(paths: impl Iterator<Item = &'a str>) -> std::collections::HashSet<String> {
    let mut counts: std::collections::HashMap<&str, usize> = std::collections::HashMap::new();
    for name in paths {
        *counts.entry(name).or_insert(0) += 1;
    }
    counts.into_iter()
        .filter(|(_, count)| *count > 1)
        .map(|(name, _)| name.to_string())
        .collect()
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

/// Write a `sorry` placeholder for an unsupported VIR feature.
pub(crate) fn write_todo(out: &mut String, what: &str) {
    out.push_str("sorry /- UNSUPPORTED: ");
    out.push_str(what);
    out.push_str(" -/");
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
