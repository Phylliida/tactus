//! Translate VIR types to Lean 4 type syntax.

use std::sync::Arc;
use vir::ast::{Dt, IntRange, TypX};

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
                Dt::Path(path) => write_path_last(out, &path.segments),
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
        _ => write_todo(out, "type"),
    }
}

/// Write the last segment of a path.
pub(crate) fn write_path_last(out: &mut String, segments: &[Arc<String>]) {
    out.push_str(segments.last().map(|s| s.as_str()).unwrap_or("_"));
}

/// Write a `sorry` placeholder with a TODO comment.
pub(crate) fn write_todo(out: &mut String, what: &str) {
    out.push_str("sorry /- TODO: ");
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
