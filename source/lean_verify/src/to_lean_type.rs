//! Translate VIR types to Lean 4 type syntax.

use std::fmt::Write;
use std::sync::Arc;
use vir::ast::{Dt, IntRange, TypX};

/// Write a VIR type as Lean 4 syntax.
pub fn write_typ(out: &mut String, typ: &TypX) {
    match typ {
        TypX::Bool => out.push_str("Prop"),
        TypX::Int(range) => write_int_range(out, range),
        TypX::TypParam(name) => out.push_str(name),
        TypX::Boxed(inner) => write_typ(out, inner),
        TypX::Datatype(dt, args, _) => {
            match dt {
                Dt::Path(path) => {
                    let name = path.segments.last().map(|s: &Arc<String>| s.as_str()).unwrap_or("?");
                    out.push_str(name);
                }
                Dt::Tuple(n) => {
                    // Tuple type as datatype
                    let _ = write!(out, "Tuple{}", n);
                }
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
        // Types we don't fully handle yet — emit a placeholder
        _ => { let _ = write!(out, "sorry /- unhandled type: {:?} -/", typ); }
    }
}

fn write_int_range(out: &mut String, range: &IntRange) {
    match range {
        IntRange::Int => out.push_str("Int"),
        IntRange::Nat => out.push_str("Nat"),
        IntRange::U(_) | IntRange::USize => out.push_str("Nat"),
        IntRange::I(_) | IntRange::ISize => out.push_str("Int"),
        IntRange::Char => out.push_str("Nat"),
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
        let inner = Arc::new(TypX::Int(IntRange::Nat));
        assert_eq!(typ_to_lean(&TypX::Boxed(inner)), "Nat");
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
