//! Translate Tactus IR types to Lean 4 type syntax.

use crate::ir::{IntRange, Typ};

/// Translate a Tactus type to Lean 4 type text.
pub fn typ_to_lean(typ: &Typ) -> String {
    match typ {
        Typ::Bool => "Prop".to_string(),
        Typ::Int(range) => int_range_to_lean(range),
        Typ::Named(name) => name.clone(),
        Typ::Tuple(elems) => {
            if elems.is_empty() {
                "Unit".to_string()
            } else {
                let parts: Vec<String> = elems.iter().map(typ_to_lean).collect();
                parts.join(" × ")
            }
        }
        Typ::Fun(params, ret) => {
            let mut parts: Vec<String> = params.iter().map(typ_to_lean).collect();
            parts.push(typ_to_lean(ret));
            parts.join(" → ")
        }
        Typ::TypParam(name) => name.clone(),
    }
}

/// Translate an integer range to a Lean type.
fn int_range_to_lean(range: &IntRange) -> String {
    match range {
        IntRange::Int => "Int".to_string(),
        IntRange::Nat => "Nat".to_string(),
        // Fixed-width types map to Int/Nat with overflow constraints handled separately
        IntRange::U(_) | IntRange::USize => "Nat".to_string(),
        IntRange::I(_) | IntRange::ISize => "Int".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_types() {
        assert_eq!(typ_to_lean(&Typ::Bool), "Prop");
        assert_eq!(typ_to_lean(&Typ::Int(IntRange::Int)), "Int");
        assert_eq!(typ_to_lean(&Typ::Int(IntRange::Nat)), "Nat");
        assert_eq!(typ_to_lean(&Typ::Int(IntRange::U(32))), "Nat");
        assert_eq!(typ_to_lean(&Typ::Int(IntRange::I(64))), "Int");
    }

    #[test]
    fn test_tuple() {
        let t = Typ::Tuple(vec![
            Typ::Int(IntRange::Int),
            Typ::Int(IntRange::Nat),
        ]);
        assert_eq!(typ_to_lean(&t), "Int × Nat");
    }

    #[test]
    fn test_unit() {
        assert_eq!(typ_to_lean(&Typ::Tuple(vec![])), "Unit");
    }

    #[test]
    fn test_function_type() {
        let t = Typ::Fun(
            vec![Typ::Int(IntRange::Nat), Typ::Int(IntRange::Nat)],
            Box::new(Typ::Int(IntRange::Nat)),
        );
        assert_eq!(typ_to_lean(&t), "Nat → Nat → Nat");
    }

    #[test]
    fn test_type_param() {
        assert_eq!(typ_to_lean(&Typ::TypParam("T".into())), "T");
    }
}
