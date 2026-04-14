//! Write individual VIR declarations as Lean 4 syntax.
//!
//! Each `write_*` function appends Lean text to a `String`.
//! Orchestration (file layout, ordering, imports) is in `generate.rs`.

use std::collections::HashMap;
use vir::ast::*;
use crate::to_lean_expr::{write_expr, write_name};
use crate::to_lean_type::{write_typ, short_name, write_sep, lean_name};

// ── Source map ──────────────────────────────────────────────────────────

/// Maps Lean line numbers back to the proof fn's tactic body.
pub struct LeanSourceMap {
    pub fn_name: String,
    /// 1-indexed line in generated .lean where the tactic body starts
    pub tactic_start_line: usize,
    pub tactic_line_count: usize,
}

impl LeanSourceMap {
    /// Given a 1-indexed Lean line number, return the offset within the tactic body.
    pub fn find_tactic_line(&self, lean_line: usize) -> Option<usize> {
        let end = self.tactic_start_line + self.tactic_line_count;
        if lean_line >= self.tactic_start_line && lean_line < end {
            Some(lean_line - self.tactic_start_line)
        } else {
            None
        }
    }
}

// ── Spec fn ─────────────────────────────────────────────────────────────

/// Write a spec fn as `@[irreducible] noncomputable def`.
pub fn write_spec_fn(out: &mut String, f: &FunctionX) {
    if matches!(f.opaqueness, Opaqueness::Opaque) {
        out.push_str("@[irreducible] ");
    }
    out.push_str("noncomputable def ");
    write_fn_name(out, &f.name);
    write_fn_params(out, f);

    out.push_str(" : ");
    write_typ(out, &f.ret.x.typ);
    out.push_str(" :=\n  ");

    match &f.body {
        Some(body) => write_expr(out, &body.x),
        None => out.push_str("sorry"),
    }
    out.push('\n');

    if !f.decrease.is_empty() {
        out.push_str("termination_by ");
        if f.decrease.len() > 1 { out.push('('); }
        write_sep(out, &*f.decrease, ", ", |out, d| write_expr(out, &d.x));
        if f.decrease.len() > 1 { out.push(')'); }
        out.push('\n');
    }
}

// ── Proof fn ────────────────────────────────────────────────────────────

/// Write a proof fn as `theorem ... := by <tactics>`.
/// Returns the 1-indexed line where the tactic body starts in the output.
pub fn write_proof_fn(out: &mut String, f: &FunctionX, tactic_body: &str) -> usize {
    out.push_str("theorem ");
    write_fn_name(out, &f.name);
    write_fn_params(out, f);

    for (i, req) in f.require.iter().enumerate() {
        out.push_str(" (h");
        out.push_str(&i.to_string());
        out.push_str(" : ");
        write_expr(out, &req.x);
        out.push(')');
    }

    out.push_str(" :\n    ");
    write_ensures(out, &f.ensure.0);
    out.push_str(" := by\n");

    // Record where tactic body starts (1-indexed line number)
    let tactic_start_line = out.chars().filter(|&c| c == '\n').count() + 1;

    for line in tactic_body.lines() {
        if line.trim().is_empty() {
            out.push('\n');
        } else {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    }

    tactic_start_line
}

// ── Datatype ────────────────────────────────────────────────────────────

/// Write a VIR datatype as a Lean `structure` (1 variant) or `inductive` (multiple).
pub fn write_datatype(out: &mut String, dt: &DatatypeX) {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p)),
        Dt::Tuple(_) => return,
    };

    let typ_params_str = dt.typ_params.iter()
        .map(|(id, _)| format!(" ({} : Type)", id))
        .collect::<String>();

    if dt.variants.len() == 1 && dt.variants[0].name.as_str() == short {
        let variant = &dt.variants[0];
        out.push_str(&format!("structure {}{} where\n", path, typ_params_str));
        for field in variant.fields.iter() {
            let (typ, _, _) = &field.a;
            out.push_str("  ");
            write_field_name(out, &field.name);
            out.push_str(" : ");
            write_typ(out, typ);
            out.push('\n');
        }
    } else {
        out.push_str(&format!("inductive {}{} where\n", path, typ_params_str));
        for variant in dt.variants.iter() {
            out.push_str("  | ");
            write_name(out, &variant.name);
            for field in variant.fields.iter() {
                let (typ, _, _) = &field.a;
                out.push_str(" (");
                write_field_name(out, &field.name);
                out.push_str(" : ");
                write_typ(out, typ);
                out.push(')');
            }
            out.push('\n');
        }
    }
}

// ── Trait ────────────────────────────────────────────────────────────────

/// Write a VIR trait as a Lean `class`.
pub fn write_trait(
    out: &mut String,
    tr: &TraitX,
    method_lookup: &HashMap<&Fun, &FunctionX>,
) {
    let name = lean_name(&tr.name);

    out.push_str("class ");
    out.push_str(&name);
    out.push_str(" (Self : Type)");
    for (tp, _) in tr.typ_params.iter() {
        out.push_str(&format!(" ({} : Type)", tp));
    }
    out.push_str(" where\n");

    for method_fun in tr.methods.iter() {
        if let Some(func) = method_lookup.get(method_fun) {
            let method_name = method_fun.path.segments.last()
                .map(|s| s.as_str()).unwrap_or("_");
            out.push_str("  ");
            write_name(out, method_name);
            out.push_str(" : ");
            write_method_type(out, func);
            out.push('\n');
        }
    }
}

/// Write method type: `Self → ParamType → ... → RetType`.
/// Self is detected by name ("self") or position (first param of a method).
fn write_method_type(out: &mut String, func: &FunctionX) {
    for (i, p) in func.params.iter().enumerate() {
        if i > 0 { out.push_str(" → "); }
        let is_self = i == 0 && (p.x.name.0.as_str() == "self"
            || p.x.name.0.contains("self"));
        if is_self { out.push_str("Self"); } else { write_typ(out, &p.x.typ); }
    }
    if !func.params.is_empty() { out.push_str(" → "); }
    write_typ(out, &func.ret.x.typ);
}

// ── Shared helpers ──────────────────────────────────────────────────────

/// Write type params, trait bounds, and value params.
fn write_fn_params(out: &mut String, f: &FunctionX) {
    for tp in f.typ_params.iter() {
        out.push_str(" (");
        out.push_str(tp);
        out.push_str(" : Type)");
    }
    for bound in f.typ_bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), typs) = &**bound {
            out.push_str(" [");
            out.push_str(&lean_name(path));
            for t in typs.iter() {
                out.push(' ');
                write_typ(out, t);
            }
            out.push(']');
        }
    }
    for p in f.params.iter() {
        out.push_str(" (");
        write_name(out, &p.x.name.0);
        out.push_str(" : ");
        write_typ(out, &p.x.typ);
        out.push(')');
    }
}

fn write_ensures(out: &mut String, ensures: &[Expr]) {
    if ensures.is_empty() {
        out.push_str("True");
    } else {
        write_sep(out, ensures, " ∧ ", |out, e| write_expr(out, &e.x));
    }
}

fn write_field_name(out: &mut String, name: &str) {
    if name.parse::<usize>().is_ok() {
        out.push_str("val");
        out.push_str(name);
    } else {
        write_name(out, name);
    }
}

fn write_fn_name(out: &mut String, fun: &Fun) {
    out.push_str(&lean_name(&fun.path));
}
