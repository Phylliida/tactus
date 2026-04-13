//! Translate VIR functions to Lean 4 definitions and theorems.

use vir::ast::*;
use crate::prelude::TACTUS_PRELUDE;
use crate::to_lean_expr::{write_expr, write_name};
use crate::to_lean_type::write_typ;

/// Generate a complete Lean file from VIR functions.
///
/// `spec_fns` must be in dependency order (callees before callers).
/// Each proof fn is paired with its tactic body text.
/// `namespace` is the Lean namespace (e.g., "my_crate.my_module").
pub fn generate_lean_file(
    spec_fns: &[&FunctionX],
    proof_fns: &[(&FunctionX, &str)],
    imports: &[String],
    namespace: Option<&str>,
) -> String {
    let mut out = String::new();
    out.push_str(TACTUS_PRELUDE);

    for imp in imports {
        out.push_str("import ");
        out.push_str(imp);
        out.push('\n');
    }
    if !imports.is_empty() {
        out.push('\n');
    }

    if let Some(ns) = namespace {
        out.push_str("namespace ");
        out.push_str(ns);
        out.push_str("\n\n");
    }

    for f in spec_fns {
        write_spec_fn(&mut out, f);
        out.push('\n');
    }

    for (f, tactics) in proof_fns {
        write_proof_fn(&mut out, f, tactics);
        out.push('\n');
    }

    if let Some(ns) = namespace {
        out.push_str("end ");
        out.push_str(ns);
        out.push('\n');
    }

    out
}

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
        if f.decrease.len() == 1 {
            write_expr(out, &f.decrease[0].x);
        } else {
            out.push('(');
            for (i, d) in f.decrease.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, &d.x);
            }
            out.push(')');
        }
        out.push('\n');
    }
}

/// Write a proof fn as `theorem ... := by <tactics>`.
pub fn write_proof_fn(out: &mut String, f: &FunctionX, tactic_body: &str) {
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

    for line in tactic_body.lines() {
        if line.trim().is_empty() {
            out.push('\n');
        } else {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
    }
}

/// Write type params + value params shared by spec and proof fns.
fn write_fn_params(out: &mut String, f: &FunctionX) {
    for tp in f.typ_params.iter() {
        out.push_str(" (");
        out.push_str(tp);
        out.push_str(" : Type*)");
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
    match ensures.len() {
        0 => out.push_str("True"),
        1 => write_expr(out, &ensures[0].x),
        _ => {
            for (i, e) in ensures.iter().enumerate() {
                if i > 0 { out.push_str(" ∧ "); }
                write_expr(out, &e.x);
            }
        }
    }
}

fn write_fn_name(out: &mut String, fun: &Fun) {
    out.push_str(fun.path.segments.last().map(|s| s.as_str()).unwrap_or("_"));
}
