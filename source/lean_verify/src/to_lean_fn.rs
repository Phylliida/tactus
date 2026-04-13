//! Translate VIR functions to Lean 4 definitions and theorems.

use vir::ast::*;
use crate::dep_order::{FnGroup, order_spec_fns};
use crate::prelude::TACTUS_PRELUDE;
use crate::to_lean_expr::{write_expr, write_name};
use crate::to_lean_type::write_typ;

/// Generate a complete Lean file from VIR functions.
///
/// `all_fns` is the full set of VIR functions from the crate.
/// `proof_fns` are the proof fns to verify, each paired with tactic body text.
/// Spec fns are automatically filtered to only those transitively referenced,
/// topologically sorted, and grouped by mutual recursion.
pub fn generate_lean_file(
    all_fns: &[&FunctionX],
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

    // Order spec fns: filter to referenced, topological sort, group mutual recursion
    let proof_fn_refs: Vec<&FunctionX> = proof_fns.iter().map(|(f, _)| *f).collect();
    let groups = order_spec_fns(all_fns, &proof_fn_refs);

    for group in &groups {
        match group {
            FnGroup::Single(f) => {
                write_spec_fn(&mut out, f);
                out.push('\n');
            }
            FnGroup::Mutual(fns) => {
                out.push_str("mutual\n");
                for f in fns {
                    write_spec_fn(&mut out, f);
                    out.push('\n');
                }
                out.push_str("end\n\n");
            }
        }
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
