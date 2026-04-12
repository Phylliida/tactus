//! Translate VIR functions to Lean 4 definitions and theorems.

use vir::ast::*;
use crate::prelude::TACTUS_PRELUDE;
use crate::to_lean_expr::write_expr;
use crate::to_lean_type::write_typ;

/// Generate a complete Lean file from VIR functions.
///
/// `spec_fns` must be in dependency order (callees before callers).
/// `proof_fns` are emitted after all spec fns.
/// Each proof fn is paired with its tactic body text.
pub fn generate_lean_file(
    spec_fns: &[&FunctionX],
    proof_fns: &[(&FunctionX, &str)], // (function, tactic_body)
    imports: &[String],
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

    for f in spec_fns {
        write_spec_fn(&mut out, f);
        out.push('\n');
    }

    for (f, tactics) in proof_fns {
        write_proof_fn(&mut out, f, tactics);
        out.push('\n');
    }

    out
}

/// Write a spec fn as `@[irreducible] noncomputable def`.
pub fn write_spec_fn(out: &mut String, f: &FunctionX) {
    let is_open = !matches!(f.opaqueness, Opaqueness::Opaque);
    if !is_open {
        out.push_str("@[irreducible] ");
    }
    out.push_str("noncomputable def ");

    write_fn_name(out, &f.name);

    for tp in f.typ_params.iter() {
        out.push_str(" (");
        out.push_str(tp);
        out.push_str(" : Type*)");
    }

    for p in f.params.iter() {
        out.push_str(" (");
        out.push_str(&p.x.name.0);
        out.push_str(" : ");
        write_typ(out, &p.x.typ);
        out.push(')');
    }

    out.push_str(" : ");
    write_typ(out, &f.ret.x.typ);
    out.push_str(" :=\n  ");

    if let Some(body) = &f.body {
        write_expr(out, &body.x);
    } else {
        out.push_str("sorry");
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

    for tp in f.typ_params.iter() {
        out.push_str(" (");
        out.push_str(tp);
        out.push_str(" : Type*)");
    }

    for p in f.params.iter() {
        out.push_str(" (");
        out.push_str(&p.x.name.0);
        out.push_str(" : ");
        write_typ(out, &p.x.typ);
        out.push(')');
    }

    // requires → hypotheses
    for (i, req) in f.require.iter().enumerate() {
        out.push_str(" (h");
        out.push_str(&i.to_string());
        out.push_str(" : ");
        write_expr(out, &req.x);
        out.push(')');
    }

    // ensures → goal
    out.push_str(" :\n    ");
    write_ensures(out, &f.ensure.0);
    out.push_str(" := by\n");

    // tactic body (verbatim, indented 2 spaces)
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

fn write_ensures(out: &mut String, ensures: &[Expr]) {
    if ensures.is_empty() {
        out.push_str("True");
    } else if ensures.len() == 1 {
        write_expr(out, &ensures[0].x);
    } else {
        for (i, e) in ensures.iter().enumerate() {
            if i > 0 { out.push_str(" ∧ "); }
            write_expr(out, &e.x);
        }
    }
}

fn write_fn_name(out: &mut String, fun: &Fun) {
    let segments = &fun.path.segments;
    if segments.len() == 1 {
        out.push_str(&segments[0]);
    } else {
        // Use last segment — namespacing handled by caller wrapping in `namespace`
        out.push_str(segments.last().map(|s| s.as_str()).unwrap_or("?"));
    }
}
