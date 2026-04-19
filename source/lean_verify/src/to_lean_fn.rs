//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    Binder as LBinder, BinderKind, Class, ClassMethod, Command, Datatype,
    DatatypeKind, Def, Expr as LExpr, ExprNode, Field, Instance, InstanceMethod,
    Theorem, Tactic, Variant,
};
use crate::lean_pp::{pp_command, pp_expr};
use crate::to_lean_expr::{sanitize, vir_expr_to_ast};
use crate::to_lean_type::{lean_name, short_name, typ_to_expr};

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

/// Build a `Def` AST node for a spec fn.
pub fn spec_fn_to_ast(f: &FunctionX) -> Def {
    let attrs = if matches!(f.opaqueness, Opaqueness::Opaque) {
        vec!["irreducible".into()]
    } else {
        vec![]
    };
    let body = match &f.body {
        Some(b) => vir_expr_to_ast(b),
        None => LExpr::new(ExprNode::Var("sorry".into())),
    };
    let termination_by = if f.decrease.is_empty() {
        None
    } else if f.decrease.len() == 1 {
        Some(vir_expr_to_ast(&f.decrease[0]))
    } else {
        // Tuple of decreases expressions. AST has no tuple node; emit as Raw.
        let parts: Vec<String> = f.decrease.iter()
            .map(|d| pp_expr(&vir_expr_to_ast(d))).collect();
        Some(LExpr::new(ExprNode::Raw(format!("({})", parts.join(", ")))))
    };
    Def {
        attrs,
        noncomputable: true,
        name: lean_name(&f.name.path),
        binders: fn_binders(f),
        ret_ty: typ_to_expr(&f.ret.x.typ),
        body,
        termination_by,
        span: None,
    }
}

pub fn write_spec_fn(out: &mut String, f: &FunctionX) {
    out.push_str(&pp_command(&Command::Def(spec_fn_to_ast(f))));
}

// ── Proof fn ────────────────────────────────────────────────────────────

/// Build a `Theorem` AST node for a proof fn with the given tactic text.
pub fn proof_fn_to_ast(f: &FunctionX, tactic_body: &str) -> Theorem {
    let mut binders = fn_binders(f);
    for (i, req) in f.require.iter().enumerate() {
        binders.push(LBinder {
            name: Some(format!("h{}", i)),
            ty: vir_expr_to_ast(req),
            kind: BinderKind::Explicit,
        });
    }
    let goal = ensures_conj(&f.ensure.0);
    Theorem {
        name: lean_name(&f.name.path),
        binders,
        goal,
        tactic: Tactic::Raw(tactic_body.to_string()),
        span: None,
    }
}

/// Write a proof fn as a Lean theorem and return the 1-indexed line where
/// the tactic body starts in the accumulated output — callers use this to
/// build a `LeanSourceMap`.
pub fn write_proof_fn(out: &mut String, f: &FunctionX, tactic_body: &str) -> usize {
    let t = proof_fn_to_ast(f, tactic_body);
    let rendered = pp_command(&Command::Theorem(t));
    // The pp format guarantees one `:= by\n` marker in the theorem; count
    // newlines in `out` through (and including) that marker to get the
    // 1-indexed line where the tactic body begins.
    let tail_start = rendered.find(":= by\n").expect("theorem without `:= by`");
    let newlines_before = out.chars().filter(|&c| c == '\n').count();
    let newlines_in_prefix = rendered[..tail_start + ":= by\n".len()]
        .chars().filter(|&c| c == '\n').count();
    let tactic_start_line = newlines_before + newlines_in_prefix + 1;
    out.push_str(&rendered);
    tactic_start_line
}

// ── Datatype ────────────────────────────────────────────────────────────

pub fn datatype_to_ast(dt: &DatatypeX) -> Option<Datatype> {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
        Dt::Tuple(_) => return None,
    };
    let typ_params: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();

    let kind = if dt.variants.len() == 1 && dt.variants[0].name.as_str() == short {
        let variant = &dt.variants[0];
        DatatypeKind::Structure {
            fields: variant.fields.iter().map(|f| Field {
                name: field_name(&f.name),
                ty: typ_to_expr(&f.a.0),
            }).collect(),
        }
    } else {
        DatatypeKind::Inductive {
            variants: dt.variants.iter().map(|v| Variant {
                name: sanitize(&v.name),
                fields: v.fields.iter().map(|f| Field {
                    name: field_name(&f.name),
                    ty: typ_to_expr(&f.a.0),
                }).collect(),
            }).collect(),
        }
    };
    Some(Datatype { name: path, typ_params, kind, span: None })
}

pub fn write_datatype(out: &mut String, dt: &DatatypeX) {
    if let Some(d) = datatype_to_ast(dt) {
        out.push_str(&pp_command(&Command::Datatype(d)));
    }
}

// ── Trait (Lean `class`) ───────────────────────────────────────────────

pub fn trait_to_ast(
    tr: &TraitX,
    method_lookup: &HashMap<&Fun, &FunctionX>,
) -> Class {
    // Positional class binders: `(Self : Type) (T : Type) … (Item : outParam Type)`.
    let mut typ_params: Vec<LBinder> = Vec::new();
    typ_params.push(LBinder {
        name: Some("Self".into()),
        ty: LExpr::new(ExprNode::Var("Type".into())),
        kind: BinderKind::Explicit,
    });
    for (tp, _) in tr.typ_params.iter() {
        typ_params.push(LBinder {
            name: Some(tp.to_string()),
            ty: LExpr::new(ExprNode::Var("Type".into())),
            kind: BinderKind::Explicit,
        });
    }
    for assoc_name in tr.assoc_typs.iter() {
        typ_params.push(LBinder {
            name: Some(sanitize(assoc_name)),
            ty: LExpr::new(ExprNode::Var("Type".into())),
            kind: BinderKind::OutParam,
        });
    }

    let bounds = trait_bounds_to_ast(&tr.typ_bounds);

    let methods = tr.methods.iter().map(|method_fun| {
        let func = method_lookup.get(method_fun).unwrap_or_else(|| {
            panic!(
                "trait method {:?} not found in VIR function list — \
                 this is a Tactus bug, please report it",
                method_fun.path
            )
        });
        let short = method_fun.path.segments.last()
            .map(|s| s.as_str()).unwrap_or("_");
        ClassMethod {
            name: sanitize(short),
            ty: method_type(func),
        }
    }).collect();

    Class {
        name: lean_name(&tr.name),
        typ_params,
        bounds,
        methods,
        span: None,
    }
}

pub fn write_trait(
    out: &mut String,
    tr: &TraitX,
    method_lookup: &HashMap<&Fun, &FunctionX>,
) {
    out.push_str(&pp_command(&Command::Class(trait_to_ast(tr, method_lookup))));
}

/// Build the method type `Self → P₁ → … → Ret`. Inside a class, associated
/// types become unqualified identifiers (they're class type params), so a
/// `TypX::Projection { name, … }` renders as just the projection name.
fn method_type(func: &FunctionX) -> LExpr {
    let param_type = |p: &vir::ast::Param| -> LExpr {
        if p.x.name.0.as_str() == "self" {
            LExpr::new(ExprNode::Var("Self".into()))
        } else {
            typ_maybe_projection_to_expr(&p.x.typ)
        }
    };

    // Fold right-to-left into nested `→`. For zero params, the "arrow
    // chain" is just the return type.
    let mut out = typ_maybe_projection_to_expr(&func.ret.x.typ);
    for p in func.params.iter().rev() {
        out = LExpr::new(ExprNode::BinOp {
            op: crate::lean_ast::BinOp::Implies,
            lhs: Box::new(param_type(p)),
            rhs: Box::new(out),
        });
    }
    out
}

/// Inside a class definition, a `Self::AssocType` projection renders as the
/// bare associated-type name (a class type param). Everywhere else, delegate
/// to the standard type translator.
fn typ_maybe_projection_to_expr(typ: &TypX) -> LExpr {
    if let TypX::Projection { name, .. } = typ {
        LExpr::new(ExprNode::Var(sanitize(name)))
    } else {
        typ_to_expr(typ)
    }
}

// ── Trait impl (Lean `instance`) ───────────────────────────────────────

pub fn trait_impl_to_ast(
    ti: &TraitImplX,
    method_impls: &[&FunctionX],
    assoc_types: &[&AssocTypeImplX],
) -> Instance {
    let mut binders: Vec<LBinder> = Vec::new();
    for tp in ti.typ_params.iter() {
        binders.push(LBinder {
            name: Some(tp.to_string()),
            ty: LExpr::new(ExprNode::Var("Type".into())),
            kind: BinderKind::Implicit,
        });
    }
    binders.extend(trait_bounds_to_ast(&ti.typ_bounds));

    // Build `TraitName arg1 arg2 …` — trait_typ_args are the positional
    // trait type arguments (Self + extras); assoc_types fill the outParam
    // slots declared by the class.
    let mut target_args: Vec<LExpr> = Vec::new();
    for t in ti.trait_typ_args.iter() { target_args.push(typ_to_expr(t)); }
    for a in assoc_types { target_args.push(typ_to_expr(&a.typ)); }
    let target = if target_args.is_empty() {
        LExpr::new(ExprNode::Var(lean_name(&ti.trait_path)))
    } else {
        LExpr::new(ExprNode::App {
            head: Box::new(LExpr::new(ExprNode::Var(lean_name(&ti.trait_path)))),
            args: target_args,
        })
    };

    let methods = method_impls.iter().map(|func| {
        let short = func.name.path.segments.last()
            .map(|s| s.as_str()).unwrap_or("_");
        // If the method has params, wrap body in `fun p1 p2 … => body`.
        let body = match &func.body {
            Some(b) => {
                let ast_body = vir_expr_to_ast(b);
                if func.params.is_empty() {
                    ast_body
                } else {
                    let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder {
                        name: Some(sanitize(p.x.name.0.as_str())),
                        // Type irrelevant here (Lean infers from the class),
                        // but we need a valid Expr; use `_` placeholder.
                        ty: LExpr::new(ExprNode::Var("_".into())),
                        kind: BinderKind::Explicit,
                    }).collect();
                    // We actually want `fun p1 p2 => body` without type
                    // annotations. The AST Lambda requires typed binders, so
                    // we render as Raw for brevity.
                    let params: Vec<String> = func.params.iter()
                        .map(|p| sanitize(p.x.name.0.as_str())).collect();
                    let body_txt = pp_expr(&ast_body);
                    let _ = binders; // keep-warn-suppress placeholder unused
                    LExpr::new(ExprNode::Raw(
                        format!("fun {} => {}", params.join(" "), body_txt)
                    ))
                }
            }
            None => LExpr::new(ExprNode::Var("sorry".into())),
        };
        InstanceMethod { name: sanitize(short), body }
    }).collect();

    Instance { binders, target, methods, span: None }
}

pub fn write_trait_impl(
    out: &mut String,
    ti: &TraitImplX,
    method_impls: &[&FunctionX],
    assoc_types: &[&AssocTypeImplX],
) {
    out.push_str(&pp_command(&Command::Instance(
        trait_impl_to_ast(ti, method_impls, assoc_types)
    )));
}

// ── Shared helpers ──────────────────────────────────────────────────────

/// Function parameter list as AST binders: type params, trait bounds,
/// then value params. Const generics become explicit `(N : ConstType)`
/// instead of `(N : Type)`.
fn fn_binders(f: &FunctionX) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();

    let const_typ_for = |name: &str| -> Option<&TypX> {
        for bound in f.typ_bounds.iter() {
            if let GenericBoundX::ConstTyp(param_typ, val_typ) = &**bound {
                if let TypX::TypParam(n) = &**param_typ {
                    if n.as_str() == name { return Some(val_typ); }
                }
            }
        }
        None
    };

    for tp in f.typ_params.iter() {
        let ty = if let Some(val_typ) = const_typ_for(tp) {
            typ_to_expr(val_typ)
        } else {
            LExpr::new(ExprNode::Var("Type".into()))
        };
        out.push(LBinder {
            name: Some(tp.to_string()),
            ty,
            kind: BinderKind::Explicit,
        });
    }

    out.extend(trait_bounds_to_ast(&f.typ_bounds));

    for p in f.params.iter() {
        out.push(LBinder {
            name: Some(sanitize(&p.x.name.0)),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
    }

    out
}

/// Generic bounds → Lean `[Trait T₁ T₂ …]` instance binders, with any
/// matching `TypEquality` bounds merged in as extra type arguments.
fn trait_bounds_to_ast(bounds: &GenericBounds) -> Vec<LBinder> {
    let mut out = Vec::new();
    for bound in bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), typs) = &**bound {
            let mut args: Vec<LExpr> = typs.iter().map(|t| typ_to_expr(t)).collect();
            for other in bounds.iter() {
                if let GenericBoundX::TypEquality(eq_path, _, _, typ) = &**other {
                    if lean_name(eq_path) == lean_name(path) {
                        args.push(typ_to_expr(typ));
                    }
                }
            }
            let target = LExpr::new(ExprNode::App {
                head: Box::new(LExpr::new(ExprNode::Var(lean_name(path)))),
                args,
            });
            out.push(LBinder { name: None, ty: target, kind: BinderKind::Instance });
        }
    }
    out
}

/// Conjoin a list of ensures clauses into a single `Expr`. Empty → `True`.
fn ensures_conj(ensures: &[Expr]) -> LExpr {
    if ensures.is_empty() {
        return LExpr::new(ExprNode::LitBool(true));
    }
    let mut iter = ensures.iter().rev();
    let mut acc = vir_expr_to_ast(iter.next().unwrap());
    for e in iter {
        acc = LExpr::new(ExprNode::BinOp {
            op: crate::lean_ast::BinOp::And,
            // Note: `∧` is right-associative in Lean. To match left-to-right
            // ordering of ensures clauses we fold right-to-left (first ens
            // ends up leftmost).
            lhs: Box::new(vir_expr_to_ast(e)),
            rhs: Box::new(acc),
        });
    }
    acc
}

fn field_name(name: &str) -> String {
    if name.parse::<usize>().is_ok() {
        format!("val{}", name)
    } else {
        sanitize(name)
    }
}
