//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    and_all, Binder as LBinder, BinderKind, Class, ClassMethod, Datatype,
    DatatypeKind, Def, Expr as LExpr, ExprNode, Field, Instance, InstanceMethod,
    Theorem, Tactic, Variant,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

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
    let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| vir_expr_to_ast(d)).collect();
    Def {
        attrs,
        name: lean_name(&f.name.path),
        binders: fn_binders(f),
        ret_ty: typ_to_expr(&f.ret.x.typ),
        body,
        termination_by,
    }
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
    let goal = and_all(f.ensure.0.iter().map(|e| vir_expr_to_ast(e)).collect());
    Theorem {
        name: lean_name(&f.name.path),
        binders,
        goal,
        tactic: Tactic::Raw(tactic_body.to_string()),
    }
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
    Some(Datatype { name: path, typ_params, kind })
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
    }
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
        let body = match &func.body {
            Some(b) => {
                let ast_body = vir_expr_to_ast(b);
                if func.params.is_empty() {
                    ast_body
                } else {
                    // `fun (p₁ : _) (p₂ : _) … => body`. The `_` lets Lean
                    // infer each parameter type from the class's method
                    // signature, which is what we want.
                    let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder {
                        name: Some(sanitize(p.x.name.0.as_str())),
                        ty: LExpr::new(ExprNode::Var("_".into())),
                        kind: BinderKind::Explicit,
                    }).collect();
                    LExpr::new(ExprNode::Lambda {
                        binders,
                        body: Box::new(ast_body),
                    })
                }
            }
            None => LExpr::new(ExprNode::Var("sorry".into())),
        };
        InstanceMethod { name: sanitize(short), body }
    }).collect();

    Instance { binders, target, methods }
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

    // Each param → one binder, and (for fixed-width int types) one
    // hypothesis binder right after giving the refinement bounds.
    // Must mirror `sst_to_lean::exec_fn_theorem_to_ast`: both paths
    // need to agree on the in-scope refinement for the same param,
    // or proof fns and the exec fns that call them diverge.
    for p in f.params.iter() {
        let name = sanitize(&p.x.name.0);
        out.push(LBinder {
            name: Some(name.clone()),
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
        if let Some(pred) = crate::to_lean_sst_expr::type_bound_predicate(
            &LExpr::var(name.clone()),
            &p.x.typ,
        ) {
            out.push(LBinder {
                name: Some(format!("h_{}_bound", name)),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
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

fn field_name(name: &str) -> String {
    if name.parse::<usize>().is_ok() {
        format!("val{}", name)
    } else {
        sanitize(name)
    }
}
