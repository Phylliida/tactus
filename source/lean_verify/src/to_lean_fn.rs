//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    and_all, Binder as LBinder, BinderKind, Class, ClassMethod, Command, Datatype,
    DatatypeKind, Def, Expr as LExpr, ExprNode, Field, Instance, InstanceMethod,
    MatchArm, Pattern as LPattern, Theorem, Tactic, Variant,
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

/// Emit a datatype declaration plus, for multi-variant inductives,
/// the per-variant discriminator (`Type.is<Variant>`) and accessor
/// (`Type.<Variant>_<field>`) defs that exec-fn match-desugaring
/// references.
///
/// Why accessors: Lean's `structure` auto-derives field accessors
/// (`Point.x`), so single-variant structs work out of the box. But
/// `inductive` doesn't auto-derive per-variant discriminators or
/// field accessors — in Lean you normally pattern-match on the value.
/// Exec fns reach this path because `ast_simplify` lowers `match` to
/// an if-chain built from `UnaryOpr::IsVariant` + `UnaryOpr::Field`,
/// and the desugared form expects accessor fns to exist. So we
/// synthesise them.
///
/// `emit_accessors` controls whether the accessor defs are produced.
/// The exec-fn preamble passes `true` — the desugared if-chain
/// needs them. The proof-fn preamble passes `false` — proof fns
/// render match as native Lean match (spec fns preserve match
/// through to VIR-AST), never reach the desugared Field/IsVariant
/// form, and don't benefit from accessors. More importantly,
/// emitting accessors for datatypes that proof fns reference but
/// whose field types lack `Inhabited` (the accessor's fallback
/// case calls `default`) breaks Lean elaboration even when the
/// accessor is never called.
///
/// Returns an empty `Vec` for `Dt::Tuple` (no declaration needed —
/// tuples are rendered as `T × U` products).
pub fn datatype_to_cmds(dt: &DatatypeX, emit_accessors: bool) -> Vec<Command> {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
        Dt::Tuple(_) => return vec![],
    };
    let typ_params: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();

    let is_single_variant_struct =
        dt.variants.len() == 1 && dt.variants[0].name.as_str() == short;

    let kind = if is_single_variant_struct {
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

    let mut cmds = vec![Command::Datatype(Datatype {
        name: path.clone(),
        typ_params: typ_params.clone(),
        kind,
    })];
    if !is_single_variant_struct && emit_accessors {
        cmds.extend(multi_variant_accessor_defs(dt, &path));
    }
    cmds
}

/// Emit `Type.is<Variant>` discriminators and `Type.<Variant>_<field>`
/// accessors for each (variant, field) pair on a multi-variant
/// inductive.
///
/// Discriminator: `def Type.isFoo : Type → Bool := fun x => match x
/// with | Type.Foo .. => true | _ => false` — one per variant,
/// regardless of whether the variant carries fields. `is_variant_node`
/// in `expr_shared.rs` emits `x.isFoo` references that resolve here.
///
/// Accessor: `noncomputable def Type.Foo_val0 : Type → FieldTy :=
/// fun x => match x with | Type.Foo v _ => v | _ => Classical.arbitrary _`
/// — one per (variant, field) pair. The `_` patterns ignore the other
/// fields in that variant; other variants get `Classical.arbitrary _`
/// because those cases are unreachable when the user's code guards
/// the projection with a prior `isVariant` check, but Lean still
/// requires the match to be total. `Classical.arbitrary` needs
/// `Nonempty` — fine for the primitive types exec-fn match-desugaring
/// actually reaches (ints, bools, references).
fn multi_variant_accessor_defs(dt: &DatatypeX, type_name: &str) -> Vec<Command> {
    let mut cmds = Vec::new();
    let x_binder = || LBinder {
        name: Some("x".into()),
        ty: LExpr::var(type_name),
        kind: BinderKind::Explicit,
    };
    let match_on_x = |arms: Vec<MatchArm>| LExpr::new(ExprNode::Match {
        scrutinee: Box::new(LExpr::var("x")),
        arms,
    });

    // Discriminators: `def Type.isFoo (x : Type) : Prop := match x with …`.
    // Lean's `inductive` doesn't auto-derive these (only `structure` does);
    // `is_variant_node` in `expr_shared.rs` emits `x.isFoo` references that
    // resolve here.
    //
    // **Prop, not Bool.** Verus's `TypX::Bool` renders as Lean `Prop`
    // (see `to_lean_type::typ_to_expr`). The desugared match-test
    // (`pattern_to_exprs` in ast_simplify) builds expressions typed
    // `TypX::Bool` and combines them with `BinaryOp::And` — which
    // maps to Lean `∧ : Prop → Prop → Prop`. So everything in that
    // chain must be `Prop`. Returning `Bool` would cause the `And`
    // between `x.isFoo` (Bool) and `True` (from the wildcard base
    // case) to be a Prop/Bool mismatch.
    for v in dt.variants.iter() {
        let var_san = sanitize(&v.name);
        let wildcards: Vec<LPattern> = v.fields.iter().map(|_| LPattern::Wildcard).collect();
        cmds.push(Command::Def(Def {
            // `@[simp]`: let `simp_all` unfold the discriminator so
            // `tactus_auto` can close exec-fn goals that turn on a
            // pattern test. Without this, `k.isFoo` stays opaque and
            // the downstream `omega` / `simp_all` can't case-split
            // the enum.
            attrs: vec!["simp".into()],
            name: format!("{}.is{}", type_name, var_san),
            binders: vec![x_binder()],
            ret_ty: LExpr::var("Prop"),
            body: match_on_x(vec![
                MatchArm {
                    pattern: LPattern::Ctor {
                        name: format!("{}.{}", type_name, var_san),
                        args: wildcards,
                    },
                    body: LExpr::lit_bool(true),
                },
                MatchArm {
                    pattern: LPattern::Wildcard,
                    body: LExpr::lit_bool(false),
                },
            ]),
            termination_by: vec![],
        }));
    }

    // Accessors: `def Type.Foo_val0 (x : Type) : FieldTy := match x with
    //   | Type.Foo v _ _ => v | _ => Classical.arbitrary _`.
    // One per (variant, field) pair. The `_` patterns ignore the other
    // fields in that variant; other variants get `Classical.arbitrary _`
    // — unreachable in practice (the desugared match guards with a
    // prior `isVariant` check), but Lean requires totality.
    // `Classical.arbitrary` needs `[Nonempty α]`, which is auto-derived
    // for the primitive types exec-fn match-desugaring actually reaches.
    for v in dt.variants.iter() {
        let var_san = sanitize(&v.name);
        for (idx, f) in v.fields.iter().enumerate() {
            let field_local = format!("_tactus_field_{}", idx);
            let binders_pat: Vec<LPattern> =
                (0..v.fields.len()).map(|i| if i == idx {
                    LPattern::Var(field_local.clone())
                } else {
                    LPattern::Wildcard
                }).collect();
            cmds.push(Command::Def(Def {
                // `@[simp]` for the same reason as the discriminator:
                // `simp_all` should unfold the accessor before `omega`
                // tries to reason about its result. Without this the
                // accessor is opaque and goals involving it get stuck.
                attrs: vec!["simp".into()],
                name: format!("{}.{}_{}", type_name, var_san, field_name(&f.name)),
                binders: vec![x_binder()],
                ret_ty: typ_to_expr(&f.a.0),
                body: match_on_x(vec![
                    MatchArm {
                        pattern: LPattern::Ctor {
                            name: format!("{}.{}", type_name, var_san),
                            args: binders_pat,
                        },
                        body: LExpr::var(field_local),
                    },
                    MatchArm {
                        pattern: LPattern::Wildcard,
                        // `default` resolves via `[Inhabited α]`, which
                        // Lean derives automatically for primitive
                        // types (Int, Nat, Bool) — the types exec-fn
                        // match-desugaring actually reaches. Users
                        // with custom field types may need a manual
                        // `instance : Inhabited Foo := ⟨…⟩`.
                        // Unreachable anyway when call sites guard
                        // the accessor with a prior isVariant check.
                        body: LExpr::var("default"),
                    },
                ]),
                termination_by: vec![],
            }));
        }
    }

    cmds
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
