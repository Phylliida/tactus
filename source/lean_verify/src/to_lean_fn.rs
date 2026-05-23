//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    and_all, Axiom, BinOp, Binder as LBinder, BinderKind, Class, ClassMethod, Command, Datatype,
    DatatypeKind, Def, DefCurried, Expr as LExpr, ExprNode, Field, Instance,
    InstanceMethod, MatchArm, Pattern as LPattern, Theorem, Tactic, Variant,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

// ── Shared constants ────────────────────────────────────────────────────

/// Auto-tactic used for the proof slot of `⟨witness, _⟩` pairs emitted
/// as instance method bodies for non-unit-return proof-fn trait methods.
/// `rfl` closes when the witness expression matches the ensures' RHS
/// literally; `simp_all` handles unfolding through standalone def chains.
/// Used in both `trait_to_ast` (class default) and `trait_impl_to_ast`
/// (instance body) — extract here so phrasing changes propagate to
/// both sites at once.
const SUBTYPE_WITNESS_AUTO_PROOF: &str = "first | rfl | simp_all";

/// Fallback tactic when `tactic_bodies` lookup misses for a proof-fn
/// trait method. Lean accepts `sorry` with a warning rather than a
/// hard error, preserving the "soundness escape hatch with surfaced
/// signal" model — but in practice every proof fn with `tactic_span`
/// should be readable, so the fallback is defensive only.
const TACTIC_BODY_FALLBACK: &str = "sorry";

/// True when `typ` is a reference-like decoration that renders through
/// one of the `Tactus.X` wrapper structures. These wrappers are opaque
/// at the dispatch level (so trait resolution distinguishes `Foo &A`
/// from `Foo A`) but transparent at the value level via the
/// definitional `.deref` projection (single-field structure).
///
/// Mirrors `to_lean_type::typ_to_node`'s decision about which decorations
/// produce a wrapper. Keep in sync.
///
/// **Note**: this is the *typ-only* check. For `&mut` params Verus's
/// legacy mode also produces `is_mut: true` with a non-decorated typ —
/// use [`crate::expr_shared::is_mut_ref_typ`] when both signals are
/// available (which is the canonical "is this param wrapper-bound?"
/// question).
pub(crate) fn is_ref_decorated(typ: &TypX) -> bool {
    matches!(typ,
        TypX::Decorate(TypDecoration::Ref | TypDecoration::MutRef
                       | TypDecoration::Box | TypDecoration::Rc
                       | TypDecoration::Arc, _, _)
        | TypX::MutRef(_))
}

/// True when this param's Lean binder is wrapper-typed and so the
/// body needs a `let p := p.deref` shadow to access the inner value
/// uniformly. Covers Ref/Box/Rc/Arc decorations plus all three
/// `&mut`-like shapes (legacy `is_mut: true`, new-mode `MutRef<T>`,
/// `Decorate(MutRef, _, _)`).
fn needs_param_deref(p: &Param) -> bool {
    // Ref-like decorations always wrap.
    if is_ref_decorated(&p.x.typ) {
        return true;
    }
    // `&mut` in legacy mode (`is_mut: true`, plain typ) also gets
    // wrapped at the binder via `param_binder_typ`.
    crate::expr_shared::is_mut_ref_typ(&p.x.typ, p.x.is_mut)
}

/// Wrap a body expression with `let p := p.deref` for each param whose
/// Lean binder is wrapper-typed, so the body sees `p` as the inner type.
/// Lean's shadowing means the binder `(p : Tactus.Ref T)` survives at
/// the param position (for dispatch) while the body's references to `p`
/// resolve to the derefed inner.
///
/// Non-wrapped params pass through unchanged.
///
/// Applied at every site that emits a body containing references to
/// reference-decorated params: spec_fn_to_ast standalone defs,
/// trait_impl_to_ast instance method bodies, trait_to_ast class default
/// bodies, proof_fn_to_ast requires/ensures.
pub(crate) fn wrap_body_with_param_derefs(body: LExpr, params: &Params) -> LExpr {
    // Iterate in REVERSE so the FIRST param's let-binding ends up
    // outermost (after building the wrap by repeatedly prepending).
    let mut wrapped = body;
    for p in params.iter().rev() {
        if needs_param_deref(p) {
            let param_name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
            wrapped = LExpr::let_bind(
                param_name.clone(),
                LExpr::field_proj(LExpr::var(param_name), "deref"),
                wrapped,
            );
        }
    }
    wrapped
}

// ── Source map ──────────────────────────────────────────────────────────

/// Maps Lean line numbers back to the user's source.
///
/// Proof fns and exec fns use different mapping mechanisms — the
/// enum split makes the dichotomy explicit instead of having one
/// struct with conditionally-meaningful fields.
pub enum LeanSourceMap {
    /// Proof fns: the user-written tactic body starts at
    /// `tactic_start_line` and runs `tactic_line_count` lines.
    /// `find_tactic_line` returns the offset within that block.
    ProofFn {
        fn_name: String,
        /// 1-indexed line in generated `.lean` where the tactic body starts.
        tactic_start_line: usize,
        tactic_line_count: usize,
    },
    /// Exec fns (#51 source mapping): `span_marks` is a list of
    /// landmarks populated by the pp as it visits
    /// `ExprNode::SpanMark` nodes. `find_span_mark` returns the
    /// closest preceding obligation-kind mark for a given Lean
    /// error line.
    ExecFn {
        fn_name: String,
        span_marks: Vec<crate::lean_pp::SpanMarkLandmark>,
    },
}

impl LeanSourceMap {
    /// Proof-fn path: 1-indexed offset within the tactic body for
    /// a given Lean line number, or `None` outside the body.
    pub fn find_tactic_line(&self, lean_line: usize) -> Option<usize> {
        match self {
            LeanSourceMap::ProofFn { tactic_start_line, tactic_line_count, .. } => {
                let end = tactic_start_line + tactic_line_count;
                if lean_line >= *tactic_start_line && lean_line < end {
                    Some(lean_line - tactic_start_line)
                } else {
                    None
                }
            }
            LeanSourceMap::ExecFn { .. } => None,
        }
    }

    /// Exec-fn path: closest preceding **obligation-kind**
    /// `SpanMarkLandmark` for a Lean error line. Returns `None`
    /// for proof-fn maps or when no obligation-kind mark
    /// precedes the line.
    ///
    /// Structurally exact for per-obligation theorems (D, Stages
    /// 1-4): each theorem has exactly one "obligation mark" at
    /// the innermost (latest, in source order) position of its
    /// goal. Hypothesis-kind marks (LoopCondition for the
    /// loop's cond, BranchCondition for an `if`'s cond) appear
    /// earlier in the goal but are filtered out here via
    /// `AssertKind::is_obligation_kind` — they exist for the
    /// `/- @rust:LOC -/` comments in the generated `.lean`
    /// (visual debugging) but never fire as error labels.
    /// Lean's `pos.line` for a failure points at the theorem's
    /// tactic invocation, which is just after the goal; the
    /// closest preceding obligation mark is therefore the
    /// obligation mark for that theorem, with the right
    /// `AssertKind` for the failing obligation.
    pub fn find_span_mark(&self, lean_line: usize) -> Option<&crate::lean_pp::SpanMarkLandmark> {
        match self {
            LeanSourceMap::ExecFn { span_marks, .. } => {
                span_marks.iter()
                    .rev()
                    .find(|m| m.line <= lean_line && m.kind.is_obligation_kind())
            }
            LeanSourceMap::ProofFn { .. } => None,
        }
    }
}

// ── Spec fn ─────────────────────────────────────────────────────────────

/// Build a top-level command for a spec fn. Returns `Command::Def`
/// when the fn has a body, `Command::Axiom` when it doesn't.
///
/// Body-less cases that route through the Axiom branch:
/// - `pub uninterp spec fn` (deliberately uninterpreted on the Verus side).
/// - `external_body` spec fns (Verus's escape hatch for FFI/spec gaps).
/// - Cross-crate spec fns whose body was stripped at `export_crate` time
///   (private or closed specs from imported crates).
///
/// Lean's `axiom` is the right encoding: it declares a constant whose
/// value is unspecified, matching Verus's "this is just a symbol with
/// a type" semantics. (The previous `def ... := sorry` shape was dead
/// code, unreachable because dep_order's `build_spec_fn_map` filtered
/// body=None fns out — which produced "unresolved" sanity-check
/// rejections at the call site. Audit 2026-05-12 unfiltered the map
/// and routes through `Axiom` here.)
pub fn spec_fn_to_ast(f: &FunctionX, fn_map: &crate::sst_to_lean::FnMap) -> Command {
    // Spec fns are Lean defs (mathematical definitions). The
    // u-type / i-type refinement bounds belong on theorems
    // (proof fns + exec fn obligations), not on the spec fn's
    // signature — including them would change the spec fn's
    // type from `Int → Int` to `Int → Bound → Int` and break
    // call sites that pass only the value. Surfaced 2026-05-09
    // by `test_diag_exec_plain_assert_with_spec_call` (#147).
    let binders = fn_binders_without_bound_hyps(f);
    let ret_ty = typ_to_expr(&f.ret.x.typ);
    let name = lean_name(&f.name.path);
    match &f.body {
        Some(b) => {
            let attrs = if matches!(f.opaqueness, Opaqueness::Opaque) {
                vec!["irreducible".into()]
            } else {
                vec![]
            };
            // Insert Int.toNat coercions at Call sites where args render
            // as Lean Int but params render as Lean Nat
            // (BUG-as-nat-cast.md). A spec fn body may call other spec
            // fns whose params are nat-typed.
            let coerced_body = crate::sst_to_lean::insert_nat_coercions_in_expr(b, fn_map);
            let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
            let body = wrap_body_with_param_derefs(
                crate::to_lean_expr::vir_expr_to_ast_with_binders(&coerced_body, &binder_ctx),
                &f.params,
            );
            let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| {
                let coerced = crate::sst_to_lean::insert_nat_coercions_in_expr(d, fn_map);
                crate::to_lean_expr::vir_expr_to_ast_with_binders(&coerced, &binder_ctx)
            }).collect();
            Command::Def(Def { attrs, name, binders, ret_ty, body, termination_by })
        }
        None => Command::Axiom(Axiom { name, binders, ret_ty, attrs: vec![] }),
    }
}

// ── Proof fn ────────────────────────────────────────────────────────────

/// Build a `Theorem` AST node for a proof fn with the given tactic text.
///
/// `fn_map` is consulted to insert `Int.toNat` coercions at Call sites
/// where args render as Lean `Int` but the callee's params render as
/// Lean `Nat` (BUG-as-nat-cast.md). Pass an empty map if no fn-map
/// info is available; the only effect is that uncoerced Int → Nat
/// calls would fail Lean elaboration (matching the pre-fix state).
pub fn proof_fn_to_ast(
    f: &FunctionX,
    tactic_body: &str,
    fn_map: &crate::sst_to_lean::FnMap,
) -> Theorem {
    let mut binders = fn_binders(f);
    let binder_ctx = crate::to_lean_expr::binder_ctx_from_params(&f.params);
    for (i, req) in f.require.iter().enumerate() {
        // Insert Int.toNat coercions at Call sites where needed.
        let coerced = crate::sst_to_lean::insert_nat_coercions_in_expr(req, fn_map);
        // Wrap with `let p := p.deref` for ref-decorated params so the
        // hypothesis body sees inner types.
        let req_ty = wrap_body_with_param_derefs(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(&coerced, &binder_ctx),
            &f.params);
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::synthetic(format!("h{}", i))),
            ty: req_ty,
            kind: BinderKind::Explicit,
        });
    }
    let goal_raw = and_all(f.ensure.0.iter().map(|e| {
        let coerced = crate::sst_to_lean::insert_nat_coercions_in_expr(e, fn_map);
        crate::to_lean_expr::vir_expr_to_ast_with_binders(&coerced, &binder_ctx)
    }).collect());
    let goal = wrap_body_with_param_derefs(goal_raw, &f.params);
    // Honor Verus's `decreases` clause for recursive proof fns. Lean often
    // auto-infers termination for simple structural recursion, but cases
    // where the measure is non-obvious (Collatz, lex pairs, computed
    // descent) require the explicit clause. Mirrors `spec_fn_to_ast`.
    let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| {
        let coerced = crate::sst_to_lean::insert_nat_coercions_in_expr(d, fn_map);
        crate::to_lean_expr::vir_expr_to_ast_with_binders(&coerced, &binder_ctx)
    }).collect();
    Theorem {
        name: lean_name(&f.name.path),
        binders,
        goal,
        tactic: Tactic::Raw(tactic_body.to_string()),
        requires_preamble: Vec::new(),
        heartbeats: f.attrs.tactus_heartbeats,
        termination_by,
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
pub fn datatype_to_cmds(
    dt: &DatatypeX,
    emit_accessors: bool,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Vec<Command> {
    // External-body types (`#[verifier::external_body] struct Foo {}`,
    // and the `external_type_specification` proxy variant) have no
    // user-visible structure; Verus stipulates them as opaque carriers
    // for axiomatized methods. Emitting them as an empty Lean `structure`
    // gives them a unique inhabitant (`Foo.mk`), so any two values
    // collapse via `cases` — a soundness gap. Route to opaque-axiom
    // emission instead. See `external_body_type_cmds`.
    if matches!(dt.transparency, DatatypeTransparency::Never) {
        return external_body_type_cmds(dt);
    }
    // Single-element SCC. The set's lifetime is tied to `dt`'s name
    // path; constructed locally because non-mutual datatypes never
    // cross outside their own SCC.
    let mut scc_paths: std::collections::HashSet<&Path> = std::collections::HashSet::new();
    if let Dt::Path(p) = &dt.name {
        scc_paths.insert(p);
    }
    let mut cmds = Vec::new();
    if let Some(decl) = datatype_decl_cmd(dt, &scc_paths, external_body_paths) {
        cmds.push(decl);
    }
    if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths, external_body_paths) {
        cmds.push(inst);
    }
    cmds.extend(datatype_accessor_cmds(dt, emit_accessors));
    if let Some(height) = datatype_height_cmd(dt, &scc_paths) {
        cmds.push(height);
    }
    cmds
}

/// Emit external_body types as opaque axioms:
/// ```text
/// axiom T : Type → Type → ... → Type
/// @[instance] axiom T.instInhabited (A : Type) (B : Type) ... :
///     Inhabited (T A B ...)
/// ```
///
/// Two axioms per type:
/// 1. The type itself, curried through its type params. No equations,
///    no constructors — values are distinguishable only via whatever
///    axiomatized spec fns the user provides.
/// 2. An `Inhabited` instance stipulated by axiom. Required because
///    Tactus emits `| _ => default` fallback arms in multi-variant
///    enum accessors; an external_body field type needs an Inhabited
///    instance for the accessor to elaborate. The `@[instance]` attribute
///    plugs it into Lean's typeclass resolution.
///
/// Both shapes are sound under classical+choice: the type stipulator
/// (e.g., vstd) is claiming "this type is nonempty" and "this is the
/// signature." Tactus's role is to faithfully encode that stipulation.
fn external_body_type_cmds(dt: &DatatypeX) -> Vec<Command> {
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return vec![],
    };
    // Type axiom: `axiom T : Type → ... → Type`, currying type params
    // into the return type so the result is `Type → ... → Type`.
    let type_ret_ty = curry_type_to_type(dt.typ_params.len());
    let type_axiom = Axiom {
        name: path.clone(),
        binders: vec![],
        ret_ty: type_ret_ty,
        attrs: vec![],
    };
    // Inhabited axiom: `@[instance] axiom T.instInhabited (A : Type) ... :
    //   Inhabited (T A ...)`.
    let inhabited_binders: Vec<LBinder> = dt.typ_params.iter()
        .map(|(id, _)| LBinder {
            name: Some(crate::lean_name::LeanName::lit(id.as_str())),
            ty: LExpr::var_lit("Type"),
            kind: BinderKind::Explicit,
        })
        .collect();
    let parent_applied = if dt.typ_params.is_empty() {
        LExpr::var_lit(&path)
    } else {
        let args: Vec<LExpr> = dt.typ_params.iter()
            .map(|(id, _)| LExpr::var_lit(id.as_str()))
            .collect();
        LExpr::app(LExpr::var_lit(&path), args)
    };
    let inhabited_ret_ty = LExpr::app(LExpr::var_lit("Inhabited"), vec![parent_applied]);
    let inhabited_axiom = Axiom {
        name: format!("{}.instInhabited", path),
        binders: inhabited_binders,
        ret_ty: inhabited_ret_ty,
        attrs: vec!["instance".into()],
    };
    vec![Command::Axiom(type_axiom), Command::Axiom(inhabited_axiom)]
}

/// Build `Type → Type → ... → Type` with `arity` arrows. For `arity = 0`,
/// returns just `Type`. For `arity = 2`, returns `Type → Type → Type`.
///
/// Used for external_body type axiom signatures (`axiom T : Type → Type`
/// for `T<A>`).
///
/// Lean's `→` for non-`Prop` types is the same syntactic arrow as the
/// implication arrow on Props (both render via `BinOp::Implies` which
/// pretty-prints as `→` — see `to_lean_type::SpecFn` for the same
/// convention applied to spec fn types).
fn curry_type_to_type(arity: usize) -> LExpr {
    let type_ = LExpr::var_lit("Type");
    let mut result = type_.clone();
    for _ in 0..arity {
        result = LExpr::new(ExprNode::BinOp {
            op: BinOp::Implies,
            lhs: Box::new(type_.clone()),
            rhs: Box::new(result),
        });
    }
    result
}

/// Emit a group of datatypes — `Single` for non-mutual, `Mutual` for
/// SCCs of size >1 (#109). For mutual SCCs:
/// 1. Inductive declarations are wrapped in a `mutual ... end` block
///    so cross-type field references resolve.
/// 2. Accessors emit OUTSIDE the mutual block — they're per-datatype
///    structural defs that don't recurse across the SCC.
/// 3. Height fns are wrapped in a SECOND `mutual ... end` block —
///    cross-type recursive calls (e.g., `A.height` calling
///    `B.height`) require the mutual scope to typecheck.
///
/// `deriving Inhabited` stays on each `inductive` declaration even
/// inside the mutual block — Lean accepts inline deriving for
/// mutually-recursive inductives and produces conditional instances.
pub fn datatype_group_to_cmds<'a>(
    group: &crate::dep_order::DatatypeGroup<'a>,
    emit_accessors: bool,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Vec<Command> {
    use crate::dep_order::DatatypeGroup;
    let all_dts: Vec<&'a DatatypeX> = match group {
        DatatypeGroup::Single(dt) => return datatype_to_cmds(dt, emit_accessors, external_body_paths),
        DatatypeGroup::Mutual(dts) => dts.clone(),
    };

    // External-body types in a mutual SCC are exotic — they have no
    // fields so they can't recurse into other types. If `dep_order` ever
    // groups one into an SCC (currently it shouldn't), peel them off and
    // emit as opaque axioms separately; the remaining members go through
    // the mutual emission path.
    let mut cmds = Vec::new();
    let dts: Vec<&'a DatatypeX> = all_dts.iter().copied().filter(|dt| {
        if matches!(dt.transparency, DatatypeTransparency::Never) {
            cmds.extend(external_body_type_cmds(dt));
            false
        } else {
            true
        }
    }).collect();
    if dts.is_empty() {
        return cmds;
    }

    // Build the SCC path set once for all (non-external-body) members of
    // the group.
    let scc_paths: std::collections::HashSet<&Path> = dts.iter()
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some(p),
            Dt::Tuple(_) => None,
        })
        .collect();

    // 1. mutual block of inductives.
    let inductive_cmds: Vec<Command> = dts.iter()
        .filter_map(|dt| datatype_decl_cmd(dt, &scc_paths, external_body_paths))
        .collect();
    cmds.push(Command::Mutual(inductive_cmds));

    // 1b. Manual `Inhabited` instances for any indexed-style members of
    // the SCC (Lean rejects `deriving Inhabited` on indexed inductives).
    // Emitted OUTSIDE the mutual block — Lean's instance system can
    // resolve cross-references to types declared earlier in the file
    // (the mutual block above) without needing the instance itself to
    // be inside it.
    for dt in &dts {
        if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths, external_body_paths) {
            cmds.push(inst);
        }
    }

    // 2. accessors per-datatype, outside the mutual block.
    for dt in &dts {
        cmds.extend(datatype_accessor_cmds(dt, emit_accessors));
    }

    // 3. mutual block of height fns. Each height fn reaches the
    //    others by name; the mutual scope makes those names visible.
    let height_cmds: Vec<Command> = dts.iter()
        .filter_map(|dt| datatype_height_cmd(dt, &scc_paths))
        .collect();
    if !height_cmds.is_empty() {
        cmds.push(Command::Mutual(height_cmds));
    }

    cmds
}

/// Returns `true` iff `dt` has at least one variant field whose type is a
/// recursive reference to a datatype in `scc_paths` AND whose type-arguments
/// don't match the parent's `typ_params` positionally — i.e., the recursive
/// arm uses a different instantiation than the parent declares.
///
/// Example trigger: `enum Mut<A> { Plain(A), Recurse(Mut<u8>) }` — the
/// `Recurse` arm uses `Mut<u8>` while the parent's typ_params are `[A]`.
/// Lean's parameter-style strict-positivity check rejects this; we route
/// to indexed-style emission instead (which Lean accepts).
///
/// Counterexample (uniform recursion): `enum List<A> { Cons(A, List<A>) }`
/// — recursive arm uses `List<A>`, args match parent's params. Returns false.
///
/// Counterexample (no generics): `enum Tree { Leaf, Node(Tree, Tree) }` —
/// no parent params to compare against; recursion is trivially uniform.
/// Returns false.
/// Returns `true` iff `typ` peels to a `Dt::Path(p)` reference where `p`
/// is in `external_body_paths`. Used by the Inhabited-emission gate
/// (`has_field_referencing_external_body`) to decide whether the parent
/// datatype's auto-derived Inhabited would fail Lean's compiler IR check.
///
/// Only the outermost path is checked — nested generic args don't matter
/// here because Lean's `deriving Inhabited` constructs the default by
/// picking a variant and applying `default` to each field's TYPE. A field
/// of type `Vec<Opaque>` produces `Vec.nil` via Vec's polymorphic
/// Inhabited (no Opaque value constructed); only a field DIRECTLY typed
/// `Opaque` forces calling `default : Opaque` which lacks code.
fn typ_references_external_body(
    typ: &Typ,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> bool {
    let peeled = crate::to_lean_type::peel_typ_wrappers(typ);
    match &**peeled {
        TypX::Datatype(Dt::Path(p), _, _) => external_body_paths.contains(p),
        _ => false,
    }
}

/// Returns `true` iff any variant field of `dt` references an external_body
/// datatype directly (via `typ_references_external_body`). See that helper's
/// docstring for why a shallow check suffices.
fn has_field_referencing_external_body(
    dt: &DatatypeX,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> bool {
    dt.variants.iter().any(|v|
        v.fields.iter().any(|f| typ_references_external_body(&f.a.0, external_body_paths))
    )
}

fn has_cross_instantiation_recursion(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
) -> bool {
    let parent_params: Vec<&str> = dt.typ_params.iter().map(|(id, _)| id.as_str()).collect();
    if parent_params.is_empty() {
        return false; // no params → no cross-instantiation possible.
    }
    for variant in dt.variants.iter() {
        for field in variant.fields.iter() {
            let field_typ = crate::to_lean_type::peel_typ_wrappers(&field.a.0);
            let TypX::Datatype(Dt::Path(p), args, _) = &**field_typ else { continue; };
            if !scc_paths.contains(p) { continue; }
            // Recursive arm. Compare args to parent's typ_params positionally.
            if args.len() != parent_params.len() { return true; }
            for (arg, &param_name) in args.iter().zip(parent_params.iter()) {
                let arg_peeled = crate::to_lean_type::peel_typ_wrappers(arg);
                let TypX::TypParam(n) = &**arg_peeled else { return true; };
                if n.as_str() != param_name { return true; }
            }
        }
    }
    false
}

/// Emit the `inductive` (or `structure`) declaration for a datatype.
/// Returns None for `Dt::Tuple` (no decl needed; tuples render as products).
///
/// Branches on `has_cross_instantiation_recursion` to pick parameter-style
/// vs indexed-style. Indexed-style requires a companion `Inhabited`
/// instance — emitted separately by `datatype_inhabited_instance_cmd`.
fn datatype_decl_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
        Dt::Tuple(_) => return None,
    };
    let typ_params: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();

    let is_single_variant_struct =
        dt.variants.len() == 1 && dt.variants[0].name.as_str() == short;

    let cross_inst = has_cross_instantiation_recursion(dt, scc_paths);

    let kind = if is_single_variant_struct {
        let variant = &dt.variants[0];
        DatatypeKind::Structure {
            fields: variant.fields.iter().map(|f| Field {
                name: field_name(&f.name),
                ty: typ_to_expr(&f.a.0),
            }).collect(),
        }
    } else {
        let variants: Vec<Variant> = dt.variants.iter().map(|v| Variant {
            name: sanitize(&v.name),
            fields: v.fields.iter().map(|f| Field {
                name: field_name(&f.name),
                ty: typ_to_expr(&f.a.0),
            }).collect(),
        }).collect();
        if cross_inst {
            DatatypeKind::IndexedInductive { variants }
        } else {
            DatatypeKind::Inductive { variants }
        }
    };

    // Derive `Inhabited` automatically for parameter-style. Lean rejects
    // `deriving Inhabited` on indexed-style inductives, so we drop the
    // derive and emit a manual instance via
    // `datatype_inhabited_instance_cmd` instead. For self-referential
    // types like `enum Stack { Empty, Push(u8, Box<Stack>) }`,
    // `Push_val1 : Stack → Stack` needs `Inhabited Stack`. For generic
    // datatypes (#108), Lean's `deriving Inhabited` auto-generates a
    // conditional instance `[Inhabited A] → Inhabited (List A)`. For
    // mutually recursive SCCs (#109), Lean accepts `deriving Inhabited`
    // inline even inside a `mutual` block (parameter-style only).
    //
    // ALSO drop the derive when any field references an external_body
    // type: Lean's auto-derived Inhabited is *computable* and depends on
    // the field's Inhabited.default at code-gen time. External_body
    // types have axiomatic Inhabited instances with no executable code,
    // so the compiler IR check fails on the parent's auto-derived
    // instance. `datatype_inhabited_instance_cmd` emits a manual
    // `noncomputable instance` in this case (and the cross-instantiation
    // case above).
    let has_external_body_field =
        has_field_referencing_external_body(dt, external_body_paths);
    let derives = if cross_inst || has_external_body_field {
        vec![]
    } else {
        vec!["Inhabited".into()]
    };
    Some(Command::Datatype(Datatype {
        name: path,
        typ_params,
        kind,
        derives,
    }))
}

/// For indexed-style datatypes (cross-instantiation recursion), emit a
/// manual `Inhabited` instance of shape:
/// ```text
/// noncomputable instance {A : Type} [Inhabited A] : Inhabited (T A) where
///   default := T.<base> default default ...
/// ```
/// where `<base>` is a non-recursive variant (one whose fields don't
/// reference any datatype in the SCC). Each field gets `default` from the
/// `[Inhabited A]` typeclass param (for type-param fields) or the global
/// `Inhabited Int` etc. instances (for primitive fields).
///
/// Returns `None` for parameter-style datatypes (Lean's `deriving Inhabited`
/// handles those) and for tuple datatypes (no decl). Also returns `Some`
/// when any variant field references an external_body type — the parent
/// must then have a *noncomputable* Inhabited instance (axiom-backed
/// child Inhabited instances have no executable code; Lean's auto-derived
/// computable instance would fail the IR check).
fn datatype_inhabited_instance_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
    external_body_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let cross_inst = has_cross_instantiation_recursion(dt, scc_paths);
    let has_external_body_field =
        has_field_referencing_external_body(dt, external_body_paths);
    if !cross_inst && !has_external_body_field {
        return None;
    }
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return None,
    };
    // Find a base constructor — a variant whose fields don't reference any
    // datatype in the SCC AND don't reference any external_body datatype.
    // Such a variant exists for most Rust-constructible enums (a unit-like
    // variant or one with only primitive fields). If none exists (e.g.,
    // every variant has an external_body field), fall back to the first
    // variant: `default` for an external_body field type routes to that
    // type's axiom-backed Inhabited instance, which is valid noncomputable.
    let base_variant = dt.variants.iter()
        .find(|v| v.fields.iter().all(|f| {
            field_recursive_target(&f.a.0, scc_paths).is_none()
                && !typ_references_external_body(&f.a.0, external_body_paths)
        }))
        .or_else(|| dt.variants.first())?;

    // Build `T.<base> default default ...` — the constructor applied to
    // `default` for each field. Lean infers the implicit type-args via the
    // target `Inhabited (T A)` plus the `[Inhabited A]` bound.
    let ctor_name = format!("{}.{}", path, sanitize(&base_variant.name));
    let mut body = LExpr::var_lit(&ctor_name);
    if !base_variant.fields.is_empty() {
        let args: Vec<LExpr> = base_variant.fields.iter()
            .map(|_| LExpr::var_lit("default"))
            .collect();
        body = LExpr::app(body, args);
    }

    // Binders: `{A : Type} [Inhabited A]` per type parameter.
    let mut binders: Vec<LBinder> = Vec::new();
    for (id, _) in dt.typ_params.iter() {
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit(id.as_str())),
            ty: LExpr::var_lit("Type"),
            kind: BinderKind::Implicit,
        });
        binders.push(LBinder {
            name: None,
            ty: LExpr::app(
                LExpr::var_lit("Inhabited"),
                vec![LExpr::var_lit(id.as_str())],
            ),
            kind: BinderKind::Instance,
        });
    }

    // Target: `Inhabited (T A B ...)`.
    let parent_applied = if dt.typ_params.is_empty() {
        LExpr::var_lit(&path)
    } else {
        let args: Vec<LExpr> = dt.typ_params.iter()
            .map(|(id, _)| LExpr::var_lit(id.as_str()))
            .collect();
        LExpr::app(LExpr::var_lit(&path), args)
    };
    let target = LExpr::app(LExpr::var_lit("Inhabited"), vec![parent_applied]);

    Some(Command::Instance(Instance {
        binders,
        target,
        methods: vec![InstanceMethod {
            name: "default".into(),
            body,
        }],
    }))
}

/// Emit per-variant accessor / discriminator defs for a datatype.
/// Empty for single-variant structs (handled via Lean's auto-generated
/// `structure` projections) and when `emit_accessors == false` (proof-
/// fn paths preserve native Lean match instead of routing through
/// generated accessors).
fn datatype_accessor_cmds(dt: &DatatypeX, emit_accessors: bool) -> Vec<Command> {
    let (path, short) = match &dt.name {
        Dt::Path(p) => (lean_name(p), short_name(p).to_string()),
        Dt::Tuple(_) => return vec![],
    };
    let is_single_variant_struct =
        dt.variants.len() == 1 && dt.variants[0].name.as_str() == short;
    if is_single_variant_struct || !emit_accessors {
        return vec![];
    }
    multi_variant_accessor_defs(dt, &path)
}

/// Emit the height fn for a datatype, parameterized by the SCC it
/// belongs to. See `height_fn_for_datatype` for the semantics.
fn datatype_height_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return None,
    };
    height_fn_for_datatype(dt, &path, scc_paths)
}

/// Emit `def T.height : T → Nat` alongside the datatype so that
/// non-int `decreases` measures on `T` can discharge the
/// termination obligation emitted by `sst_exp_to_ast_checked`'s
/// `CheckDecreaseHeight` arm.
///
/// - **Non-recursive datatype** (no recursive fields w.r.t. the SCC):
///   emit `fun _ => 1`. Doesn't help termination (there's no
///   structural subterm), but keeps the Lean symbol resolvable if a
///   user writes `decreases x` for a non-recursive `x` — the
///   obligation `1 < 1` is simply false, so the recursion fails
///   verification with a clear goal.
/// - **Recursive datatype**: emit a match over variants, summing
///   `1 + height(f)` for each field whose type is in `scc_paths`,
///   treating other fields as 0. The recursive call uses the
///   FIELD's height fn, not the parent's — so for an SCC, a
///   `Tree.Branch f` arm where `f : Forest` calls `Forest.height f`
///   (rather than the trivial `1` in the pre-#109 code that only
///   recursed on self).
///
/// `scc_paths` contains all datatype paths in the SCC the input `dt`
/// belongs to (always at least `dt`'s own path). For non-mutual
/// datatypes the set has size 1 and behavior matches the pre-#109
/// shape. For mutual SCCs (#109) the set has size >1 and the
/// emitted `def` MUST be wrapped in a `mutual ... end` block
/// alongside the other SCC members' height fns — Lean otherwise
/// rejects the cross-type recursive reference.
///
/// Returns `None` for **tuple datatypes** (`Dt::Tuple`) — they're
/// rendered as products with no declaration site.
///
/// The "recursive field" test peels `TypX::Boxed` (poly coercion)
/// and `TypX::Decorate` (e.g., `Box<Self>`, `&Self`) before
/// comparing — this matches how `typ_to_expr` renders field types
/// at the Lean level (Box is transparent).
fn height_fn_for_datatype(
    dt: &DatatypeX,
    path: &str,
    scc_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    use crate::lean_ast::{BinOp, ExprNode};
    if let Dt::Tuple(_) = &dt.name {
        return None;
    }

    // Generic datatypes (#108): emit `T.height : {A : Type} → … → T A B …
    // → Nat`. The implicit type-param binders let callers write just
    // `T.height x` — Lean infers A from x's type. Recursion is on the
    // T A structure, not on A itself; the equation compiler handles this
    // because the recursive arg (e.g. `Tree.Node x rest` → recurse on
    // `rest : Tree A`) decreases by structure regardless of A.
    let typ_param_names: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();
    let typed_input: LExpr = if typ_param_names.is_empty() {
        LExpr::var_synthetic(path)
    } else {
        LExpr::app(
            LExpr::var_synthetic(path),
            typ_param_names.iter()
                .map(|tp| LExpr::var_lit(tp))
                .collect(),
        )
    };
    let implicit_typ_binders: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder {
        name: Some(crate::lean_name::LeanName::lit(tp)),
        ty: LExpr::var_lit("Type"),
        kind: BinderKind::Implicit,
    }).collect();

    let has_recursive_field = dt.variants.iter().any(|v|
        v.fields.iter().any(|f| field_recursive_target(&f.a.0, scc_paths).is_some())
    );

    if !has_recursive_field {
        // Non-recursive: simple constant fn. The match-on-binder form
        // is fine here — there's no WF analysis needed.
        let mut binders = implicit_typ_binders;
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit("_")),
            ty: typed_input,
            kind: BinderKind::Explicit,
        });
        return Some(Command::Def(Def {
            attrs: vec!["simp".into()],
            name: format!("{}.height", path),
            binders,
            ret_ty: LExpr::var_lit("Nat"),
            body: LExpr::lit_int("1"),
            termination_by: vec![],
        }));
    }

    // Recursive: emit curried-form `def T.height : T → Nat | pat
    // => body | ...` rather than the match-on-binder form. The
    // curried form is the Lean-idiomatic shape for structural
    // recursion — the equation compiler is designed around it,
    // and WF analysis is more reliable when the recursion is
    // expressed as direct equations rather than a match-on-
    // binder.
    //
    // For generics (#108): emit implicit type-param binders BEFORE
    // the colon (via `DefCurried.binders`), not inside the type as
    // a `∀`. This produces `def T.height {A : Type} : T A → Nat
    // | pat => body` — Lean's equation compiler infers A from the
    // pattern's value position. Wrapping `∀ {A : Type}` inside the
    // type expression confuses elaboration: the equations end up
    // matching the implicit slot first, and `List.Nil` gets typed
    // as the `A` (Type-valued) instead of as the `List A` value.
    let arrow_ty = LExpr::new(ExprNode::BinOp {
        op: BinOp::Implies,
        lhs: Box::new(typed_input),
        rhs: Box::new(LExpr::var_lit("Nat")),
    });
    let equations: Vec<MatchArm> = dt.variants.iter().map(|v| {
        let var_san = sanitize(&v.name);
        let ctor_name = format!("{}.{}", path, var_san);
        let mut pats = Vec::with_capacity(v.fields.len());
        // (binder name, height fn name, deref count) for each
        // recursive field. The height fn name uses the FIELD's
        // datatype (which is in the SCC), not the parent's. For
        // self-recursion these match; for mutual recursion across
        // an SCC they differ. The deref count is the number of
        // wrapper layers Lean infers on the binder — for
        // `Box<Stack>` the binder is `Tactus.Box Stack` so we need
        // `<binder>.deref` to reach the inner `Stack`. Each layer
        // (Box / Ref / MutRef / Rc / Arc) contributes one `.deref`.
        //
        // Binder names follow the `_tactus_field_<idx>` convention
        // (see `expr_shared` Convention 1) — same shape as the
        // accessor-fn field-extract locals in `datatype_to_cmds`,
        // since the semantic role is identical: a pattern-match
        // binder for one positional field of a variant.
        let mut recursive_binders: Vec<(String, String, usize)> = Vec::new();
        for (idx, f) in v.fields.iter().enumerate() {
            if let Some(target_path) = field_recursive_target(&f.a.0, scc_paths) {
                let name = format!("_tactus_field_{}", idx);
                let height_fn = format!("{}.height", lean_name(target_path));
                let n_derefs = crate::expr_shared::count_ref_decorations(&*f.a.0);
                pats.push(LPattern::Var(crate::lean_name::LeanName::synthetic(name.clone())));
                recursive_binders.push((name, height_fn, n_derefs));
            } else {
                pats.push(LPattern::Wildcard);
            }
        }
        let mut arm_body = LExpr::lit_int("1");
        for (name, height_fn, n_derefs) in &recursive_binders {
            let arg = crate::expr_shared::apply_deref_chain(
                LExpr::var_synthetic(name.clone()),
                *n_derefs,
            );
            arm_body = LExpr::add(
                arm_body,
                LExpr::app1(LExpr::var_synthetic(height_fn.clone()), arg),
            );
        }
        MatchArm {
            pattern: LPattern::Ctor { name: ctor_name, args: pats },
            body: arm_body,
        }
    }).collect();
    Some(Command::DefCurried(DefCurried {
        attrs: vec!["simp".into()],
        name: format!("{}.height", path),
        binders: implicit_typ_binders,
        ty: arrow_ty,
        equations,
    }))
}


/// If `typ` is a reference to a datatype path that's in `scc_paths`,
/// returns that path. Otherwise None. Peels `TypX::Boxed` and
/// `TypX::Decorate` to handle `Box<Self>`, `&Self`, etc.
///
/// For non-mutual datatypes, `scc_paths` contains just the datatype's
/// own path — the result is "is this field self-referential?". For
/// mutually-recursive SCCs (#109), `scc_paths` contains every path in
/// the SCC, so a field of type `B` inside datatype `A` matches when
/// `B` is in the same SCC. The returned path is used by the height fn
/// emitter to choose `B.height` vs `A.height` for the recursive call.
///
/// Generic datatypes (#108): a field of type `Tree<A>` inside
/// `enum Tree<A> { … }` matches when its path is in `scc_paths`,
/// regardless of how the type-arg list compares. `Tree.height` is
/// generic over A, so structural recursion on a `Tree<A>`-typed
/// field is the same as on `Tree<U>` — Lean's equation compiler
/// handles both.
fn field_recursive_target<'a>(
    typ: &Typ,
    scc_paths: &'a std::collections::HashSet<&Path>,
) -> Option<&'a Path> {
    match &**crate::to_lean_type::peel_typ_wrappers(typ) {
        TypX::Datatype(Dt::Path(p), _, _) => scc_paths.get(p).copied(),
        _ => None,
    }
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
    // Generic datatypes (#108): the discriminator and accessors need
    // implicit type-param binders `{A : Type}` so the input `x : T A`
    // typechecks. For non-generic datatypes the binders list is empty
    // and `x : T` (no application). Same shape as `height_fn_for_datatype`.
    let typ_param_names: Vec<String> = dt.typ_params.iter()
        .map(|(id, _)| id.to_string())
        .collect();
    let typed_input: LExpr = if typ_param_names.is_empty() {
        LExpr::var_synthetic(type_name.to_string())
    } else {
        LExpr::app(
            LExpr::var_synthetic(type_name.to_string()),
            typ_param_names.iter()
                .map(|tp| LExpr::var_lit(tp))
                .collect(),
        )
    };
    // Binder pieces, computed once and cloned per (variant, field).
    // Each piece is a logical group:
    //
    // * `typ_param_pieces`: implicit `{A : Type}` per type param —
    //   needed by both discriminators and accessors (so the input
    //   `x : T A` typechecks).
    // * `inhabited_bound_pieces`: instance `[Inhabited A]` per type
    //   param — needed by accessors only (the unreachable-arm
    //   `default` fallback resolves via `Inhabited`). Discriminators
    //   return `Prop`, no `default` use.
    // * `x_binder`: the `(x : T A)` value parameter — same for both.
    let typ_param_pieces: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder {
        name: Some(crate::lean_name::LeanName::lit(tp)),
        ty: LExpr::var_lit("Type"),
        kind: BinderKind::Implicit,
    }).collect();
    let inhabited_bound_pieces: Vec<LBinder> = typ_param_names.iter().map(|tp| LBinder {
        name: None,
        ty: LExpr::app1(LExpr::var_lit("Inhabited"), LExpr::var_lit(tp)),
        kind: BinderKind::Instance,
    }).collect();
    let x_binder = LBinder {
        name: Some(crate::lean_name::LeanName::lit("x")),
        ty: typed_input.clone(),
        kind: BinderKind::Explicit,
    };
    let discriminator_binders = || -> Vec<LBinder> {
        let mut bs = typ_param_pieces.clone();
        bs.push(x_binder.clone());
        bs
    };
    let accessor_binders = || -> Vec<LBinder> {
        let mut bs = typ_param_pieces.clone();
        bs.extend(inhabited_bound_pieces.iter().cloned());
        bs.push(x_binder.clone());
        bs
    };
    let match_on_x = |arms: Vec<MatchArm>| LExpr::new(ExprNode::Match {
        scrutinee: Box::new(LExpr::var_lit("x")),
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
        let mut arms = vec![MatchArm {
            pattern: LPattern::Ctor {
                name: format!("{}.{}", type_name, var_san),
                args: wildcards,
            },
            body: LExpr::lit_bool(true),
        }];
        // The catch-all false arm is needed for multi-variant inductives
        // (totality) but redundant for single-variant ones — the single
        // ctor pattern is already exhaustive, so Lean would warn
        // "Redundant alternative" and `lean_process` reports that as a
        // verification error. For a one-variant inductive this
        // discriminator always returns `true` anyway.
        if dt.variants.len() > 1 {
            arms.push(MatchArm {
                pattern: LPattern::Wildcard,
                body: LExpr::lit_bool(false),
            });
        }
        cmds.push(Command::Def(Def {
            // `@[simp]`: let `simp_all` unfold the discriminator so
            // `tactus_auto` can close exec-fn goals that turn on a
            // pattern test. Without this, `k.isFoo` stays opaque and
            // the downstream `omega` / `simp_all` can't case-split
            // the enum.
            attrs: vec!["simp".into()],
            name: format!("{}.is{}", type_name, var_san),
            binders: discriminator_binders(),
            ret_ty: LExpr::var_lit("Prop"),
            body: match_on_x(arms),
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
                    LPattern::Var(crate::lean_name::LeanName::synthetic(field_local.clone()))
                } else {
                    LPattern::Wildcard
                }).collect();
            let mut arms = vec![MatchArm {
                pattern: LPattern::Ctor {
                    name: format!("{}.{}", type_name, var_san),
                    args: binders_pat,
                },
                body: LExpr::var_synthetic(field_local),
            }];
            // Catch-all `default` arm: needed for multi-variant
            // inductives (Lean requires totality) but redundant for
            // single-variant ones — the ctor pattern already covers
            // every value of the type. Adding the wildcard would
            // surface as Lean's "Redundant alternative" warning and
            // fail verification.
            if dt.variants.len() > 1 {
                arms.push(MatchArm {
                    pattern: LPattern::Wildcard,
                    // `default` resolves via `[Inhabited α]`, which
                    // Lean derives automatically for primitive
                    // types (Int, Nat, Bool) — the types exec-fn
                    // match-desugaring actually reaches. Users
                    // with custom field types may need a manual
                    // `instance : Inhabited Foo := ⟨…⟩`.
                    // Unreachable anyway when call sites guard
                    // the accessor with a prior isVariant check.
                    body: LExpr::var_lit("default"),
                });
            }
            cmds.push(Command::Def(Def {
                // `@[simp]` for the same reason as the discriminator:
                // `simp_all` should unfold the accessor before `omega`
                // tries to reason about its result. Without this the
                // accessor is opaque and goals involving it get stuck.
                attrs: vec!["simp".into()],
                name: format!("{}.{}_{}", type_name, var_san, field_name(&f.name)),
                binders: accessor_binders(),
                ret_ty: typ_to_expr(&f.a.0),
                body: match_on_x(arms),
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
    tactic_bodies: &HashMap<Fun, String>,
) -> Class {
    // Positional class binders: `(Self : Type) (T : Type) … (Item : outParam Type)`.
    let mut typ_params: Vec<LBinder> = Vec::new();
    typ_params.push(LBinder {
        name: Some(crate::lean_name::LeanName::lit("Self")),
        ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
        kind: BinderKind::Explicit,
    });
    for (tp, _) in tr.typ_params.iter() {
        typ_params.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit(tp.as_str())),
            ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
            kind: BinderKind::Explicit,
        });
    }
    for assoc_name in tr.assoc_typs.iter() {
        typ_params.push(LBinder {
            name: Some(crate::lean_name::LeanName::synthetic(sanitize(assoc_name))),
            ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
            kind: BinderKind::OutParam,
        });
    }

    // Use class-context bounds rendering so the trait's Self typ_param
    // (`Self%`) normalizes to `Self` (the class's outer type variable)
    // in inherited bounds like `trait Sub: Super` → `class Sub (Self :
    // Type) [Super Self] where ...`.
    let bounds = class_bounds_to_ast(&tr.typ_bounds);

    // Pre-compute the set of sibling method names. Used by proof-fn
    // method-type rendering: ensures expressions that reference
    // sibling trait methods must render UNQUALIFIED (Lean rejects
    // `Class.method` inside the class declaration; see
    // `proof_fn_method_type` docstring).
    let trait_short_name = short_name(&tr.name).to_string();
    let sibling_methods: std::collections::HashSet<String> = tr.methods.iter()
        .filter_map(|m| m.path.segments.last().map(|s| s.to_string()))
        .collect();

    let methods: Vec<ClassMethod> = tr.methods.iter().map(|method_fun| {
        let func = method_lookup.get(method_fun).unwrap_or_else(|| {
            panic!(
                "trait method {:?} not found in VIR function list — \
                 this is a Tactus bug, please report it",
                method_fun.path
            )
        });
        let short = method_fun.path.segments.last()
            .map(|s| s.as_str()).unwrap_or("_");
        // Class-method default body, when the trait provides one.
        // Render strategy by mode:
        // * Spec methods: render the actual body via `vir_expr_to_ast`,
        //   wrapped in `fun (p₁ : _) (p₂ : _) … => body`. Lean unfolds
        //   class defaults during typeclass dispatch, so the body is
        //   load-bearing.
        // * Exec methods: render `default` placeholder wrapped in
        //   lambda. Rendering exec bodies via vir_expr_to_ast panics
        //   on Assign/Loop/Return; the body isn't load-bearing for
        //   verification (walk_call inlines specs, not bodies).
        // * Proof methods: render the tactic body verbatim as
        //   `by <tactic>` (via Raw escape hatch). Default body in
        //   the trait provides a proof that holds for any Self
        //   satisfying the class — Verus enforces this. Wrapped in
        //   lambda over the proof fn's params so the body's
        //   references to params (`self`, etc.) resolve correctly.
        //
        // Note for proof-fn class methods: the method's TYPE is a
        // Prop-valued `∀ params, ensures` (or subtype for non-unit
        // returns) — see `proof_fn_method_type`. So the default body
        // must produce a term of that type, which a tactic proof does.
        let default = func.body.as_ref().map(|b| {
            let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
            let body_expr = match func.mode {
                vir::ast::Mode::Spec => wrap_body_with_param_derefs(
                    crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &body_binders),
                    &func.params),
                vir::ast::Mode::Exec => LExpr::var_lit("default"),
                vir::ast::Mode::Proof => {
                    // Class default for proof-fn method. Mirrors
                    // `trait_impl_to_ast`'s instance-side logic:
                    // unit return → `by <tactic>`; non-unit return
                    // → `⟨value, by first | rfl | simp_all⟩` built
                    // structurally via Anon + ByBlock.
                    if is_unit_typ(&func.ret.x.typ) {
                        let tac = tactic_bodies.get(&func.name)
                            .map(|s| s.as_str())
                            .unwrap_or(TACTIC_BODY_FALLBACK);
                        LExpr::new(ExprNode::ByBlock { tactic: tac.to_string() })
                    } else {
                        let value = wrap_body_with_param_derefs(
                            crate::to_lean_expr::vir_expr_to_ast_with_binders(b, &body_binders),
                            &func.params);
                        let proof = LExpr::new(ExprNode::ByBlock {
                            tactic: SUBTYPE_WITNESS_AUTO_PROOF.to_string(),
                        });
                        LExpr::new(ExprNode::Anon(vec![value, proof]))
                    }
                }
            };
            if func.params.is_empty() {
                body_expr
            } else {
                let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder {
                    name: Some(crate::lean_name::LeanName::synthetic(sanitize(p.x.name.0.as_str()))),
                    ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("_"))),
                    kind: BinderKind::Explicit,
                }).collect();
                LExpr::new(ExprNode::Lambda {
                    binders,
                    body: Box::new(body_expr),
                })
            }
        });
        // Only spec-mode methods get termination clauses rendered.
        // Exec methods have placeholder bodies (no termination to
        // discharge). Proof methods have tactic bodies, but Lean
        // doesn't accept `termination_by` on class-method defaults
        // (it's for `def`/`theorem`); recursive proof-fn trait
        // methods are a documented deferral — see DESIGN.md TODO.
        let termination_by: Vec<LExpr> = if matches!(func.mode, vir::ast::Mode::Spec) {
            func.decrease.iter().map(|d| vir_expr_to_ast(d)).collect()
        } else {
            Vec::new()
        };
        // Method type: Prop-valued for proof fns, function-typed for
        // spec/exec. Proof-fn type captures the trait's full semantic
        // promise (the ensures is the class method type itself, with
        // sibling references stripped to unqualified form).
        let ty = if matches!(func.mode, vir::ast::Mode::Proof) {
            proof_fn_method_type(func, &trait_short_name, &sibling_methods)
        } else {
            method_type(func)
        };
        ClassMethod {
            name: sanitize(short),
            ty,
            default,
            termination_by,
        }
    }).collect();

    Class {
        name: lean_name(&tr.name),
        typ_params,
        bounds,
        methods,
    }
}

/// Build the method type `<self_ty> → P₁ → … → Ret`. Inside a class,
/// associated types become unqualified identifiers (they're class type
/// params), and the trait's `Self%` type-param normalizes to the
/// class's outer `Self`. Reference-like decorations on the receiver
/// type (`&self`, `&mut self`, `Box<Self>`, etc.) survive as
/// `Tactus.Ref Self` etc. so that trait dispatch matches the impl
/// side.
fn method_type(func: &FunctionX) -> LExpr {
    let mut out = typ_maybe_projection_to_expr(&func.ret.x.typ);
    for p in func.params.iter().rev() {
        out = LExpr::new(ExprNode::BinOp {
            op: crate::lean_ast::BinOp::Implies,
            lhs: Box::new(typ_maybe_projection_to_expr(&p.x.typ)),
            rhs: Box::new(out),
        });
    }
    out
}

/// Inside a class definition:
/// - `Self::AssocType` projections render as the bare associated-type
///   name (a class type param).
/// - The trait's Self typ_param (`TypX::TypParam` with name
///   matching `vir::def::trait_self_type_param()`) renders as
///   the outer class's `Self` type variable.
/// - Everything else delegates to the standard type translator.
///
/// **Why the Self normalization.** Verus represents the trait's Self
/// as a typ_param with a canonical disambiguated name (literally
/// `"Self%"` per `vir::def::TRAIT_SELF_TYPE_PARAM`). The class
/// declaration's outer type variable is literally `Self` (no
/// disambiguator), so a method signature referencing the trait's
/// Self must normalize to match. Without this, e.g., a `proof fn
/// produce() -> (r: Self)` class field would render as
/// `produce : { _return : Self% // True }` — a dangling reference
/// the sanity check (correctly) rejects.
///
/// We match against `trait_self_type_param()` directly rather than
/// string-parsing the suffix, so a Verus-side rename of the constant
/// causes a compile error here rather than silent breakage.
fn typ_maybe_projection_to_expr(typ: &TypX) -> LExpr {
    use vir::ast::TypDecoration;
    use crate::lean_ast::BinOp;

    fn applied(name: &str, args: Vec<LExpr>) -> LExpr {
        if args.is_empty() {
            LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit(name)))
        } else {
            LExpr::new(ExprNode::App {
                head: Box::new(LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit(name)))),
                args,
            })
        }
    }

    match typ {
        TypX::TypParam(name) if *name == vir::def::trait_self_type_param() => {
            LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Self")))
        }
        TypX::Projection { name, .. } => {
            // Inside a class declaration, assoc-type projections render
            // as the bare name (a class type param).
            LExpr::new(ExprNode::Var(crate::lean_name::LeanName::synthetic(sanitize(name))))
        }
        TypX::Decorate(deco, _, inner) => match deco {
            TypDecoration::Ref => applied("Tactus.Ref", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::MutRef => applied("Tactus.MutRef", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Box => applied("Tactus.Box", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Rc => applied("Tactus.Rc", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Arc => applied("Tactus.Arc", vec![typ_maybe_projection_to_expr(inner)]),
            TypDecoration::Ghost | TypDecoration::Tracked
            | TypDecoration::Never | TypDecoration::ConstPtr =>
                typ_maybe_projection_to_expr(inner),
        },
        TypX::MutRef(inner) => applied("Tactus.MutRef", vec![typ_maybe_projection_to_expr(inner)]),
        TypX::Boxed(inner) => typ_maybe_projection_to_expr(inner),
        TypX::Datatype(dt, args, _) => match dt {
            vir::ast::Dt::Path(path) => {
                let head = crate::to_lean_type::lean_name(path);
                let mapped: Vec<LExpr> = args.iter()
                    .map(|a| typ_maybe_projection_to_expr(a)).collect();
                if mapped.is_empty() {
                    LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit(&head)))
                } else {
                    LExpr::new(ExprNode::App {
                        head: Box::new(LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit(&head)))),
                        args: mapped,
                    })
                }
            }
            vir::ast::Dt::Tuple(_) => match args.len() {
                0 => applied("Unit", Vec::new()),
                1 => typ_maybe_projection_to_expr(&args[0]),
                _ => {
                    let mut iter = args.iter().rev();
                    let mut acc = typ_maybe_projection_to_expr(iter.next().unwrap());
                    for a in iter {
                        acc = LExpr::new(ExprNode::BinOp {
                            op: BinOp::Prod,
                            lhs: Box::new(typ_maybe_projection_to_expr(a)),
                            rhs: Box::new(acc),
                        });
                    }
                    acc
                }
            },
        },
        TypX::SpecFn(params, ret) => {
            let mut out = typ_maybe_projection_to_expr(ret);
            for p in params.iter().rev() {
                out = LExpr::new(ExprNode::BinOp {
                    op: BinOp::Implies,
                    lhs: Box::new(typ_maybe_projection_to_expr(p)),
                    rhs: Box::new(out),
                });
            }
            out
        }
        TypX::Primitive(prim, args) => {
            let head = match prim {
                vir::ast::Primitive::Array => "Array",
                vir::ast::Primitive::Slice => "List",
                vir::ast::Primitive::StrSlice => "String",
                vir::ast::Primitive::Ptr => "USize",
                vir::ast::Primitive::Global => "Unit",
            };
            let type_args: Vec<_> = match prim {
                vir::ast::Primitive::Array | vir::ast::Primitive::Slice => {
                    args.iter().take(1).map(|a| typ_maybe_projection_to_expr(a)).collect()
                }
                _ => args.iter().map(|a| typ_maybe_projection_to_expr(a)).collect(),
            };
            applied(head, type_args)
        }
        // Everything else falls through to the standard renderer; these
        // shapes don't contain Self% or Projection (or if they do, the
        // standard renderer's emission is acceptable as-is).
        _ => typ_to_expr(typ),
    }
}

// `is_unit_typ` lives in `to_lean_type.rs` — shared with `dep_order`'s
// `seed_impl_proof_method_bodies`, which needs the same discrimination
// to decide whether an impl proof-fn body must be pre-seeded.
use crate::to_lean_type::is_unit_typ;

/// Build value-level parameter binders for a trait method's class-
/// method type. Distinct from `fn_binders` (which also emits
/// `(T : Type)` for typ_params and `[Trait T]` for trait bounds — both
/// of which are the OUTER class's responsibility when we're inside a
/// class declaration). Mathlib's class method type idiom binds only
/// value-level params.
///
/// For `self`-typed params, renders the type as `Self` (the class
/// type variable) rather than going through `typ_to_expr` which would
/// produce the trait's full path.
fn class_method_value_binders(func: &FunctionX) -> Vec<LBinder> {
    let mut out: Vec<LBinder> = Vec::new();
    for p in func.params.iter() {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        let ty = typ_maybe_projection_to_expr(&p.x.typ);
        out.push(LBinder {
            name: Some(name.clone()),
            ty,
            kind: BinderKind::Explicit,
        });
        if let Some(pred) = crate::to_lean_sst_expr::type_bound_predicate(
            &LExpr::var(name.clone()),
            &p.x.typ,
        ) {
            out.push(LBinder {
                name: Some(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str()))),
                ty: pred,
                kind: BinderKind::Explicit,
            });
        }
    }
    out
}

/// Build the class-method type for a proof-fn trait method.
///
/// Lean's idiom for "typeclass promises lemmas about its types" is
/// Prop-typed class fields (see Mathlib's `Group.mul_assoc`, etc.).
/// This helper builds `∀ (params...) (req_hyps...), <ensures>` for the
/// common unit-return case.
///
/// For non-unit return types, the goal becomes a subtype
/// `{ ret : RetTy // <ensures> }` so the instance must provide a
/// witnessing value together with a proof. The return name is bound
/// inside the ensures by Verus's named-return convention.
///
/// References to sibling trait methods inside the ensures must render
/// as UNQUALIFIED names. Lean rejects `ClassName.method` inside the
/// class declaration itself — the class isn't fully declared at that
/// point. Mathlib uniformly uses unqualified sibling references; we
/// post-process the rendered LExpr to strip the class qualifier from
/// known sibling method names.
fn proof_fn_method_type(
    func: &FunctionX,
    class_name: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    // Class methods bind ONLY value-level params (and their refinement
    // bounds + requires hypotheses). The trait's `Self` is the class's
    // type variable (already in scope at the method's site); the
    // trait's bounds are imposed by the class extends mechanism, not
    // re-introduced on each method. Mathlib's `Semigroup` shows the
    // shape: `class Semigroup (G : Type u) extends Mul G where
    //   mul_assoc : ∀ a b c : G, ...` — no `(G : Type)` or `[Mul G]`
    // re-binders inside `mul_assoc`'s type.
    let mut binders = class_method_value_binders(func);
    let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
    for (i, req) in func.require.iter().enumerate() {
        // Inside the class declaration, sibling refs can use bare
        // names (the class's own scope) — pass empty `impl_prefix`
        // to get the bare-name rewrite. Instance bodies use a
        // non-empty prefix to route to impl-specific standalones.
        let req_ty = strip_class_qualifier(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(req, &body_binders),
            class_name, "", sibling_methods,
        );
        // Requires render as named hypothesis binders following the
        // `_tactus_<role>_<id>` reserved-name convention (see
        // expr_shared.rs § "Reserved identifier conventions").
        // Anonymous binders aren't an option — Lean's ∀ chain
        // requires each binder to have a name, and our pp only
        // emits `(name : ty)` when name is Some.
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::synthetic(format!("_tactus_req_{}", i))),
            ty: req_ty,
            kind: BinderKind::Explicit,
        });
    }
    let ensures = and_all(func.ensure.0.iter()
        .map(|e| strip_class_qualifier(
            crate::to_lean_expr::vir_expr_to_ast_with_binders(e, &body_binders),
            class_name, "", sibling_methods))
        .collect());

    let goal = if is_unit_typ(&func.ret.x.typ) {
        ensures
    } else {
        // Non-unit return: render as `{ ret : RetTy // <ensures> }`
        // via the structured Subtype AST node. The node owns its
        // type and predicate as LExprs — pp handles composition,
        // sanity check handles scoping (name is bound in pred),
        // substitute handles alpha-renaming.
        let ret_name = crate::lean_name::LeanName::synthetic(
            sanitize(func.ret.x.name.0.as_str())
        );
        let ret_ty = typ_maybe_projection_to_expr(&func.ret.x.typ);
        LExpr::new(ExprNode::Subtype {
            name: ret_name,
            ty: Box::new(ret_ty),
            pred: Box::new(ensures),
        })
    };

    if binders.is_empty() {
        goal
    } else {
        LExpr::new(ExprNode::Forall { binders, body: Box::new(goal) })
    }
}

/// Walk `expr` and rewrite any `Var("<class_name>.<method>")` where
/// `method` is in `sibling_methods` to `Var("<method>")` (unqualified).
///
/// Inside a class declaration, sibling references to other methods of
/// the same class MUST be unqualified — see `proof_fn_method_type`'s
/// docstring for why. This helper applies the rewrite to a fully-
/// rendered LExpr, walking via the existing structural map_children
/// machinery so we don't have to enumerate every ExprNode variant.
/// Rewrite `Class.method` refs inside an instance body to the
/// disambiguated standalone-def name (`<impl_prefix>.method`).
/// Lean's `instance` construction can't forward-reference siblings
/// via class dispatch (the instance isn't available for synthesis
/// during its own definition — see Lean reference manual §
/// "Instance Declarations"). So sibling refs in impl method bodies
/// must go through the standalone defs that `spec_fn_to_ast` emits,
/// at their post-disambiguation names (per `lean_name`'s impl-
/// marker preservation, 2026-05-17 fix for
/// BUG-no-helper-proof-fn-call-from-exec.md).
///
/// `impl_prefix` is the dotted-path prefix shared by all siblings
/// of THIS impl (computed by dropping the last segment of any
/// impl method's `lean_name` rendering — e.g., for `MyInt::is_zero`
/// at full path `test_crate.impl__0.is_zero`, the prefix is
/// `test_crate.impl__0`). Passed in by `trait_impl_to_ast`.

fn strip_class_qualifier(
    expr: LExpr,
    class_name: &str,
    impl_prefix: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    let class_prefix = format!("{}.", class_name);
    strip_class_qualifier_rec(expr, &class_prefix, impl_prefix, sibling_methods)
}

fn strip_class_qualifier_rec(
    expr: LExpr,
    class_prefix: &str,
    impl_prefix: &str,
    sibling_methods: &std::collections::HashSet<String>,
) -> LExpr {
    match &expr.node {
        ExprNode::Var(name) => {
            let s = name.as_str();
            if let Some(rest) = s.strip_prefix(class_prefix) {
                if sibling_methods.contains(rest) {
                    let disambiguated = if impl_prefix.is_empty() {
                        rest.to_string()
                    } else {
                        format!("{}.{}", impl_prefix, rest)
                    };
                    return LExpr::new(ExprNode::Var(
                        crate::lean_name::LeanName::synthetic(disambiguated),
                    ));
                }
            }
            expr
        }
        _ => {
            let node = crate::lean_ast::map_children(&expr.node, |c: &LExpr| {
                strip_class_qualifier_rec(c.clone(), class_prefix, impl_prefix, sibling_methods)
            });
            LExpr::new(node)
        }
    }
}

// ── Trait impl (Lean `instance`) ───────────────────────────────────────

pub fn trait_impl_to_ast(
    ti: &TraitImplX,
    method_impls: &[&FunctionX],
    assoc_types: &[&AssocTypeImplX],
    tactic_bodies: &HashMap<Fun, String>,
    subst: &crate::impl_subst::ImplSubst,
) -> Instance {
    let mut binders: Vec<LBinder> = Vec::new();
    for tp in ti.typ_params.iter() {
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit(tp.as_str())),
            ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
            kind: BinderKind::Implicit,
        });
    }
    // Fresh implicit binders from the projection substitution
    // (per-impl, Bug B step 2). Each fresh binder corresponds to a
    // `<X as T>::N` projection appearing in the impl's signature;
    // see `impl_subst::ImplSubst` for the design.
    for fresh in subst.fresh_binders.iter() {
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit(fresh.as_str())),
            ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
            kind: BinderKind::Implicit,
        });
    }
    // Augmented bound list: original bounds + fake TypEquality
    // bounds that wire fresh binders into the relevant trait
    // brackets. `trait_bounds_to_ast` already iterates bounds and
    // appends matching TypEquality typs to the rendered args, so
    // synthesising fake equalities reuses that machinery.
    let augmented_bounds: Vec<GenericBound> = (*ti.typ_bounds).iter().cloned()
        .chain(subst.fake_bounds.iter().cloned())
        .collect();
    let augmented_bounds = std::sync::Arc::new(augmented_bounds);
    binders.extend(trait_bounds_to_ast(&augmented_bounds));

    // Build `TraitName arg1 arg2 …` — trait_typ_args are the positional
    // trait type arguments (Self + extras); assoc_types fill the outParam
    // slots declared by the class. Both are rewritten through `subst`
    // to replace `<X as T>::N` projections with the fresh binder names.
    let mut target_args: Vec<LExpr> = Vec::new();
    for t in ti.trait_typ_args.iter() {
        target_args.push(typ_to_expr(&subst.rewrite_typ(t)));
    }
    for a in assoc_types { target_args.push(typ_to_expr(&subst.rewrite_typ(&a.typ))); }
    let target = if target_args.is_empty() {
        LExpr::new(ExprNode::Var(crate::lean_name::LeanName::from_path(&ti.trait_path)))
    } else {
        LExpr::new(ExprNode::App {
            head: Box::new(LExpr::new(ExprNode::Var(crate::lean_name::LeanName::from_path(&ti.trait_path)))),
            args: target_args,
        })
    };

    // Skip body=None methods — they inherit from the class default.
    // Lean's typeclass machinery dispatches to the class default
    // when the instance omits a method. For an empty impl
    // (`impl Tr for T {}` with all method bodies inherited), the
    // result is `instance : Tr T where` with no method bodies —
    // Lean fills in everything from the class.
    //
    // Render strategy is mode-dispatched, see the inner `match`:
    // * Spec methods: render the actual body via `vir_expr_to_ast`
    //   (Lean's typeclass dispatch may unfold the instance's
    //   method during proof, so the body is load-bearing).
    // * Exec methods: emit `default` placeholder (the body isn't
    //   load-bearing — walk_call inlines specs at call sites, not
    //   bodies via typeclass dispatch). Rendering the exec body
    //   would panic on Assign / Loop / Return constructs.
    // * Proof methods, two sub-cases:
    //   - Unit return: instance produces a proof via `by <tactic>`.
    //   - Non-unit return: instance produces a `⟨value, proof⟩`
    //     pair (the body is the witness; rfl/simp_all closes the
    //     subtype equality).
    //
    // Note: if the trait method has NO default body AND the impl
    // also has body=None, that's a structurally invalid state
    // (Verus would have rejected the impl as missing a required
    // method) — skipping is still safe because Lean would catch
    // the missing-method-in-instance error directly.
    // Instance method bodies that reference sibling trait methods
    // must use the BARE standalone-def name, not the class-qualified
    // `Class.method` form — Lean's `instance` construction can't
    // forward-reference siblings (the instance isn't available for
    // synthesis during its own definition; see Lean reference manual
    // § "Instance Declarations"). The VIR-level
    // `rewrite_self_sibling_calls` handles the swap; `method_redirects`
    // maps each impl method's short name to its full `Fun`. The
    // rewrite gates on receiver type, leaving cross-instance calls
    // (blanket-impl case) as class dispatch.
    //
    // Source of truth: `subst.method_context.method_redirects`.
    // That map carries pre-renamed Funs (when the impl-method
    // natural-name rename applies), so sibling-call rewrites
    // produce `Bar.Counter.method` instead of `impl__N.method`.
    // Fallback to empty map when no method context is set (no impl
    // methods, or method_context absent).
    let empty_redirects: HashMap<String, Fun> = HashMap::new();
    let method_redirects: &HashMap<String, Fun> = subst.method_context.as_ref()
        .map(|c| &c.method_redirects)
        .unwrap_or(&empty_redirects);

    let methods: Vec<InstanceMethod> = method_impls.iter()
        .filter_map(|func| {
            let short = func.name.path.segments.last()
                .map(|s| s.as_str()).unwrap_or("_");
            // Body=None impl methods (`uninterp spec fn ...;`) get a
            // synthesized body that dispatches to the standalone axiom
            // emitted by `spec_fn_to_ast`. Without this the instance
            // declares but doesn't provide the method, and Lean rejects.
            // The standalone axiom has signature `(typ_params...)
            // [bounds...] (params...) -> RetTy`; partial-applying the
            // typ_params (which are in scope as implicit binders on the
            // instance) plus param vars in the lambda body gives a
            // function matching the class field type via eta-expansion.
            // Spec-mode only — body=None proof and exec methods are
            // structurally invalid (Verus would have rejected) so the
            // filter still drops them.
            let body_expr = match (func.mode, &func.body) {
                (vir::ast::Mode::Spec, None) => {
                    // Use the renamed Fun path from `method_redirects`
                    // — same source of truth as the body-rewrite
                    // path, carrying the natural-name rename when
                    // applied. Both `method_redirects` and this
                    // `method_impls.iter().filter_map(|func| ...)`
                    // loop iterate the same `method_impls` slice,
                    // so the lookup is guaranteed.
                    let method_short = func.name.path.segments.last()
                        .expect("impl method has at least one path segment")
                        .as_str();
                    let standalone_path = method_redirects.get(method_short)
                        .expect("method_redirects has an entry for every method_impl")
                        .path.clone();
                    let standalone = LExpr::new(ExprNode::Var(
                        crate::lean_name::LeanName::from_path(&standalone_path)
                    ));
                    let mut args: Vec<LExpr> = func.typ_params.iter().map(|tp| {
                        LExpr::new(ExprNode::Var(
                            crate::lean_name::LeanName::lit(tp.as_str())
                        ))
                    }).collect();
                    for p in func.params.iter() {
                        args.push(LExpr::new(ExprNode::Var(
                            crate::lean_name::LeanName::synthetic(
                                sanitize(p.x.name.0.as_str())
                            )
                        )));
                    }
                    if args.is_empty() {
                        standalone
                    } else {
                        LExpr::new(ExprNode::App {
                            head: Box::new(standalone),
                            args,
                        })
                    }
                }
                (vir::ast::Mode::Proof, None) | (vir::ast::Mode::Exec, None) => return None,
                (vir::ast::Mode::Spec, Some(body)) => {
                    // VIR-level type-aware redirect of self-sibling
                    // Class.method calls to impl__N.method standalones.
                    // For blanket-impl bodies that call Trait.method on
                    // a typ-param (a different instance), the receiver-
                    // type check skips the rewrite and the call stays
                    // as class dispatch. See `rewrite_self_sibling_calls`
                    // docs for the full rationale (Bug B body fix).
                    let self_typ = ti.trait_typ_args.first()
                        .expect("impl's trait_typ_args must include Self");
                    let rewritten = crate::impl_subst::rewrite_self_sibling_calls(
                        body, &ti.trait_path, self_typ, &method_redirects,
                    );
                    // Wrap with `let p := p.deref` for each reference-
                    // decorated param so the body sees inner types.
                    let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
                    wrap_body_with_param_derefs(
                        crate::to_lean_expr::vir_expr_to_ast_with_binders(&rewritten, &body_binders),
                        &func.params,
                    )
                }
                (vir::ast::Mode::Exec, Some(_)) => {
                    // Exec placeholder. `default` produces a value
                    // of any type, satisfying Lean's instance-completeness
                    // requirement without needing to render the
                    // (stateful) exec body. walk_call inlines specs
                    // at call sites, not bodies via typeclass dispatch.
                    LExpr::var_lit("default")
                }
                (vir::ast::Mode::Proof, Some(_)) => {
                    // Proof methods. Two cases based on return type:
                    //
                    // (a) Unit return: the class method's TYPE is
                    //     `∀ params, ensures` (a Prop). The instance
                    //     must produce a proof — the user's `by {
                    //     tactic }` body. Renders as ByBlock with
                    //     context-aware indentation.
                    //
                    // (b) Non-unit return: the class method's TYPE is
                    //     `∀ params, { r : RetTy // ensures }` (a
                    //     subtype). The instance must produce a
                    //     `⟨value, proof⟩` pair. Verus's `by { }`
                    //     syntax doesn't fit non-unit returns (the
                    //     sanitized body fails Rust's type check),
                    //     so the user writes a regular Verus-style
                    //     body expression. Tactus renders that body
                    //     as the WITNESS VALUE and emits `by rfl`
                    //     as the proof (the canonical case where the
                    //     body matches the ensures' RHS literally).
                    //     For non-trivial proofs, the user adds a
                    //     `proof { }` block in the body — Verus's
                    //     auto-postcondition-check handles it on the
                    //     Verus side.
                    if is_unit_typ(&func.ret.x.typ) {
                        let tac = tactic_bodies.get(&func.name)
                            .map(|s| s.as_str())
                            .unwrap_or(TACTIC_BODY_FALLBACK);
                        LExpr::new(ExprNode::ByBlock { tactic: tac.to_string() })
                    } else {
                        // Non-unit return: subtype value pair
                        // `⟨body, by first | rfl | simp_all⟩` built
                        // via structured AST nodes (Anon + ByBlock)
                        // rather than Raw string formatting — pp
                        // handles composition, sanity checks the
                        // value's refs, indentation tracks context
                        // automatically.
                        //
                        // The body's references to sibling spec
                        // methods (e.g., `self.target()`) render via
                        // `vir_expr_to_ast` as the UNQUALIFIED
                        // standalone-def name. At instance-body
                        // emission position, sibling class-field
                        // refs aren't in scope (Lean's instance
                        // elaboration doesn't bring fields into
                        // scope mid-block), AND qualified
                        // `Class.method` refs fail because the
                        // typeclass instance is being constructed.
                        // The standalone def IS in scope —
                        // dep_order pre-seeds impl proof-fn method
                        // bodies for non-unit returns
                        // (`seed_impl_proof_method_bodies`) so the
                        // called spec methods emit as standalone
                        // defs before the instance.
                        let body = func.body.as_ref().unwrap();
                        // VIR-level rewrite (same as the Spec case).
                        let self_typ = ti.trait_typ_args.first()
                            .expect("impl's trait_typ_args must include Self");
                        let rewritten = crate::impl_subst::rewrite_self_sibling_calls(
                            body, &ti.trait_path, self_typ, &method_redirects,
                        );
                        let body_binders = crate::to_lean_expr::binder_ctx_from_params(&func.params);
                        let value = wrap_body_with_param_derefs(
                            crate::to_lean_expr::vir_expr_to_ast_with_binders(&rewritten, &body_binders),
                            &func.params,
                        );
                        // `rfl` closes when body matches ensures
                        // literally; `simp_all` handles unfolding
                        // through standalone def chains.
                        let proof = LExpr::new(ExprNode::ByBlock {
                            tactic: SUBTYPE_WITNESS_AUTO_PROOF.to_string(),
                        });
                        LExpr::new(ExprNode::Anon(vec![value, proof]))
                    }
                }
            };
            let lambda = if func.params.is_empty() {
                body_expr
            } else {
                // `fun (p₁ : _) (p₂ : _) … => body`. The `_` lets Lean
                // infer each parameter type from the class's method
                // signature, which is what we want.
                let binders: Vec<LBinder> = func.params.iter().map(|p| LBinder {
                    name: Some(crate::lean_name::LeanName::synthetic(sanitize(p.x.name.0.as_str()))),
                    ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("_"))),
                    kind: BinderKind::Explicit,
                }).collect();
                LExpr::new(ExprNode::Lambda {
                    binders,
                    body: Box::new(body_expr),
                })
            };
            Some(InstanceMethod { name: sanitize(short), body: lambda })
        })
        .collect();

    Instance { binders, target, methods }
}

// ── Shared helpers ──────────────────────────────────────────────────────

/// Function parameter list as AST binders: type params, trait bounds,
/// then value params. Const generics become explicit `(N : ConstType)`
/// instead of `(N : Type)`.
fn fn_binders(f: &FunctionX) -> Vec<LBinder> {
    fn_binders_with_bounds(f, /* include_bound_hyps */ true)
}

/// Spec-fn variant of `fn_binders`: omit the `h_<name>_bound` refinement
/// hypotheses. Spec fns are Lean defs, not theorems — bound hyps would
/// change the type from `Int → Int` to `Int → Bound → Int` and break
/// call sites that only pass values. Bounds for spec-fn params are
/// instead established at theorem-call sites (where the corresponding
/// hyps DO exist via `fn_binders` on the calling proof/exec fn).
fn fn_binders_without_bound_hyps(f: &FunctionX) -> Vec<LBinder> {
    fn_binders_with_bounds(f, /* include_bound_hyps */ false)
}

fn fn_binders_with_bounds(f: &FunctionX, include_bound_hyps: bool) -> Vec<LBinder> {
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
            LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type")))
        };
        out.push(LBinder {
            name: Some(crate::lean_name::LeanName::lit(tp.as_str())),
            ty,
            kind: BinderKind::Explicit,
        });
    }

    out.extend(trait_bounds_to_ast(&f.typ_bounds));

    // Each param → one binder, and (for fixed-width int types in
    // proof/exec contexts, gated by `include_bound_hyps`) one
    // hypothesis binder right after giving the refinement bounds.
    //
    // Three callers, two regimes:
    //   - `fn_binders` (proof fn + exec fn theorem path) → bounds INCLUDED.
    //     Must mirror `sst_to_lean::exec_fn_theorem_to_ast`'s bound
    //     emission so proof-fn-callers and exec-fn-callers see the
    //     same in-scope refinement for shared params.
    //   - `fn_binders_without_bound_hyps` (spec fn def path) → bounds OMITTED.
    //     Spec fns are Lean defs, not theorems; bound hyps would change
    //     the signature from `Int → Int` to `Int → Bound → Int` and
    //     break call sites. Bounds for spec-fn params are established
    //     at theorem-call sites (where the corresponding hyps DO exist
    //     via `fn_binders` on the calling proof/exec fn).
    for p in f.params.iter() {
        let name = crate::lean_name::LeanName::from_var_ident(&p.x.name);
        out.push(LBinder {
            name: Some(name.clone()),
            ty: crate::to_lean_type::param_binder_typ(&p.x.typ, p.x.is_mut),
            kind: BinderKind::Explicit,
        });
        if include_bound_hyps {
            // For wrapper-bound params (`Tactus.Ref`/`MutRef`/...), the
            // bound applies to the inner value via `.deref` — the wrapper
            // itself has no order/arithmetic instance.
            let bound_value = if needs_param_deref(p) {
                LExpr::field_proj(LExpr::var(name.clone()), "deref")
            } else {
                LExpr::var(name.clone())
            };
            if let Some(pred) = crate::to_lean_sst_expr::type_bound_predicate(
                &bound_value,
                &p.x.typ,
            ) {
                out.push(LBinder {
                    name: Some(crate::lean_name::LeanName::synthetic(format!("h_{}_bound", name.as_str()))),
                    ty: pred,
                    kind: BinderKind::Explicit,
                });
            }
        }
    }

    out
}

/// Generic bounds → Lean `[Trait T₁ T₂ …]` instance binders, with any
/// matching `TypEquality` bounds merged in as extra type arguments.
fn trait_bounds_to_ast(bounds: &GenericBounds) -> Vec<LBinder> {
    trait_bounds_to_ast_with(bounds, |t| typ_to_expr(t))
}

/// Class-context variant of `trait_bounds_to_ast` — uses
/// `typ_maybe_projection_to_expr` for type rendering so the trait's
/// Self typ_param (`Self%`) normalizes to `Self` (the class's outer
/// type variable) when it appears in bounds.
///
/// Used by `trait_to_ast` when rendering the class declaration's
/// inherited bounds (e.g., `trait Sub: Super` produces a `[Super Self]`
/// bound on the Sub class, where `Self` must match the class's outer
/// `Self : Type` binder, not the disambiguated `Self%` name).
fn class_bounds_to_ast(bounds: &GenericBounds) -> Vec<LBinder> {
    trait_bounds_to_ast_with(bounds, |t| typ_maybe_projection_to_expr(t))
}

fn trait_bounds_to_ast_with<F>(bounds: &GenericBounds, typ_render: F) -> Vec<LBinder>
where
    F: Fn(&TypX) -> LExpr,
{
    use vir::ast_util::types_equal;
    let mut out = Vec::new();
    for bound in bounds.iter() {
        if let GenericBoundX::Trait(TraitId::Path(path), typs) = &**bound {
            let mut args: Vec<LExpr> = typs.iter().map(|t| typ_render(t)).collect();
            // Append TypEquality typs whose (trait_path, trait_typ_args)
            // match THIS bound. Matching by path alone is too loose when
            // multiple bounds share a trait but differ on typ_args
            // (e.g., `impl<A: View, B: View>` produces two separate
            // bounds, each needing only its own TypEquality entries).
            // Pre-2026-05-19 this matched on path only and 2-typ-param
            // blanket impls produced malformed `[View A V_a V_b]`
            // 3-arg brackets. Pinned by
            // `test_view_blanket_impl_multi_param_probe`.
            for other in bounds.iter() {
                if let GenericBoundX::TypEquality(eq_path, eq_typs, _, typ) = &**other {
                    if lean_name(eq_path) != lean_name(path) { continue; }
                    if typs.len() != eq_typs.len() { continue; }
                    let typs_match = typs.iter().zip(eq_typs.iter())
                        .all(|(a, b)| types_equal(a, b));
                    if !typs_match { continue; }
                    args.push(typ_render(typ));
                }
            }
            let target = LExpr::new(ExprNode::App {
                head: Box::new(LExpr::new(ExprNode::Var(crate::lean_name::LeanName::from_path(path)))),
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
