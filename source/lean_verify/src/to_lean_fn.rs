//! Translate VIR declarations to `lean_ast` commands and pp them.
//!
//! Each `write_*` entry point builds a `lean_ast::Command` (or a `Vec` of
//! them) and pretty-prints it into the caller's `String` buffer. The
//! `*_to_ast` variants expose the command for callers that want to collect
//! a whole krate and pp at the end.

use std::collections::HashMap;
use vir::ast::*;
use crate::lean_ast::{
    and_all, Axiom, Binder as LBinder, BinderKind, Class, ClassMethod, Command, Datatype,
    DatatypeKind, Def, DefCurried, Expr as LExpr, ExprNode, Field, Instance,
    InstanceMethod, MatchArm, Pattern as LPattern, Theorem, Tactic, Variant,
};
use crate::to_lean_expr::vir_expr_to_ast;
use crate::to_lean_type::{lean_name, sanitize, short_name, typ_to_expr};

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
pub fn spec_fn_to_ast(f: &FunctionX) -> Command {
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
            let body = vir_expr_to_ast(b);
            let termination_by: Vec<LExpr> = f.decrease.iter().map(|d| vir_expr_to_ast(d)).collect();
            Command::Def(Def { attrs, name, binders, ret_ty, body, termination_by })
        }
        None => Command::Axiom(Axiom { name, binders, ret_ty }),
    }
}

// ── Proof fn ────────────────────────────────────────────────────────────

/// Build a `Theorem` AST node for a proof fn with the given tactic text.
pub fn proof_fn_to_ast(f: &FunctionX, tactic_body: &str) -> Theorem {
    let mut binders = fn_binders(f);
    for (i, req) in f.require.iter().enumerate() {
        binders.push(LBinder {
            name: Some(crate::lean_name::LeanName::synthetic(format!("h{}", i))),
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
        requires_preamble: Vec::new(),
        heartbeats: f.attrs.tactus_heartbeats,
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
    // Single-element SCC. The set's lifetime is tied to `dt`'s name
    // path; constructed locally because non-mutual datatypes never
    // cross outside their own SCC.
    let mut scc_paths: std::collections::HashSet<&Path> = std::collections::HashSet::new();
    if let Dt::Path(p) = &dt.name {
        scc_paths.insert(p);
    }
    let mut cmds = Vec::new();
    if let Some(decl) = datatype_decl_cmd(dt, &scc_paths) {
        cmds.push(decl);
    }
    if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths) {
        cmds.push(inst);
    }
    cmds.extend(datatype_accessor_cmds(dt, emit_accessors));
    if let Some(height) = datatype_height_cmd(dt, &scc_paths) {
        cmds.push(height);
    }
    cmds
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
) -> Vec<Command> {
    use crate::dep_order::DatatypeGroup;
    let dts: Vec<&'a DatatypeX> = match group {
        DatatypeGroup::Single(dt) => return datatype_to_cmds(dt, emit_accessors),
        DatatypeGroup::Mutual(dts) => dts.clone(),
    };

    // Build the SCC path set once for all members of the group.
    let scc_paths: std::collections::HashSet<&Path> = dts.iter()
        .filter_map(|dt| match &dt.name {
            Dt::Path(p) => Some(p),
            Dt::Tuple(_) => None,
        })
        .collect();

    let mut cmds = Vec::new();

    // 1. mutual block of inductives.
    let inductive_cmds: Vec<Command> = dts.iter()
        .filter_map(|dt| datatype_decl_cmd(dt, &scc_paths))
        .collect();
    cmds.push(Command::Mutual(inductive_cmds));

    // 1b. Manual `Inhabited` instances for any indexed-style members of
    // the SCC (Lean rejects `deriving Inhabited` on indexed inductives).
    // Emitted OUTSIDE the mutual block — Lean's instance system can
    // resolve cross-references to types declared earlier in the file
    // (the mutual block above) without needing the instance itself to
    // be inside it.
    for dt in &dts {
        if let Some(inst) = datatype_inhabited_instance_cmd(dt, &scc_paths) {
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
    let derives = if cross_inst { vec![] } else { vec!["Inhabited".into()] };
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
/// handles those) and for tuple datatypes (no decl).
fn datatype_inhabited_instance_cmd(
    dt: &DatatypeX,
    scc_paths: &std::collections::HashSet<&Path>,
) -> Option<Command> {
    if !has_cross_instantiation_recursion(dt, scc_paths) {
        return None;
    }
    let path = match &dt.name {
        Dt::Path(p) => lean_name(p),
        Dt::Tuple(_) => return None,
    };
    // Find a base constructor — a variant whose fields don't reference any
    // datatype in the SCC. Such a variant always exists for any
    // Rust-constructible enum (otherwise the datatype is uninhabited).
    let base_variant = dt.variants.iter().find(|v| {
        v.fields.iter().all(|f| field_recursive_target(&f.a.0, scc_paths).is_none())
    })?;

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
        // (binder name, height fn name) for each recursive field.
        // The height fn name uses the FIELD's datatype (which is in
        // the SCC), not the parent's. For self-recursion these
        // match; for mutual recursion across an SCC they differ.
        let mut recursive_binders: Vec<(String, String)> = Vec::new();
        for (idx, f) in v.fields.iter().enumerate() {
            if let Some(target_path) = field_recursive_target(&f.a.0, scc_paths) {
                let name = format!("_rec_{}", idx);
                let height_fn = format!("{}.height", lean_name(target_path));
                pats.push(LPattern::Var(crate::lean_name::LeanName::synthetic(name.clone())));
                recursive_binders.push((name, height_fn));
            } else {
                pats.push(LPattern::Wildcard);
            }
        }
        let mut arm_body = LExpr::lit_int("1");
        for (name, height_fn) in &recursive_binders {
            arm_body = LExpr::add(
                arm_body,
                LExpr::app1(
                    LExpr::var_synthetic(height_fn.clone()),
                    LExpr::var_synthetic(name.clone()),
                ),
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
        // Class-method default body, when the trait provides one.
        // Renders as `fun (p₁ : _) (p₂ : _) … => body` so Lean infers
        // each param type from the method signature. For zero-param
        // methods, just the body. Used by empty impls (`impl Tr for
        // T {}`) which inherit the default — those instances omit
        // the method, and Lean dispatches via this default.
        //
        // Proof-fn trait method defaults are NOT properly handled —
        // see DESIGN.md "Proof-fn trait method defaults UNTESTED"
        // entry. The body's tactic text would be rendered as a
        // value expression here, which is structurally wrong. No
        // tests exercise this combination today.
        let default = func.body.as_ref().map(|b| {
            let body_expr = vir_expr_to_ast(b);
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
        let termination_by: Vec<LExpr> = func.decrease.iter()
            .map(|d| vir_expr_to_ast(d))
            .collect();
        ClassMethod {
            name: sanitize(short),
            ty: method_type(func),
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

/// Build the method type `Self → P₁ → … → Ret`. Inside a class, associated
/// types become unqualified identifiers (they're class type params), so a
/// `TypX::Projection { name, … }` renders as just the projection name.
fn method_type(func: &FunctionX) -> LExpr {
    let param_type = |p: &vir::ast::Param| -> LExpr {
        if p.x.name.0.as_str() == "self" {
            LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Self")))
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
        LExpr::new(ExprNode::Var(crate::lean_name::LeanName::synthetic(sanitize(name))))
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
            name: Some(crate::lean_name::LeanName::lit(tp.as_str())),
            ty: LExpr::new(ExprNode::Var(crate::lean_name::LeanName::lit("Type"))),
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
    // Note: if the trait method has NO default body AND the impl
    // also has body=None, that's a structurally invalid state
    // (Verus would have rejected the impl as missing a required
    // method) — skipping is still safe because Lean would catch
    // the missing-method-in-instance error directly.
    let methods = method_impls.iter()
        .filter_map(|func| {
            let body = func.body.as_ref()?;
            let short = func.name.path.segments.last()
                .map(|s| s.as_str()).unwrap_or("_");
            let ast_body = vir_expr_to_ast(body);
            let lambda = if func.params.is_empty() {
                ast_body
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
                    body: Box::new(ast_body),
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
            ty: typ_to_expr(&p.x.typ),
            kind: BinderKind::Explicit,
        });
        if include_bound_hyps {
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
