//! Translate VIR types to `lean_ast::Expr` (in Lean, types are expressions).

use vir::ast::{Dt, IntRange, Path, Typ, TypDecoration, TypX};
use crate::lean_ast::{BinOp, Expr, ExprNode};
use crate::lean_name::LeanName;

/// Canonical VIR-type → Lean-AST translator.
pub fn typ_to_expr(typ: &TypX) -> Expr {
    Expr::new(typ_to_node(typ))
}

/// Render a fn parameter's type at the Lean theorem-binder level,
/// uniformly wrapping `&mut` references through `Tactus.MutRef`
/// regardless of which Verus mode produced the param.
///
/// Verus represents `&mut T` params in two distinct shapes depending
/// on mode:
/// * Legacy mode (default): `is_mut: true`, typ = plain `T`.
/// * New-mut-ref mode: `is_mut: false`, typ = `TypX::MutRef(T)`.
///
/// The new-mode shape's `TypX::MutRef` arm of `typ_to_node` already
/// emits `Tactus.MutRef T`. For the legacy shape, the plain typ would
/// emit just `T` — we wrap it here so both modes converge at the
/// binder level. Downstream machinery (body-deref shadow, pre-state
/// capture, call-site substitution) then treats both modes uniformly.
///
/// `is_mut_ref_typ` (in `expr_shared`) is the canonical predicate.
pub(crate) fn param_binder_typ(typ: &Typ, is_mut: bool) -> Expr {
    let rendered = typ_to_expr(typ);
    // If typ already renders through a MutRef wrapper (new mode or
    // decorated shape), no extra wrap needed.
    let already_wrapped = matches!(
        &**typ,
        TypX::MutRef(_) | TypX::Decorate(TypDecoration::MutRef, _, _)
    );
    if is_mut && !already_wrapped {
        Expr::new(ExprNode::App {
            head: Box::new(Expr::new(ExprNode::Var(LeanName::lit("Tactus.MutRef")))),
            args: vec![rendered],
        })
    } else {
        rendered
    }
}

/// True when `typ` is the unit type (`()` in Verus). After
/// `ast_simplify`, tuple types are represented as
/// `TypX::Datatype(Dt::Tuple(n), ...)` — the 0-arity tuple is unit.
///
/// Used to discriminate unit-return proof fns (the common case — pure
/// lemma) from value-returning proof fns (the "extract a witness"
/// shape, which needs subtype rendering for the class method type).
/// Lives in `to_lean_type.rs` rather than `to_lean_fn.rs` because both
/// `to_lean_fn` and `dep_order` need to discriminate the same way; a
/// shared helper avoids subtle drift in what counts as "unit" across
/// the two paths.
pub(crate) fn is_unit_typ(typ: &TypX) -> bool {
    matches!(typ, TypX::Datatype(Dt::Tuple(0), _, _))
}

/// Peel `TypX::Boxed` (poly coercion) and `TypX::Decorate` (Rust
/// decorations like `Box<T>`, `&T`, `&mut T`) to reach the
/// underlying type. These are transparent at the Lean level —
/// `typ_to_expr` also peels both — so multiple distinct checks
/// (is-int, is-user-datatype, is-self-referential-field) share
/// this helper. Single edit site if Verus adds a new transparent
/// wrapper.
pub(crate) fn peel_typ_wrappers(typ: &Typ) -> &Typ {
    match &**typ {
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => peel_typ_wrappers(inner),
        _ => typ,
    }
}

fn typ_to_node(typ: &TypX) -> ExprNode {
    // Helper: build `App { head: Var(LeanName::lit(name)), args }`.
    // Type-position names (`Int`, `Prop`, `Array`, etc.) are hardcoded
    // Lean type constructors — the `lit` constructor is correct here.
    let applied = |name: &str, args: Vec<Expr>| {
        if args.is_empty() {
            ExprNode::Var(LeanName::lit(name))
        } else {
            ExprNode::App {
                head: Box::new(Expr::new(ExprNode::Var(LeanName::lit(name)))),
                args,
            }
        }
    };
    let lit_var = |s: &str| ExprNode::Var(LeanName::lit(s));
    match typ {
        TypX::Bool => lit_var("Prop"),
        TypX::Int(range) => lit_var(match range {
            // Fixed-width u-types and i-types render as `Int` so that
            // their spec-mode subtraction is mathematical (can go
            // negative); `HasType` bounds then catch underflow.
            IntRange::Int | IntRange::I(_) | IntRange::ISize
            | IntRange::U(_) => "Int",
            // `nat` maps directly to Lean `Nat` — matching semantics.
            // `USize` stays `Nat` too (rather than `Int`) because
            // Verus elides `as nat` casts from `usize` in spec
            // contexts — const-generic bodies like `N as nat`
            // render as just `N`, so the param's Lean type has to
            // BE `Nat` or we get a type mismatch. Same reason for
            // `Char`. The upper bound still gets emitted via the
            // `usize_hi` prelude axiom in `type_bound_predicate`;
            // the subtraction-truncation risk that motivated u8→Int
            // exists here but is rare in practice for usize and
            // accepted as a known gap pending a deeper fix.
            IntRange::Nat | IntRange::USize | IntRange::Char => "Nat",
        }),
        // Type parameter names are user-named generic params (`A`, `T`,
        // etc.) — already valid identifiers — EXCEPT the trait `Self`
        // param, which arrives as `"Self%"` and must normalize to `Self`.
        // `LeanName::typ_param` handles both.
        TypX::TypParam(name) => ExprNode::Var(LeanName::typ_param(name.as_str())),
        TypX::Boxed(inner) => typ_to_node(inner),
        TypX::MutRef(inner) => {
            // New-mut-ref-mode shape (`TypX::MutRef`, distinct from the
            // legacy `Decorate(MutRef, _, _)`). Render through the same
            // wrapper as legacy mode for uniformity.
            applied("Tactus.MutRef", vec![typ_to_expr(inner)])
        }
        TypX::Datatype(dt, args, _) => match dt {
            Dt::Path(path) => applied(&lean_name(path), args.iter().map(|a| typ_to_expr(a)).collect()),
            // Anonymous Rust tuple → Lean product type `T₁ × T₂ × … × Tₙ`.
            // Zero-element → `Unit`; single-element → the element itself
            // (Verus doesn't produce 1-tuples, but handle it defensively).
            Dt::Tuple(_) => match args.len() {
                0 => lit_var("Unit"),
                1 => typ_to_node(&args[0]),
                _ => {
                    let mut iter = args.iter().rev();
                    let mut acc = typ_to_expr(iter.next().unwrap());
                    for a in iter {
                        acc = Expr::new(ExprNode::BinOp {
                            op: BinOp::Prod,
                            lhs: Box::new(typ_to_expr(a)),
                            rhs: Box::new(acc),
                        });
                    }
                    acc.node
                }
            },
        },
        TypX::SpecFn(params, ret) => {
            // Fold params right-to-left into nested → so the AST reflects
            // Lean's right-associative arrow.
            let mut out = typ_to_expr(ret);
            for p in params.iter().rev() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Implies,
                    lhs: Box::new(typ_to_expr(p)),
                    rhs: Box::new(out),
                });
            }
            out.node
        }
        TypX::Decorate(deco, _, inner) => {
            // Reference-like decorations preserve type identity at the
            // Lean level so trait dispatch can distinguish `Ref A` from
            // `A`. Verus's Z3 path handles this via DECORATE=true type-IDs
            // in `sst_to_air::monotyp_to_id` (two-component `(REF, basic
            // A)` vs `(NIL_SIZED, basic A)`). Lean has no separate type-
            // ID channel; we use real distinct opaque types from the
            // prelude.
            //
            // Other decorations (Ghost, Tracked, Never, ConstPtr) stay
            // transparent — they're verification metadata or zero-cost
            // markers, not types user code observes at the spec level.
            use vir::ast::TypDecoration;
            match deco {
                TypDecoration::Ref => applied("Tactus.Ref", vec![typ_to_expr(inner)]),
                TypDecoration::MutRef => applied("Tactus.MutRef", vec![typ_to_expr(inner)]),
                TypDecoration::Box => applied("Tactus.Box", vec![typ_to_expr(inner)]),
                TypDecoration::Rc => applied("Tactus.Rc", vec![typ_to_expr(inner)]),
                TypDecoration::Arc => applied("Tactus.Arc", vec![typ_to_expr(inner)]),
                TypDecoration::Ghost | TypDecoration::Tracked
                | TypDecoration::Never | TypDecoration::ConstPtr => typ_to_node(inner),
            }
        }
        TypX::Projection { trait_typ_args, trait_path, name } => {
            // <Self as Trait>::AssocType → Trait.AssocType Self …
            let head = format!("{}.{}", lean_name(trait_path), name);
            applied(&head, trait_typ_args.iter().map(|t| typ_to_expr(t)).collect())
        }
        TypX::Primitive(prim, args) => {
            let head = match prim {
                // Verus's `[T; N]` carries `[T, N]` as args (element
                // type + const-length). Lean core's `Vector α n`
                // (4.25) is exactly the length-indexed array, so both
                // args render — instances like vstd's `View for
                // [T; N]` (whose `array_view` needs N) bind the
                // length from the type head
                // (BUG-vstd-preamble-cluster.md bug 2). The length
                // slot is a `ConstInt` (literal) or a const-generic
                // `TypParam` (binder), both of which `typ_to_expr`
                // renders natively.
                vir::ast::Primitive::Array => "Vector",
                vir::ast::Primitive::Slice => "List",
                vir::ast::Primitive::StrSlice => "String",
                vir::ast::Primitive::Ptr => "USize",
                vir::ast::Primitive::Global => "Unit",
            };
            // Slice carries just `[T]`; take(1) defensively.
            let type_args: Vec<_> = match prim {
                vir::ast::Primitive::Slice => {
                    args.iter().take(1).map(|a| typ_to_expr(a)).collect()
                }
                _ => args.iter().map(|a| typ_to_expr(a)).collect(),
            };
            applied(head, type_args)
        }
        TypX::ConstInt(n) => ExprNode::Lit(n.to_string()),
        TypX::ConstBool(b) => lit_var(if *b { "true" } else { "false" }),
        TypX::Real => lit_var("Real"),
        TypX::Float(_) => lit_var("Float"),
        TypX::TypeId => lit_var("Nat"),
        TypX::FnDef(_, typs, _) => {
            // Zero-sized identifier type → `Unit` (possibly paired with
            // extra type args for disambiguation as `Unit × T₁ × T₂ …`).
            // `×` is right-associative, so folding from the right gives
            // the pp the shape Lean expects without defensive parens.
            let mut out = Expr::new(lit_var("Unit"));
            for t in typs.iter() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Prod,
                    lhs: Box::new(out),
                    rhs: Box::new(typ_to_expr(t)),
                });
            }
            out.node
        }
        TypX::AnonymousClosure(params, ret, _, _) => {
            let mut out = typ_to_expr(ret);
            for p in params.iter().rev() {
                out = Expr::new(ExprNode::BinOp {
                    op: BinOp::Implies,
                    lhs: Box::new(typ_to_expr(p)),
                    rhs: Box::new(out),
                });
            }
            out.node
        }
        TypX::Dyn(path, args, _) => {
            applied(&lean_name(path), args.iter().map(|a| typ_to_expr(a)).collect())
        }
        TypX::Opaque { def_path, args } => {
            applied(&lean_name(def_path), args.iter().map(|a| typ_to_expr(a)).collect())
        }
        TypX::PointeeMetadata(_) => lit_var("Nat"),
        TypX::Air(_) => panic!("TypX::Air should not appear in Tactus translation"),
    }
}

/// Get the short name (last path segment) from a VIR path.
pub(crate) fn short_name(path: &Path) -> &str {
    path.segments.last().map(|s| s.as_str()).unwrap_or("_")
}

/// Derive a single-segment "type name" suitable for use as a Lean
/// namespace prefix, peeling transparent decoration. Returns `None`
/// for shapes without an obvious type name (closures, anonymous
/// tuples, primitives without a clean ID), in which case the impl-
/// method naturalisation should fall back to the synthetic
/// `impl__N` form.
///
/// Used by `impl_subst::set_method_context` to compute the natural
/// name `<self>.<trait>.<method>` for impl method standalone defs.
pub(crate) fn type_short_name(typ: &vir::ast::Typ) -> Option<String> {
    use vir::ast::TypX;
    let mut cur = typ.clone();
    loop {
        match &*cur.clone() {
            TypX::Decorate(_, _, inner) | TypX::Boxed(inner)
            | TypX::MutRef(inner) => cur = inner.clone(),
            TypX::Datatype(dt, _, _) => return match dt {
                vir::ast::Dt::Path(p) => Some(short_name(p).to_string()),
                vir::ast::Dt::Tuple(_) => None,
            },
            TypX::Primitive(p, _) => return Some(match p {
                vir::ast::Primitive::Array => "Vector".to_string(),
                vir::ast::Primitive::Slice => "Slice".to_string(),
                vir::ast::Primitive::StrSlice => "StrSlice".to_string(),
                vir::ast::Primitive::Ptr => "Ptr".to_string(),
                vir::ast::Primitive::Global => "Global".to_string(),
            }),
            TypX::TypParam(name) => return Some(name.as_str().to_string()),
            TypX::Dyn(p, _, _) | TypX::Opaque { def_path: p, .. } =>
                return Some(short_name(p).to_string()),
            TypX::Int(_) | TypX::Bool | TypX::Real | TypX::Float(_)
            | TypX::TypeId | TypX::ConstInt(_) | TypX::ConstBool(_)
            | TypX::SpecFn(..) | TypX::AnonymousClosure(..) | TypX::FnDef(..)
            | TypX::PointeeMetadata(_) | TypX::Air(_) | TypX::Projection { .. } =>
                return None,
        }
    }
}

thread_local! {
    /// Naturalized names for inherent impl methods, keyed by their raw
    /// path-derived name (`impl__0.view`) → the type-qualified form
    /// (`Holder.view`). Verus gives an inherent method an anonymous
    /// impl-block path (`impl&%0::view`) with no type segment, so the
    /// bare `lean_name` of it is the unstable, un-referenceable
    /// `impl__0.view`. Built once per render from the krate (see
    /// `generate::install_inherent_method_renames`) — where the
    /// `FunctionX` is in scope to recover the Self type from the receiver
    /// — and consulted at the single `lean_name` chokepoint so the
    /// standalone def AND every call site (VIR + SST) naturalize to the
    /// same name. Mirrors what trait-impl methods get from
    /// `set_method_context` (`Bar.Foo.impl.predicate`).
    static INHERENT_METHOD_RENAMES: std::cell::RefCell<std::collections::HashMap<String, String>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Install the inherent-method rename table (see `INHERENT_METHOD_RENAMES`).
/// Called at each per-fn render entry, where the krate is in scope.
pub(crate) fn set_inherent_method_renames(map: std::collections::HashMap<String, String>) {
    INHERENT_METHOD_RENAMES.with(|m| *m.borrow_mut() = map);
}

/// Raw path → Lean dotted name, BEFORE the inherent-method-rename
/// consult. Used both by `lean_name` (which then consults the table) and
/// by the table builder (to compute each entry's key without recursing
/// through the table).
pub(crate) fn lean_name_raw(path: &Path) -> String {
    // Sanitize every segment, including synthetic impl markers
    // (`impl&%0` → `impl__0`). The markers are load-bearing for
    // disambiguation: multiple impls of the same trait method would
    // otherwise collide on the bare method name (keeping them gives
    // `impl__0.is_zero` / `impl__1.is_zero` — uglier but unique). The
    // inherent-method rename in `lean_name` naturalizes the common case
    // (`impl__0.view` → `Holder.view`); names not in that table keep the
    // disambiguated marker form.
    let segments: Vec<String> = path.segments.iter()
        .map(|s| sanitize(s))
        .collect();
    if segments.len() == 1 && !needs_sanitization(&path.segments[0]) {
        return path.segments[0].to_string();
    }
    segments.join(".")
}

thread_local! {
    /// Namespace of the crate currently being emitted — `sanitize(crate_name)`,
    /// the same string `NamespaceOpen` wraps every emitted file in. Installed
    /// by `generate::install_emit_tables` (all emission entry points route
    /// through it). When set, `lean_name` renders **root-anchored** names
    /// (`_root_.{ns}.{name}`) so a local binder can never capture an emitted
    /// global — a Verus local named `symbol` used to turn every reference
    /// `symbol.generator_index` into a dot-notation field lookup on the
    /// binder's type ("Invalid field", 2,203 errors crate-wide on
    /// tactus-group-theory; DESIGN-lean-all-proofs-bugs.md B1a).
    ///
    /// Root-anchoring is valid in *declaration* position too (`def
    /// _root_.lib.foo.bar` inside `namespace lib` declares `lib.foo.bar`,
    /// same as the relative form — verified empirically for def / inductive
    /// + deriving / axiom / match-pattern positions), so `lean_name` applies
    /// it uniformly. Non-Lean-text uses of the name (the `.lean` filename)
    /// use `lean_name_relative`.
    ///
    /// `None` (unit tests, prelude-free fragments) falls back to relative
    /// names — the pre-B1a behavior.
    static CRATE_NS: std::cell::RefCell<Option<String>> = std::cell::RefCell::new(None);
}

/// Install the current crate namespace for root-anchored name rendering.
/// Called by `generate::install_emit_tables` — never call directly, so the
/// ambient emit state can't be half-installed.
pub(crate) fn install_crate_ns(crate_name: &str) {
    CRATE_NS.with(|n| *n.borrow_mut() = Some(sanitize(crate_name)));
}

thread_local! {
    /// Relative Lean names (`lean_name_relative` form) of every decl this
    /// crate's emission can produce — fns, datatypes, traits. Decides which
    /// root-anchor a reference gets: declared here → `_root_.{ns}.{name}`
    /// (it lives inside the file's `namespace` wrapper); NOT declared here →
    /// `_root_.{name}` (a Lean-core / prelude name such as `Nonempty`,
    /// which a synthetic VIR path renders — path shape alone can't
    /// distinguish it from a crate-root fn, so membership is the criterion).
    /// Both forms are capture-proof against local binders; the second
    /// preserves what namespace-climbing used to resolve, minus the capture
    /// risk.
    static CRATE_DECLS: std::cell::RefCell<Option<std::sync::Arc<std::collections::HashSet<String>>>> =
        std::cell::RefCell::new(None);
}

/// Install the crate-declared name set (see `CRATE_DECLS`). Called by
/// `generate::install_emit_tables` AFTER the inherent-method rename table —
/// the set stores naturalized names, so it must be built with the renames
/// already in place.
pub(crate) fn install_crate_decls(decls: std::sync::Arc<std::collections::HashSet<String>>) {
    CRATE_DECLS.with(|d| *d.borrow_mut() = Some(decls));
}

thread_local! {
    /// Relative names of the decl group whose bodies are currently being
    /// rendered. A recursive def's SELF-reference (and a `mutual` block
    /// member's reference to its siblings) must render relatively: during
    /// elaboration the decl is not yet a global constant, and `_root_.…`
    /// forces global lookup — `Unknown identifier` (verified empirically).
    /// Lean resolves the relative form through its local self-reference /
    /// mutual-group mechanism. For datatype `.height` defs the set holds
    /// the datatype's relative name (the `.height` suffix is appended
    /// after `lean_name` returns). Residual risk, accepted: a local binder
    /// shadowing a self-name's head segment inside its own recursive def —
    /// vanishingly rare vs. the systematic breakage.
    static CURRENT_DECL_SELF: std::cell::RefCell<std::collections::HashSet<String>> =
        std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Render `f` with `rel_names` ADDED to the current self-decl set (see
/// `CURRENT_DECL_SELF`), restoring the previous set afterwards. Union
/// scoping: `spec_fn_to_ast` pushes its own singleton inside the mutual
/// group's wrapper — member bodies must still resolve their siblings.
///
/// Restore is a Drop guard: renders DO panic and ARE recovered
/// (`push_lenient` / `guard_build` catch_unwind) — without the guard, a
/// panic inside `f` would leak the names into the thread-local for the
/// rest of the thread's life, making later same-thread renders emit
/// those names relative and silently resurrecting the B1a capture bug.
/// `clear_self_decls` in `install_emit_tables` is the belt to this
/// suspenders.
pub(crate) fn with_self_decls<T>(
    rel_names: impl IntoIterator<Item = String>,
    f: impl FnOnce() -> T,
) -> T {
    struct Restore {
        added: Vec<String>,
    }
    impl Drop for Restore {
        fn drop(&mut self) {
            CURRENT_DECL_SELF.with(|s| {
                let mut set = s.borrow_mut();
                for n in &self.added {
                    set.remove(n);
                }
            });
        }
    }
    let _restore = Restore {
        added: CURRENT_DECL_SELF.with(|s| {
            let mut set = s.borrow_mut();
            rel_names.into_iter().filter(|n| set.insert(n.clone())).collect()
        }),
    };
    f()
}

/// Reset the self-decl set. Called by `generate::install_emit_tables` at
/// every emission entry point — a fresh emission must never inherit
/// leaked self-names from a panicked-and-recovered render on this thread.
pub(crate) fn clear_self_decls() {
    CURRENT_DECL_SELF.with(|s| s.borrow_mut().clear());
}

/// Single-name convenience for `with_self_decls`.
pub(crate) fn with_self_decl<T>(rel_name: String, f: impl FnOnce() -> T) -> T {
    with_self_decls(std::iter::once(rel_name), f)
}

/// Convert a VIR path to a Lean dotted name, skipping the crate prefix.
/// `crate::module::name` → `module.name`
/// Names are sanitized (@ # → _) and keywords are escaped with «».
/// Inherent impl method names are naturalized (`impl__0.view` →
/// `Holder.view`) via the `INHERENT_METHOD_RENAMES` table.
/// With a crate namespace installed, the result is root-anchored:
/// `_root_.{ns}.module.name` (see `CRATE_NS`).
pub(crate) fn lean_name(path: &Path) -> String {
    let name = lean_name_relative(path);
    // Self-reference inside the decl group's own bodies: must stay
    // relative (see CURRENT_DECL_SELF — root-anchoring a not-yet-defined
    // global is `Unknown identifier`).
    let is_self = CURRENT_DECL_SELF.with(|s| s.borrow().contains(name.as_str()));
    if is_self {
        return name;
    }
    CRATE_NS.with(|ns| match &*ns.borrow() {
        Some(ns) => {
            let in_crate = CRATE_DECLS.with(|d| match &*d.borrow() {
                Some(decls) => decls.contains(&name),
                // Set not installed but ns is — shouldn't happen (same
                // installer); treat as crate-internal, the common case.
                None => true,
            });
            if in_crate {
                format!("_root_.{}.{}", ns, name)
            } else {
                format!("_root_.{}", name)
            }
        }
        None => name,
    })
}

/// `lean_name` without the root-anchor — the name relative to the emitted
/// file's `namespace` wrapper. For uses where the name is an artifact key,
/// not Lean text: the per-fn `.lean` filename (`generate::lean_file_path`).
pub(crate) fn lean_name_relative(path: &Path) -> String {
    let name = lean_name_raw(path);
    // Only inherent impl methods get a rename; gate the table lookup on
    // the cheap marker check so the common (non-impl) path stays alloc-free.
    if name.contains("impl__") {
        if let Some(nat) = INHERENT_METHOD_RENAMES.with(|m| m.borrow().get(&name).cloned()) {
            return nat;
        }
    }
    name
}

fn needs_sanitization(s: &str) -> bool {
    is_lean_keyword(s) || s.bytes().any(|b|
        b == b'@' || b == b'#' || b == b'%' || b == b'&'
    )
}

/// Make a raw identifier safe to emit as a Lean identifier: keyword-quote
/// with `«…»` if it collides with a Lean reserved word, otherwise squash
/// Verus-internal punctuation to `_`:
/// * `%` from `assert(P)` desugaring
/// * `@` / `#` from VIR disambiguation
/// * `&` from synthetic impl markers (`impl&%0` → `impl__0`)
///
/// No-op fast path for the common case of already-safe names.
pub(crate) fn sanitize(s: &str) -> String {
    if !needs_sanitization(s) {
        return s.to_string();
    }
    if is_lean_keyword(s) {
        format!("«{}»", s)
    } else {
        s.chars().map(|c| match c { '@' | '#' | '%' | '&' => '_', _ => c }).collect()
    }
}

/// Identifier-like reserved tokens of the Lean environment that emitted
/// files see (`import TactusPrelude`, Lean v4.25.0 toolchain). An
/// identifier-like string in Lean's token table is lexed as a keyword atom,
/// not an identifier, so any of these appearing raw in binder/reference
/// position is a parse error — `sanitize` «»-quotes them.
///
/// GENERATED — do not hand-edit beyond the documented exceptions. Regenerate
/// with `tactus/source/lean_verify/dump_reserved_tokens.lean` (usage in its
/// header) after a toolchain bump or new identifier-like syntax in
/// TactusPrelude. Exceptions to the raw dump:
/// * `_` (in the token table) is EXCLUDED: quoting «_» would turn a
///   wildcard binder into a named binder.
/// * `lemma` (Mathlib-only, not in TactusPrelude's import closure) is
///   INCLUDED defensively — it was quoted historically and Mathlib-importing
///   contexts (tutorial helpers) may see it reserved.
///
/// Sorted for `binary_search`; a unit test in `tests/lean_name.rs` enforces
/// sortedness.
pub(crate) const LEAN_RESERVED_TOKENS: &[&str] = &[
    "Prop", "Sort", "StateRefT", "Type",
    "abbrev", "add_decl_doc", "at", "attribute",
    "axiom", "bif", "binder_predicate", "break",
    "builtin_dsimproc", "builtin_dsimproc_decl", "builtin_grind_propagator", "builtin_initialize",
    "builtin_simproc", "builtin_simproc_decl", "by", "by_elab",
    "calc", "catch", "class", "coinductive",
    "coinductive_fixpoint", "continue", "dbg_trace", "declare_bitwise_int_theorems",
    "declare_bitwise_uint_theorems", "declare_command_config_elab", "declare_config_elab", "declare_int_theorems",
    "declare_simp_like_tactic", "declare_sint_simprocs", "declare_syntax_cat", "declare_uint_simprocs",
    "declare_uint_theorems", "decreasing_by", "def", "deriving",
    "do", "docs_to_verso", "dsimproc", "dsimproc_decl",
    "elab", "elab_rules", "elab_stx_quot", "else",
    "end", "eval_prec", "eval_prio", "example",
    "exists", "export", "extends", "finally",
    "for", "forall", "from", "fun",
    "generalizing", "grind_pattern", "grind_propagator", "have",
    "haveI", "hiding", "if", "import",
    "in", "include", "include_str", "inductive",
    "inductive_fixpoint", "infix", "infixl", "infixr",
    "init_grind_norm", "init_quot", "initialize", "instance",
    "leading_parser", "lemma", "let", "letI",
    "let_delayed", "let_expr", "let_fun", "let_tmp",
    "local", "logNamedError", "logNamedErrorAt", "logNamedWarning",
    "logNamedWarningAt", "macro", "macro_rules", "match",
    "match_expr", "matches", "max_prec", "meta",
    "mod_cast", "mut", "mutual", "namespace",
    "nat_lit", "no_index", "nofun", "nomatch",
    "noncomputable", "nonrec", "norm_cast_add_elim", "notation",
    "omit", "opaque", "open", "partial",
    "partial_fixpoint", "postfix", "prefix", "private",
    "protected", "public", "recommended_spelling", "register_builtin_option",
    "register_error_explanation", "register_label_attr", "register_linter_set", "register_option",
    "register_parser_alias", "register_simp_attr", "register_tactic_tag", "renaming",
    "repeat", "reprove", "return", "run_cmd",
    "run_elab", "run_meta", "scoped", "seal",
    "section", "set_option", "set_premise_selector", "show",
    "show_panel_widgets", "show_term", "show_term_elab", "simproc",
    "simproc_decl", "sorry", "structure", "suffices",
    "syntax", "tactic_alt", "tactic_extension", "tactic_tag",
    "termination_by", "test_extern", "then", "theorem",
    "throwError", "throwErrorAt", "throwNamedError", "throwNamedErrorAt",
    "trailing_parser", "try", "unif_hint", "universe",
    "unless", "unsafe", "unseal", "until",
    "using", "variable", "where", "while",
    "with", "with_annotate_term", "without_expected_type",
];

pub(crate) fn is_lean_keyword(s: &str) -> bool {
    LEAN_RESERVED_TOKENS.binary_search(&s).is_ok()
}

/// Walk a TypX recursively, calling `visit` at each node.
/// Preserves the input lifetime `'a` so callers can borrow from the AST.
pub(crate) fn walk_typ<'a>(typ: &'a TypX, visit: &mut impl FnMut(&'a TypX)) {
    visit(typ);
    match typ {
        TypX::Datatype(_, args, _) => {
            for arg in args.iter() { walk_typ(arg, visit); }
        }
        TypX::Boxed(inner) | TypX::Decorate(_, _, inner) => walk_typ(inner, visit),
        TypX::SpecFn(params, ret) => {
            for p in params.iter() { walk_typ(p, visit); }
            walk_typ(ret, visit);
        }
        _ => {}
    }
}

#[cfg(test)]
#[path = "tests/to_lean_type.rs"]
mod tests;
