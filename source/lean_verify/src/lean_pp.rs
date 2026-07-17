//! Pretty-printer for `lean_ast` nodes.
//!
//! Precedence is enforced at render time, not by callers. Every `write_expr`
//! call takes the *parent* precedence; children wrap themselves in parens
//! iff their own precedence is strictly lower. Associativity is encoded by
//! having left-/right-assoc operators pass `p` on the associative side and
//! `p + 1` on the other side, so same-precedence children don't parenthesize
//! when Lean would parse them correctly.
//!
//! Indentation is minimal — just enough for readability of multi-line
//! goals/bodies. Tactus-generated Lean is consumed by the kernel, not
//! reviewed by hand in the common case; debuggable on-disk artifacts are
//! about structure, not aesthetics.

use crate::lean_ast::*;

// ── Precedence ─────────────────────────────────────────────────────────
//
// Numbers roughly follow Lean 4's standard operator precedences. What
// matters is relative ordering, not the absolute number.

const PREC_IFF: u16 = 20;
const PREC_IMPLIES: u16 = 25;
const PREC_OR: u16 = 30;
const PREC_AND: u16 = 35;
const PREC_NOT: u16 = 40;
const PREC_CMP: u16 = 50;
const PREC_ADD: u16 = 65;
const PREC_MUL: u16 = 70;
const PREC_PROD: u16 = 35;
const PREC_APP: u16 = 1024;
const PREC_ATOM: u16 = u16::MAX;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Assoc { Left, Right, None_ }

fn binop_info(op: BinOp) -> (u16, Assoc) {
    match op {
        BinOp::Iff => (PREC_IFF, Assoc::Right),
        BinOp::Implies => (PREC_IMPLIES, Assoc::Right),
        BinOp::Or => (PREC_OR, Assoc::Right),
        BinOp::And => (PREC_AND, Assoc::Right),
        BinOp::Eq | BinOp::Ne
        | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => (PREC_CMP, Assoc::None_),
        BinOp::Add | BinOp::Sub => (PREC_ADD, Assoc::Left),
        BinOp::Mul | BinOp::Div | BinOp::Mod => (PREC_MUL, Assoc::Left),
        // Bitwise: Lean uses custom operators at ~65/70 range.
        BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => (PREC_ADD, Assoc::Left),
        BinOp::Shr | BinOp::Shl => (PREC_ADD, Assoc::Left),
        // Lean's `×` is right-associative at 35 (same prec as `∧`).
        BinOp::Prod => (PREC_PROD, Assoc::Right),
    }
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::And => "∧",
        BinOp::Or => "∨",
        BinOp::Implies => "→",
        BinOp::Iff => "↔",
        BinOp::Eq => "=",
        BinOp::Ne => "≠",
        BinOp::Lt => "<",
        BinOp::Le => "≤",
        BinOp::Gt => ">",
        BinOp::Ge => "≥",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::BitAnd => "&&&",
        BinOp::BitOr => "|||",
        BinOp::BitXor => "^^^",
        BinOp::Shr => ">>>",
        BinOp::Shl => "<<<",
        BinOp::Prod => "×",
    }
}

fn expr_prec(node: &ExprNode) -> u16 {
    match node {
        ExprNode::Var(_) | ExprNode::Lit(_) | ExprNode::LitBool(_)
        | ExprNode::LitStr(_) | ExprNode::LitChar(_)
        | ExprNode::ArrayLit(_) | ExprNode::VectorLit(_) | ExprNode::StructUpdate { .. }
        | ExprNode::Anon(_) | ExprNode::Tuple(_) | ExprNode::Raw(_)
        | ExprNode::ByBlock { .. } | ExprNode::Subtype { .. } => PREC_ATOM,
        ExprNode::FieldProj { .. } | ExprNode::Index { .. } => PREC_ATOM,
        // SpanMark is transparent — inherit `inner`'s precedence so
        // wrapping never changes parenthesization.
        ExprNode::SpanMark { inner, .. } => expr_prec(&inner.node),
        ExprNode::BinOp { op, .. } => binop_info(*op).0,
        ExprNode::UnOp { op: UnOp::Not, .. } => PREC_NOT,
        ExprNode::UnOp { op: UnOp::Neg, .. } => PREC_MUL + 1,
        ExprNode::UnOp { op: UnOp::BitNot, .. } => PREC_APP,
        ExprNode::App { args, .. } => if args.is_empty() { PREC_ATOM } else { PREC_APP },
        ExprNode::TypeAnnot { .. } => 0, // always parenthesized when inside anything
        ExprNode::If { .. } | ExprNode::Match { .. }
        | ExprNode::Let { .. } | ExprNode::Lambda { .. }
        | ExprNode::Forall { .. } | ExprNode::Exists { .. } => 0,
    }
}

// ── Public entry points ────────────────────────────────────────────────

/// Structural landmarks accumulated during emission. Populated
/// by `write_*` functions as they walk the AST.
pub struct Landmarks {
    /// For every `Tactic::Raw` body encountered (in source order): the
    /// 1-indexed line in `text` where the first character of the body
    /// appears. The proof-fn pipeline uses this to build a `LeanSourceMap`
    /// without having to scan the output for a marker string.
    pub tactic_starts: Vec<usize>,
    /// One per `ExprNode::SpanMark` visited during pp, in source
    /// order. Used by `LeanSourceMap` to map Lean error lines
    /// back to Rust source positions and obligation kinds (#51).
    pub span_marks: Vec<SpanMarkLandmark>,
    /// For every `Command::Theorem` (in source order): the 1-indexed
    /// line of its `theorem` keyword. Islands are structured preamble
    /// (classes/instances/defs) THEN theorems, so the FIRST entry
    /// splits emitter territory from user-proof territory — the
    /// island sorry gate keys on it (decl-head warning positions).
    pub theorem_heads: Vec<usize>,
}

/// Per-`SpanMark`-visit landmark. `line` is the 1-indexed Lean
/// line where the marked sub-expression starts; `loc` is the
/// pre-resolved Rust `file:line:col`; `rust_span` is the original
/// Verus `Span` of the obligation (cloned through codegen so the
/// verifier can attach errors directly at the obligation site
/// instead of the enclosing fn signature); `kind` is the
/// obligation's semantic class for error-message labeling.
#[derive(Debug, Clone)]
pub struct SpanMarkLandmark {
    pub line: usize,
    pub loc: String,
    pub rust_span: Option<vir::messages::Span>,
    pub kind: AssertKind,
}

impl Landmarks {
    fn new() -> Self {
        Landmarks { tactic_starts: Vec::new(), span_marks: Vec::new(), theorem_heads: Vec::new() }
    }
}

/// Pretty-print output plus structural landmarks accumulated during emission.
pub struct PpOutput {
    pub text: String,
    pub landmarks: Landmarks,
}

/// B5 (prelude split): if any theorem in `cmds` cites a search-ladder
/// tactic in its closer, the file needs `import TactusSearch`. Injected
/// here — the single chokepoint every artifact path flows through —
/// rather than at each emission site, so future paths can't forget.
/// Default emission never triggers (the S2c derived closer and B4's
/// explicit peel name no search tactics); only user tactic texts
/// (fn-level overrides, inline proofs) can. Cost is one scan plus a
/// command-list clone when it fires (rare); the injection lands before
/// landmark computation, so sourcemap alignment is preserved.
fn maybe_inject_search_import(cmds: &[Command]) -> std::borrow::Cow<'_, [Command]> {
    let needs = cmds.iter().any(|c| match c {
        Command::Theorem(t) => match &t.tactic {
            Tactic::Raw(s) | Tactic::Named(s) => crate::prelude::needs_search_import(s),
        },
        _ => false,
    });
    if !needs {
        return std::borrow::Cow::Borrowed(cmds);
    }
    let mut out = cmds.to_vec();
    // Insert after the leading import block — Lean requires all
    // `import` statements before any other command.
    let mut idx = 0;
    for (i, c) in out.iter().enumerate() {
        match c {
            Command::Import(_) => idx = i + 1,
            Command::Raw(s) if s.starts_with("import ") => idx = i + 1,
            _ => {}
        }
    }
    out.insert(idx, Command::Import("TactusSearch".to_string()));
    std::borrow::Cow::Owned(out)
}

pub fn pp_commands(cmds: &[Command]) -> PpOutput {
    let cmds = maybe_inject_search_import(cmds);
    let mut out = String::new();
    let mut lm = Landmarks::new();
    for cmd in cmds.iter() {
        write_command(&mut out, cmd, &mut lm);
    }
    PpOutput { text: out, landmarks: lm }
}

/// Render a single command. Discards any landmarks; use
/// `pp_commands` when you need them.
pub fn pp_command(cmd: &Command) -> String {
    let mut out = String::new();
    let mut lm = Landmarks::new();
    write_command(&mut out, cmd, &mut lm);
    out
}

pub fn pp_expr(e: &Expr) -> String {
    let mut out = String::new();
    let mut lm = Landmarks::new();
    write_expr(&mut out, e, 0, &mut lm);
    out
}

pub fn pp_pattern(p: &Pattern) -> String {
    let mut out = String::new();
    let mut lm = Landmarks::new();
    write_pattern(&mut out, p, &mut lm);
    out
}

/// Count `\n` bytes in the buffer. Cheap enough for the one-theorem-per-file
/// case we currently have; if we ever emit many theorems per file this is the
/// natural place to maintain a running counter instead.
fn current_line(out: &str) -> usize {
    1 + out.bytes().filter(|&b| b == b'\n').count()
}

/// Return the number of leading-space characters on the current
/// (last, unterminated) line of `out`. Used by `ByBlock` rendering
/// to compute the body indent relative to the surrounding context
/// (e.g., inside an instance method whose field declaration sits at
/// some indent, the `by` body must be indented past that).
///
/// Scans back from the end of `out` to the last `\n`; the line is
/// `out[last_newline+1..]`. Counts leading spaces only — tabs are
/// not used in Tactus's output.
fn current_line_indent(out: &str) -> usize {
    let line_start = out.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line = &out[line_start..];
    line.bytes().take_while(|&b| b == b' ').count()
}

// ── Command writers ─────────────────────────────────────────────────────

fn write_command(out: &mut String, cmd: &Command, lm: &mut Landmarks) {
    match cmd {
        Command::Raw(s) => {
            out.push_str(s);
            if !s.ends_with('\n') { out.push('\n'); }
        }
        Command::Import(path) => {
            out.push_str("import ");
            out.push_str(path);
            out.push('\n');
        }
        Command::SetOption { name, value } => {
            out.push_str("set_option ");
            out.push_str(name);
            out.push(' ');
            out.push_str(value);
            out.push('\n');
        }
        Command::NamespaceOpen(name) => {
            out.push_str("namespace ");
            out.push_str(name);
            out.push('\n');
        }
        Command::NamespaceClose(name) => {
            out.push_str("end ");
            out.push_str(name);
            out.push('\n');
        }
        Command::Mutual(cmds) => {
            out.push_str("mutual\n");
            for c in cmds { write_command(out, c, lm); }
            out.push_str("end\n\n");
        }
        Command::Def(d) => write_def(out, d, lm),
        Command::DefCurried(d) => write_def_curried(out, d, lm),
        Command::Axiom(a) => write_axiom(out, a, lm),
        Command::Theorem(t) => {
            lm.theorem_heads.push(current_line(out));
            write_theorem(out, t, lm)
        }
        Command::Datatype(dt) => write_datatype(out, dt, lm),
        Command::Class(c) => write_class(out, c, lm),
        Command::Instance(i) => write_instance(out, i, lm),
    }
}

fn write_axiom(out: &mut String, a: &Axiom, lm: &mut Landmarks) {
    if let Some(c) = &a.comment {
        out.push_str("-- ");
        out.push_str(c);
        out.push('\n');
    }
    for attr in &a.attrs {
        out.push_str("@[");
        out.push_str(attr);
        out.push_str("] ");
    }
    out.push_str("axiom ");
    out.push_str(&a.name);
    write_binders(out, &a.binders, lm);
    out.push_str(" : ");
    write_expr(out, &a.ret_ty, 0, lm);
    out.push('\n');
}

fn write_def_curried(out: &mut String, d: &DefCurried, lm: &mut Landmarks) {
    for attr in &d.attrs {
        out.push_str("@[");
        out.push_str(attr);
        out.push_str("] ");
    }
    out.push_str("noncomputable def ");
    out.push_str(&d.name);
    write_binders(out, &d.binders, lm);
    out.push_str(" : ");
    write_expr(out, &d.ty, 0, lm);
    out.push('\n');
    for arm in &d.equations {
        out.push_str("  | ");
        write_pattern(out, &arm.pattern, lm);
        out.push_str(" => ");
        write_expr(out, &arm.body, 0, lm);
        out.push('\n');
    }
}

fn write_def(out: &mut String, d: &Def, lm: &mut Landmarks) {
    for attr in &d.attrs {
        out.push_str("@[");
        out.push_str(attr);
        out.push_str("] ");
    }
    // All Tactus-emitted defs are `noncomputable`: spec fns are Prop-land
    // and can use classical axioms that Lean refuses to compile. Rather
    // than making every caller set a flag that's always true, bake it in.
    out.push_str("noncomputable def ");
    out.push_str(&d.name);
    write_binders(out, &d.binders, lm);
    out.push_str(" : ");
    write_expr(out, &d.ret_ty, 0, lm);
    out.push_str(" :=\n  ");
    write_expr(out, &d.body, 0, lm);
    out.push('\n');
    match d.termination_by.as_slice() {
        [] => {}
        [single] => {
            out.push_str(if d.termination_structural {
                "termination_by structural "
            } else {
                "termination_by "
            });
            write_expr(out, single, 0, lm);
            out.push('\n');
        }
        many => {
            out.push_str("termination_by (");
            for (i, e) in many.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push_str(")\n");
        }
    }
    if let Some(tac) = &d.decreasing_by {
        out.push_str("decreasing_by ");
        out.push_str(tac);
        out.push('\n');
    }
}

fn write_theorem(out: &mut String, t: &Theorem, lm: &mut Landmarks) {
    // Per-theorem `maxHeartbeats` override from
    // `#[verifier::heartbeats(N)]`. The `in` keyword scopes the
    // option to just this theorem; without it, the option would
    // apply to all subsequent declarations in the file.
    if let Some(n) = t.heartbeats {
        out.push_str(&format!("set_option maxHeartbeats {} in\n", n));
    }
    out.push_str("theorem ");
    out.push_str(&t.name);
    write_binders(out, &t.binders, lm);
    out.push_str(" :\n    ");
    write_expr(out, &t.goal, 0, lm);
    out.push_str(" := by\n");
    write_tactic_block(out, &t.tactic, "  ", lm);
    // `termination_by` for recursive proof fns (Verus's `decreases` clause).
    // Renders after the tactic body. Mirrors `Def.termination_by`'s emission
    // shape: bare for single measure, tuple for lex. Empty Vec → no clause.
    match t.termination_by.as_slice() {
        [] => {}
        [single] => {
            out.push_str("termination_by ");
            write_expr(out, single, 0, lm);
            out.push('\n');
        }
        many => {
            out.push_str("termination_by (");
            for (i, e) in many.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push_str(")\n");
        }
    }
    // `decreasing_by` for the recursive case, mirroring `Def`. Only ever
    // `Some` when `termination_by` is non-empty (set by `proof_fn_to_ast`).
    if let Some(tac) = &t.decreasing_by {
        out.push_str("decreasing_by ");
        out.push_str(tac);
        out.push('\n');
    }
}

fn write_datatype(out: &mut String, dt: &Datatype, lm: &mut Landmarks) {
    match &dt.kind {
        DatatypeKind::Structure { fields } => {
            out.push_str("structure ");
            out.push_str(&dt.name);
            for tp in &dt.typ_params {
                out.push_str(" (");
                out.push_str(tp);
                out.push_str(" : Type)");
            }
            out.push_str(" where\n");
            for f in fields {
                out.push_str("  ");
                out.push_str(&f.name);
                out.push_str(" : ");
                write_expr(out, &f.ty, 0, lm);
                out.push('\n');
            }
        }
        DatatypeKind::Inductive { variants } => {
            out.push_str("inductive ");
            out.push_str(&dt.name);
            for tp in &dt.typ_params {
                out.push_str(" (");
                out.push_str(tp);
                out.push_str(" : Type)");
            }
            out.push_str(" where\n");
            for v in variants {
                out.push_str("  | ");
                out.push_str(&v.name);
                for f in &v.fields {
                    out.push_str(" (");
                    out.push_str(&f.name);
                    out.push_str(" : ");
                    write_expr(out, &f.ty, 0, lm);
                    out.push(')');
                }
                out.push('\n');
            }
        }
        DatatypeKind::IndexedInductive { variants } => {
            // `inductive T : Type → Type → ... → Type 1 where`
            // (one `Type → ` for each type parameter, ending in `Type 1`
            // because Lean's universe rules force the bump for an indexed
            // inductive whose constructors universally bind type args).
            out.push_str("inductive ");
            out.push_str(&dt.name);
            out.push_str(" : ");
            for _ in &dt.typ_params {
                out.push_str("Type → ");
            }
            out.push_str("Type 1 where\n");
            for v in variants {
                // `| Name : ∀ {A : Type} {B : Type} ..., field_ty1 → ... → T A B`
                out.push_str("  | ");
                out.push_str(&v.name);
                out.push_str(" : ");
                if !dt.typ_params.is_empty() {
                    out.push('∀');
                    for tp in &dt.typ_params {
                        out.push_str(" {");
                        out.push_str(tp);
                        out.push_str(" : Type}");
                    }
                    out.push_str(", ");
                }
                for f in &v.fields {
                    write_expr(out, &f.ty, 0, lm);
                    out.push_str(" → ");
                }
                // Ctor result type: the RELATIVE self-name — the
                // root-anchored `dt.name` doesn't resolve while the
                // inductive is still being elaborated (see
                // `Datatype::self_name`).
                out.push_str(&dt.self_name);
                for tp in &dt.typ_params {
                    out.push(' ');
                    out.push_str(tp);
                }
                out.push('\n');
            }
        }
    }
    if !dt.derives.is_empty() {
        out.push_str("  deriving ");
        out.push_str(&dt.derives.join(", "));
        out.push('\n');
    }
}

fn write_class(out: &mut String, c: &Class, lm: &mut Landmarks) {
    out.push_str("class ");
    out.push_str(&c.name);
    write_binders(out, &c.typ_params, lm);
    // Superclasses via Lean's native `extends P₁, P₂, …` (comma-separated),
    // which handles superclass transitivity + inherited outParams for us.
    if !c.extends_parents.is_empty() {
        out.push_str(" extends ");
        for (i, p) in c.extends_parents.iter().enumerate() {
            if i > 0 { out.push_str(", "); }
            write_expr(out, p, 0, lm);
        }
    }
    out.push_str(" where\n");
    for m in &c.methods {
        out.push_str("  ");
        out.push_str(&m.name);
        out.push_str(" : ");
        write_expr(out, &m.ty, 0, lm);
        if let Some(default) = &m.default {
            out.push_str(" := ");
            write_expr(out, default, 0, lm);
        }
        out.push('\n');
        // Termination clause for recursive defaults. Empty Vec
        // means non-recursive default (or no default) — no
        // `termination_by` emitted.
        match m.termination_by.as_slice() {
            [] => {}
            [single] => {
                out.push_str("    termination_by ");
                write_expr(out, single, 0, lm);
                out.push('\n');
            }
            many => {
                out.push_str("    termination_by (");
                for (i, t) in many.iter().enumerate() {
                    if i > 0 { out.push_str(", "); }
                    write_expr(out, t, 0, lm);
                }
                out.push_str(")\n");
            }
        }
    }
}

fn write_instance(out: &mut String, i: &Instance, lm: &mut Landmarks) {
    out.push_str("noncomputable instance");
    write_binders(out, &i.binders, lm);
    out.push_str(" : ");
    write_expr(out, &i.target, 0, lm);
    out.push_str(" where\n");
    for m in &i.methods {
        out.push_str("  ");
        out.push_str(&m.name);
        out.push_str(" := ");
        write_expr(out, &m.body, 0, lm);
        out.push('\n');
    }
}

fn write_binders(out: &mut String, binders: &[Binder], lm: &mut Landmarks) {
    for b in binders {
        out.push(' ');
        let (lo, hi) = match b.kind {
            BinderKind::Explicit | BinderKind::OutParam => ('(', ')'),
            BinderKind::Implicit => ('{', '}'),
            BinderKind::Instance => ('[', ']'),
        };
        out.push(lo);
        if let Some(name) = &b.name {
            out.push_str(name.as_str());
            out.push_str(" : ");
        }
        if matches!(b.kind, BinderKind::OutParam) {
            out.push_str("outParam ");
        }
        write_expr(out, &b.ty, 0, lm);
        out.push(hi);
    }
}

// ── Tactic writers ──────────────────────────────────────────────────────

fn write_tactic_block(
    out: &mut String,
    t: &Tactic,
    indent: &str,
    lm: &mut Landmarks,
) {
    match t {
        Tactic::Raw(body) => {
            // Record the 1-indexed line where the first character of the
            // raw body lands. `LeanSourceMap` uses this to map Lean-reported
            // positions back to offsets within the user's tactic text.
            lm.tactic_starts.push(current_line(out));
            for line in body.lines() {
                if line.trim().is_empty() {
                    out.push('\n');
                } else {
                    out.push_str(indent);
                    out.push_str(line);
                    out.push('\n');
                }
            }
        }
        Tactic::Named(name) => {
            out.push_str(indent);
            out.push_str(name);
            out.push('\n');
        }
    }
}

// ── Expression writer ──────────────────────────────────────────────────

fn write_expr(out: &mut String, e: &Expr, parent_prec: u16, lm: &mut Landmarks) {
    let my_prec = expr_prec(&e.node);
    let needs_parens = my_prec < parent_prec;
    if needs_parens { out.push('('); }
    write_expr_body(out, &e.node, lm);
    if needs_parens { out.push(')'); }
}

fn write_expr_body(out: &mut String, node: &ExprNode, lm: &mut Landmarks) {
    match node {
        ExprNode::Var(s) => out.push_str(s.as_str()),
        ExprNode::Lit(s) => {
            if s.starts_with('-') {
                out.push('(');
                out.push_str(s);
                out.push(')');
            } else {
                out.push_str(s);
            }
        }
        ExprNode::LitBool(true) => out.push_str("True"),
        ExprNode::LitBool(false) => out.push_str("False"),
        ExprNode::LitStr(s) => {
            out.push('"');
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        ExprNode::LitChar(c) => {
            out.push('\'');
            out.push(*c);
            out.push('\'');
        }
        ExprNode::Raw(s) => out.push_str(s),

        ExprNode::ByBlock { tactic } => {
            // Tactic body in term position. Find the indent of the
            // current line in `out` (the line `by` lands on), then
            // emit each non-empty body line at that indent + 2 spaces.
            // Lean's tactic parser requires body indent strictly
            // past the surrounding context; since sibling fields in
            // classes/instances sit at the current line's indent,
            // +2 spaces is the minimum that unambiguously puts the
            // body inside the `by` block.
            //
            // Single-line tactic: emit on the same line as `by` for
            // readability (e.g., `by omega`, `by trivial`). Trim
            // each line independently so leading whitespace from
            // the dedented source doesn't leak through.
            let trimmed: Vec<&str> = tactic.lines()
                .map(|l| l.trim())
                .filter(|l| !l.is_empty())
                .collect();
            if trimmed.is_empty() {
                out.push_str("by trivial");
            } else if trimmed.len() == 1 {
                out.push_str("by ");
                out.push_str(trimmed[0]);
            } else {
                let line_indent = current_line_indent(out);
                let body_indent: String = std::iter::repeat(' ')
                    .take(line_indent + 2)
                    .collect();
                out.push_str("by");
                for line in &trimmed {
                    out.push('\n');
                    out.push_str(&body_indent);
                    out.push_str(line);
                }
            }
        }

        ExprNode::BinOp { op, lhs, rhs } => {
            let (p, assoc) = binop_info(*op);
            let (lp, rp) = match assoc {
                Assoc::Left => (p, p + 1),
                Assoc::Right => (p + 1, p),
                Assoc::None_ => (p + 1, p + 1),
            };
            write_expr(out, lhs, lp, lm);
            out.push(' ');
            out.push_str(binop_symbol(*op));
            out.push(' ');
            write_expr(out, rhs, rp, lm);
        }

        ExprNode::UnOp { op, arg } => {
            out.push_str(match op {
                UnOp::Not => "¬",
                UnOp::Neg => "-",
                UnOp::BitNot => "~~~",
            });
            // Unary ops tuck tight — emit arg at prec APP so any non-atom
            // arg (including another UnOp) parenthesizes.
            write_expr(out, arg, PREC_APP, lm);
        }

        ExprNode::App { head, args } => {
            if args.is_empty() {
                write_expr(out, head, PREC_ATOM, lm);
            } else {
                write_expr(out, head, PREC_APP, lm);
                for a in args {
                    out.push(' ');
                    write_expr(out, a, PREC_APP + 1, lm);
                }
            }
        }

        ExprNode::Let { name, value, body } => {
            // Continuation column: align the body exactly under this
            // `let`'s own keyword. Any enclosing column guard
            // (colGt/colGe against a saved position P) that admitted
            // the `let` token at column C has P ≤ C, so a continuation
            // at C passes it too. The old fixed 4-space indent dedented
            // the bodies of mid-line lets (`… then let i := v;`) below
            // their enclosing guard — Lean cut the term at the next
            // non-atom token: `unexpected token '('; expected 'else'`
            // (F1, DESIGN-lean-all-proofs-followons.md). Repro: a
            // let-chain in the RHS of an enclosing `let` inside a
            // parenthesized `∀`. Chars, not bytes — Lean columns are
            // codepoints and the prefix may hold `∀`/`∧`/`→`.
            let line_start = out.rfind('\n').map(|i| i + 1).unwrap_or(0);
            let let_col = out[line_start..].chars().count();
            out.push_str("let ");
            out.push_str(name.as_str());
            out.push_str(" := ");
            write_expr(out, value, 0, lm);
            out.push_str(";\n");
            out.extend(std::iter::repeat(' ').take(let_col));
            write_expr(out, body, 0, lm);
        }
        ExprNode::Lambda { binders, body } => {
            out.push_str("fun");
            if binders.is_empty() {
                // Zero-arg closure (`||`-syntax in Rust). Lean's `fun`
                // requires at least one binder; `fun => body` is a
                // parse error. Emit `fun ()` to match the unit-arg
                // form a Lean user would write for `Unit → T`.
                out.push_str(" ()");
            } else {
                write_binders(out, binders, lm);
            }
            out.push_str(" => ");
            write_expr(out, body, 0, lm);
        }
        ExprNode::Forall { binders, body } => {
            // Zero binders: `∀, P` is a parse error and a zero-binder
            // quantifier IS its body — print the body alone. Reached
            // via plain (non-forall) `assert … by { }`: the desugar's
            // re-assumed fact is `Quant(FORALL, vars=[], req ⇒ ens)`
            // (F4). Same guard family as Lambda's `fun ()` arm.
            if binders.is_empty() {
                write_expr(out, body, 0, lm);
            } else {
                out.push('∀');
                write_binders(out, binders, lm);
                out.push_str(", ");
                write_expr(out, body, 0, lm);
            }
        }
        ExprNode::Exists { binders, body } => {
            if binders.is_empty() {
                write_expr(out, body, 0, lm);
            } else {
                out.push('∃');
                write_binders(out, binders, lm);
                out.push_str(", ");
                write_expr(out, body, 0, lm);
            }
        }

        ExprNode::If { cond, then_, else_ } => {
            out.push_str("if ");
            write_expr(out, cond, 0, lm);
            out.push_str(" then ");
            write_expr(out, then_, 0, lm);
            if let Some(e) = else_ {
                out.push_str(" else ");
                write_expr(out, e, 0, lm);
            }
        }

        ExprNode::Match { scrutinee, arms } => {
            out.push_str("match ");
            write_expr(out, scrutinee, 0, lm);
            out.push_str(" with");
            for arm in arms {
                out.push_str(" | ");
                write_pattern(out, &arm.pattern, lm);
                out.push_str(" => ");
                write_expr(out, &arm.body, 0, lm);
            }
        }

        ExprNode::TypeAnnot { expr, ty } => {
            out.push('(');
            write_expr(out, expr, 0, lm);
            out.push_str(" : ");
            write_expr(out, ty, 0, lm);
            out.push(')');
        }

        ExprNode::FieldProj { expr, field } => {
            write_expr(out, expr, PREC_ATOM, lm);
            out.push('.');
            out.push_str(field);
        }

        ExprNode::StructUpdate { base, updates } => {
            out.push_str("{ ");
            write_expr(out, base, 0, lm);
            out.push_str(" with ");
            for (i, (name, val)) in updates.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                out.push_str(name);
                out.push_str(" := ");
                write_expr(out, val, 0, lm);
            }
            out.push_str(" }");
        }

        ExprNode::ArrayLit(elts) => {
            out.push('[');
            for (i, e) in elts.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push(']');
        }

        ExprNode::VectorLit(elts) => {
            out.push_str("#v[");
            for (i, e) in elts.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push(']');
        }

        ExprNode::Index { base, idx, bang } => {
            write_expr(out, base, PREC_ATOM, lm);
            out.push('[');
            write_expr(out, idx, 0, lm);
            out.push(']');
            if *bang {
                out.push('!');
            }
        }

        ExprNode::Anon(elts) => {
            out.push('⟨');
            for (i, e) in elts.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push('⟩');
        }

        ExprNode::Subtype { name, ty, pred } => {
            // `{ name : ty // pred }` — Lean's subtype syntax. The
            // `name` is bound in `pred` (the refinement predicate).
            // Used for proof-fn trait method types with non-unit
            // returns: the class field is `{ r : RetTy // ensures }`.
            out.push_str("{ ");
            out.push_str(name.as_str());
            out.push_str(" : ");
            write_expr(out, ty, 0, lm);
            out.push_str(" // ");
            write_expr(out, pred, 0, lm);
            out.push_str(" }");
        }

        ExprNode::Tuple(elts) => {
            out.push('(');
            for (i, e) in elts.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_expr(out, e, 0, lm);
            }
            out.push(')');
        }

        // SpanMark: transparent at the value level. Emit a leading
        // `/- @rust:LOC -/` block-comment marker in the Lean
        // output AND record `(current_line, rust_loc)` directly in
        // the landmarks struct (#51 source mapping). The comment
        // is kept in the output as a debug aid for users
        // inspecting the generated `.lean` file; the structured
        // landmark is what `LeanSourceMap::find_span_mark` reads
        // at error-formatting time. Regular block comments (`/-
        // ... -/`) are valid anywhere whitespace is (unlike
        // `/-!`, which Lean treats as a module docstring and
        // rejects inline).
        //
        // No newline sanitization needed: `rust_loc` is produced
        // by `format_rust_loc` from `Span::start_loc` (a
        // `path:line:col` string written by
        // `rust_verify::spans::to_air_span`) or, as fallback, from
        // `Span::as_string` (a `format!("{:?}", rustc_span)`
        // result). Both formats are single-line by construction.
        // Pinned by `span_mark_loc_has_no_newlines` and
        // `span_mark_render_preserves_loc_verbatim`.
        ExprNode::SpanMark { rust_loc, rust_span, kind, inner } => {
            lm.span_marks.push(SpanMarkLandmark {
                line: current_line(out),
                loc: rust_loc.clone(),
                rust_span: rust_span.clone(),
                kind: *kind,
            });
            out.push_str("/- @rust:");
            out.push_str(rust_loc);
            out.push_str(" -/ ");
            write_expr_body(out, &inner.node, lm);
        }
    }
}

fn write_pattern(out: &mut String, p: &Pattern, lm: &mut Landmarks) {
    match p {
        Pattern::Var(s) => out.push_str(s.as_str()),
        Pattern::Wildcard => out.push('_'),
        Pattern::Ctor { name, args } => {
            out.push_str(name);
            for a in args {
                out.push(' ');
                let needs = matches!(a, Pattern::Ctor { args, .. } if !args.is_empty());
                if needs { out.push('('); }
                write_pattern(out, a, lm);
                if needs { out.push(')'); }
            }
        }
        Pattern::Tuple(args) => {
            out.push('(');
            for (i, a) in args.iter().enumerate() {
                if i > 0 { out.push_str(", "); }
                write_pattern(out, a, lm);
            }
            out.push(')');
        }
        Pattern::Or(l, r) => {
            write_pattern(out, l, lm);
            out.push_str(" | ");
            write_pattern(out, r, lm);
        }
        Pattern::Binding { name, sub } => {
            out.push_str(name.as_str());
            out.push('@');
            write_pattern(out, sub, lm);
        }
        Pattern::Lit(node) => write_expr_body(out, node, lm),
    }
}

#[cfg(test)]
#[path = "tests/lean_pp.rs"]
mod tests;
