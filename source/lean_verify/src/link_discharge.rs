//! Link-discharge generator (bootstrap-73, DESIGN-link-discharge.md).
//!
//! Synthesizes ONE closed theorem per proof fn from the per-VC spine
//! sidecars (`pkg/<leaf>.spine.json`, written by `write_spine_sidecar`):
//!
//! * **zero-spine** — single binders-only postcondition VC: the VC
//!   statement IS the clean statement; re-export under the stable name.
//! * **straight-line** — no branches: one positional application of the
//!   VC theorem(s); call premises discharged by callees' closed
//!   theorems, Unit ret binders by `()`.
//! * **fix** — lowered-match recursion: a `match` on the scrutinee with
//!   per-arm positional applications, `have hdec := <termination VC>`
//!   for the woven height premise, the theorem's own recursive call as
//!   the IH, and `termination_by`/`decreasing_by` replaying the
//!   termination VC (the probe34 hand-validated shape).
//!
//! Everything not (yet) synthesizable is PENDING with a reason — the
//! census is reported through the package-gate note. No silent caps.

use std::collections::{HashMap, HashSet};

// ── sidecar model ───────────────────────────────────────────────────

pub struct FnSidecar {
    pub vcs: Vec<Vc>,
}

pub struct Vc {
    pub name: String,
    pub leaf: String,
    pub spine: Vec<Node>,
    pub is_post: bool,
    pub is_term: bool,
}

#[derive(PartialEq, Clone)]
pub enum Node {
    All { name: String, ty: String },
    Let { name: String, v: String },
    Branch { test: Option<BTest> },
    Call { callee: String, is_self: bool, args: Vec<Arg> },
    Height,
    /// N1 hoisted-let equation hyp (`_h_{binder}_hoist1 : binder = v`).
    /// The value binder `binder` is the mid-spine All immediately
    /// before this node; it is definitionally `v`, so the composer
    /// replays `let {binder} := {v};` and closes this premise with
    /// `rfl` (zeta-defeq). Not a fn param — `leading_alls` trims it.
    HoistEq { binder: String, v: String },
    /// The fn's OWN requires clause (named hyp, `p:"requires"`). Part
    /// of the fn's contract, not a woven premise — carried as a
    /// hypothesis binder of the closed theorem and fed back
    /// positionally.
    Req { name: String, prop: String },
    Other,
}

#[derive(PartialEq, Clone)]
pub struct BTest {
    pub scrut: String,
    pub dt: String,
    pub variant: String,
    pub pos: bool,
}

#[derive(PartialEq, Clone)]
pub struct Arg {
    pub text: String,
    #[allow(dead_code)] // bound recipes (wf rung) read the tag
    pub tag: String,
}

pub fn parse_sidecar(txt: &str) -> Option<FnSidecar> {
    let v: serde_json::Value = serde_json::from_str(txt).ok()?;
    let mut vcs = Vec::new();
    for vc in v.get("vcs")?.as_array()? {
        let name = vc.get("name")?.as_str()?.to_string();
        let leaf = vc.get("leaf").and_then(|l| l.as_str()).unwrap_or("").to_string();
        let mut spine = Vec::new();
        // spine:null = a stage-A exclusion (bit_vector) — treat as Other
        // so the fn pends loudly rather than mis-synthesizing.
        match vc.get("spine").and_then(|s| s.as_array()) {
            None => spine.push(Node::Other),
            Some(arr) => {
                for n in arr {
                    let k = n.get("k").and_then(|k| k.as_str()).unwrap_or("");
                    // An "all" entry CARRYING premise provenance is an
                    // absorbed leading hyp (`_h_hoist_N` binder) — same
                    // application position as the corresponding imp, so
                    // parse it as the premise node directly.
                    let k = if k == "all" && n.get("p").is_some() { "imp" } else { k };
                    spine.push(match k {
                        "all" => Node::All {
                            name: n.get("name")?.as_str()?.to_string(),
                            ty: n.get("ty")?.as_str()?.to_string(),
                        },
                        "let" => Node::Let {
                            name: n.get("name")?.as_str()?.to_string(),
                            v: n.get("v").and_then(|v| v.as_str()).unwrap_or("").to_string(),
                        },
                        "imp" => match n.get("p").and_then(|p| p.as_str()).unwrap_or("") {
                            "branch" => Node::Branch {
                                test: n.get("variant").and_then(|_| {
                                    Some(BTest {
                                        scrut: n.get("scrut")?.as_str()?.to_string(),
                                        dt: n.get("dt")?.as_str()?.to_string(),
                                        variant: n.get("variant")?.as_str()?.to_string(),
                                        pos: n.get("pos")?.as_bool()?,
                                    })
                                }),
                            },
                            "height" => Node::Height,
                            // Hoist/requires premises are usable only in
                            // their NAMED (all+p) form. The equation RHS
                            // comes from the STRUCTURED `v` field (written
                            // from the eq LExpr — self-review 2026-07-24
                            // finding 2, no text re-parse); a sidecar
                            // without it (non-eq shape, or the unnamed imp
                            // form) falls through to Other (loud pend),
                            // never a silent misparse.
                            "hoist" => (|| {
                                Some(Node::HoistEq {
                                    binder: n.get("binder")?.as_str()?.to_string(),
                                    v: n.get("v")?.as_str()?.to_string(),
                                })
                            })()
                            .unwrap_or(Node::Other),
                            "requires" => (|| {
                                Some(Node::Req {
                                    name: n.get("name")?.as_str()?.to_string(),
                                    prop: n.get("ty")?.as_str()?.to_string(),
                                })
                            })()
                            .unwrap_or(Node::Other),
                            "call" => Node::Call {
                                callee: n.get("callee")?.as_str()?.to_string(),
                                is_self: n.get("self")?.as_bool()?,
                                args: n
                                    .get("args")?
                                    .as_array()?
                                    .iter()
                                    .map(|a| {
                                        Some(Arg {
                                            text: a.get("text")?.as_str()?.to_string(),
                                            tag: a.get("tag")?.as_str()?.to_string(),
                                        })
                                    })
                                    .collect::<Option<Vec<_>>>()?,
                            },
                            _ => Node::Other,
                        },
                        _ => Node::Other,
                    });
                }
            }
        }
        vcs.push(Vc {
            is_post: name.contains("_tactus_postcondition_"),
            is_term: name.contains("_tactus_termination_"),
            name,
            leaf,
            spine,
        });
    }
    Some(FnSidecar { vcs })
}

// ── generator context ───────────────────────────────────────────────

pub struct Ctx<'a> {
    /// Relative fn name → its sidecar (all proof fns in the crate).
    pub sidecars: &'a HashMap<String, FnSidecar>,
    /// Relative fn names whose `<rel>_closed` is already emitted,
    /// with the wf params their synthesized signature carries.
    pub closed: &'a HashMap<String, ClosedMeta>,
    /// Datatype (relative name) → ordered [(variant, field
    /// accessors in declaration order — `val<N>` or the field name)].
    pub variants: &'a HashMap<String, Vec<(String, Vec<String>)>>,
    /// R-b: datatype (relative) → wf-conjunct structure per variant.
    /// Present only for scalar-carrying datatypes (those with a
    /// generated `{Dt}Wf` predicate).
    pub wf: &'a HashMap<String, WfInfo>,
    /// R-c: synthesized preservation lemmas (`{g}_wf`), by spec fn.
    pub wf_lemmas: &'a HashMap<String, crate::wf_synth::FnWfSig>,
    /// R-c: per-datatype conjunct specs (ctor-literal wf resolution).
    pub wf_specs: &'a HashMap<String, crate::wf_synth::DtWfSpec>,
    /// Crate namespace (`lib`) — for parsing spec-fn heads in arg texts.
    pub ns: &'a str,
}

/// N2 match-splitting: a mid-spine `∀ ({scrut}_val{i} : T)` field
/// binder. In a fix arm the scrutinee is destructured, so the right
/// instantiation is the pattern's i-th argument.
fn n2_field_binder_token(name: &str, env: &AppEnv) -> Option<String> {
    let (p, pat) = env.scrut_subst?;
    let base = if let Some(rest) = name.strip_prefix(p) {
        rest
    } else if let Some(a) = env.scrut_alias {
        name.strip_prefix(a)?
    } else {
        return None;
    };
    let acc = base.strip_prefix('_')?;
    let idx = env.arm_accessors.iter().position(|a| a == acc)?;
    let toks: Vec<&str> = pat.split_whitespace().collect();
    toks.get(idx + 1).map(|t| t.to_string())
}

/// Strip balanced outer paren layers: `((X))` → `X`, but `(A) (B)`
/// stays intact (the closing paren of the first token is not the last
/// char). Depth-aware — never produces unbalanced fragments.
fn strip_outer_parens(mut t: &str) -> &str {
    t = t.trim();
    loop {
        if !(t.starts_with('(') && t.ends_with(')')) {
            return t;
        }
        let mut depth = 0i32;
        let mut ok = true;
        for (i, c) in t.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && i != t.len() - 1 {
                        ok = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if !ok || depth != 0 {
            return t;
        }
        t = t[1..t.len() - 1].trim();
    }
}

/// Split an application text into top-level (paren-depth-0) tokens.
fn split_top(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut cur = String::new();
    for c in text.chars() {
        match c {
            '(' => {
                depth += 1;
                cur.push(c);
            }
            ')' => {
                depth = depth.saturating_sub(1);
                cur.push(c);
            }
            ' ' if depth == 0 => {
                if !cur.is_empty() {
                    out.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        out.push(cur);
    }
    out
}

/// A bound-conjunct proof for an argument TEXT: the arm's destructured
/// component or a lead `h_*_bound` binder when nameable — `(by omega)`
/// only as a context-free fallback (tactic goals in term-position match
/// arms can be postponed outside the arm, losing pattern hypotheses).
fn resolve_bound_text(text: &str, env: &AppEnv) -> String {
    let t = strip_outer_parens(text);
    if let Some((comp, false)) = env.arm_comps.get(t) {
        return comp.clone();
    }
    let hb = format!("h_{}_bound", t);
    if env.own_lead.iter().any(|n| matches!(n, Node::All { name, .. } if *name == hb)) {
        return hb;
    }
    if let Some(v) = env.lets.get(t) {
        return resolve_bound_text(v, env);
    }
    "(by omega)".to_string()
}

/// R-c: resolve a wf proof for an argument TEXT — own param hypothesis,
/// arm component (`x.deref`), synthesized `{g}_wf` application, or a
/// constructor's anonymous-constructor proof. Bounds ride `(by omega)`.
fn resolve_wf_text(text: &str, want_dt: &str, env: &AppEnv) -> Result<String, String> {
    let t = strip_outer_parens(text);
    if let Some(b) = env.own_wf.get(t) {
        return Ok(b.clone());
    }
    if let Some(stripped) = t.strip_suffix(".deref") {
        if let Some((comp, true)) = env.arm_comps.get(stripped) {
            return Ok(comp.clone());
        }
        // (Boxed-param wf hyps are keyed by `p.deref` in own_wf, so
        // the first lookup above already catches them.)
        if let Some(v) = env.lets.get(stripped) {
            return resolve_wf_text(&format!("({}).deref", v), want_dt, env);
        }
    }
    if let Some((comp, true)) = env.arm_comps.get(t) {
        return Ok(comp.clone());
    }
    if let Some(v) = env.lets.get(t) {
        return resolve_wf_text(v, want_dt, env);
    }
    let toks = split_top(t);
    let head = toks.first().map(|s| s.as_str()).unwrap_or("");
    let Some(rest) = head.strip_prefix(&format!("{}.", env.ns)) else {
        return Err(format!("wf-transport for arg `{}` ({}Wf)", text, want_dt));
    };
    if let Some((d, v)) = rest.split_once('.') {
        // Constructor application `lib.D.V a b …`.
        if d != want_dt {
            return Err(format!("ctor {} where {}Wf wanted", d, want_dt));
        }
        let spec = env
            .wf_specs
            .get(d)
            .ok_or_else(|| format!("no wf spec for {}", d))?;
        let conjs = spec
            .variants
            .get(v)
            .ok_or_else(|| format!("unknown variant {}.{}", d, v))?;
        let mut parts = Vec::new();
        for (idx, kind) in conjs {
            let arg = toks
                .get(idx + 1)
                .ok_or_else(|| format!("ctor {}.{} arity in `{}`", d, v, text))?;
            match kind {
                crate::wf_synth::ConjKind::Bound => parts.push(resolve_bound_text(arg, env)),
                crate::wf_synth::ConjKind::Rec { dt, boxed } => {
                    let inner = if *boxed {
                        let a = strip_outer_parens(arg);
                        match a.strip_prefix("Tactus.Box.mk ") {
                            Some(x) => x.to_string(),
                            // Bare Box-typed var: its wf is the wf of
                            // `v.deref` — resolvable via an own-wf
                            // hypothesis on the deref.
                            None if !a.contains(' ') => format!("{}.deref", a),
                            None => {
                                return Err(format!(
                                    "boxed ctor arg `{}` not Box.mk", arg
                                ))
                            }
                        }
                    } else {
                        arg.clone()
                    };
                    parts.push(resolve_wf_text(&inner, dt, env)?);
                }
            }
        }
        return Ok(match parts.len() {
            0 => "trivial".to_string(),
            1 => parts.into_iter().next().unwrap(),
            _ => format!("⟨{}⟩", parts.join(", ")),
        });
    }
    // Spec-fn application `lib.g a b …` with a synthesized lemma.
    let sig = env
        .wf_lemmas
        .get(rest)
        .ok_or_else(|| format!("wf-transport for arg `{}` ({}Wf, no {}_wf)", text, want_dt, rest))?;
    if sig.ret_dt != want_dt {
        return Err(format!("{} returns {}Wf, wanted {}Wf", rest, sig.ret_dt, want_dt));
    }
    if toks.len() != sig.params.len() + 1 {
        return Err(format!("`{}` arity vs {}_wf", text, rest));
    }
    let mut out = format!("({}_wf", rest);
    for (a, (_, kind)) in toks[1..].iter().zip(&sig.params) {
        out.push(' ');
        out.push_str(a);
        match kind {
            crate::wf_synth::ParamKind::Bounded(_) => {
                out.push(' ');
                out.push_str(&resolve_bound_text(a, env));
            }
            crate::wf_synth::ParamKind::Dt(d) => {
                out.push(' ');
                out.push_str(&resolve_wf_text(a, d, env)?);
            }
            crate::wf_synth::ParamKind::Other => {}
        }
    }
    out.push(')');
    Ok(out)
}

/// Signature metadata of an already-closed fn: the wf hypotheses its
/// clean statement takes, in binder order (appended after the VC's
/// leading Alls). `(param name, datatype rel name)`.
#[derive(Clone, Default)]
pub struct ClosedMeta {
    pub wf_params: Vec<(String, String)>,
}

/// Wf-conjunct structure of one datatype: variant → ordered conjunct
/// fields. Order MUST match the generated `{Dt}Wf` match clauses —
/// the arm destructuring components are positional.
pub struct WfInfo {
    pub variants: HashMap<String, Vec<WfComp>>,
}

/// One wf conjunct: `accessor` names the field (`val0`, `cond_ann`);
/// `rec` = a recursive `{Dt2}Wf child.deref` conjunct (vs a scalar
/// bound). Component binder names: `hwf_{accessor}` for rec,
/// `h_wf_{accessor}` for bounds.
pub struct WfComp {
    pub accessor: String,
    pub rec: bool,
}

pub enum Outcome {
    Closed { text: String, kind: &'static str, meta: ClosedMeta },
    Pending(String),
}

fn pend(reason: impl Into<String>) -> Outcome {
    Outcome::Pending(reason.into())
}

/// Word-boundary occurrence check (is `name` referenced in `text`?).
pub(crate) fn referenced(name: &str, text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut start = 0;
    while let Some(pos) = text[start..].find(name) {
        let i = start + pos;
        let before_ok = i == 0 || {
            let c = bytes[i - 1] as char;
            !(c.is_alphanumeric() || c == '_')
        };
        let j = i + name.len();
        let after_ok = j >= bytes.len() || {
            let c = bytes[j] as char;
            !(c.is_alphanumeric() || c == '_')
        };
        if before_ok && after_ok {
            return true;
        }
        start = i + 1;
    }
    false
}

/// Word-boundary global replace (companion to [`referenced`]).
pub(crate) fn replace_word(text: &str, name: &str, with: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    while i < text.len() {
        if let Some(pos) = text[i..].find(name) {
            let at = i + pos;
            let before_ok = at == 0 || {
                let c = bytes[at - 1] as char;
                !(c.is_alphanumeric() || c == '_')
            };
            let j = at + name.len();
            let after_ok = j >= bytes.len() || {
                let c = bytes[j] as char;
                !(c.is_alphanumeric() || c == '_')
            };
            out.push_str(&text[i..at]);
            if before_ok && after_ok {
                out.push_str(with);
            } else {
                out.push_str(name);
            }
            i = j;
        } else {
            out.push_str(&text[i..]);
            break;
        }
    }
    out
}

/// Expand let-bound names to their (parenthesized, transitively
/// expanded) values. Used where arm-scoped term lets are NOT in scope
/// — the `decreasing_by` bullets (the equation compiler's goals see
/// pattern binders but not the arm's term-mode lets).
fn expand_lets(text: &str, lets: &[(String, String)]) -> String {
    let mut expanded: Vec<(String, String)> = Vec::new();
    for (n, v) in lets {
        let mut ev = v.clone();
        for (pn, pv) in &expanded {
            ev = replace_word(&ev, pn, &format!("({})", pv));
        }
        expanded.push((n.clone(), ev));
    }
    let mut out = text.to_string();
    for (n, v) in expanded.iter().rev() {
        out = replace_word(&out, n, &format!("({})", v));
    }
    out
}

/// Strip a leading `/- ... -/ ` span-mark comment from a rendered leaf.
fn strip_mark(s: &str) -> &str {
    let t = s.trim_start();
    if let Some(rest) = t.strip_prefix("/-") {
        if let Some(end) = rest.find("-/") {
            return rest[end + 2..].trim_start();
        }
    }
    t
}

/// Leading `All` prefix of a spine (the clean statement's binders).
/// Stops at the first Unit-typed All — those are `∀`-path callee ret
/// binders (application slots for `()`), not signature binders.
/// The value-binder names of N1 hoisted lets in this spine. These
/// mid-spine Alls are NOT fn params (each is followed by its HoistEq
/// equation hyp): `leading_alls` trims them and `app_args`
/// instantiates them with their replayed `let`.
fn hoist_binder_names(spine: &[Node]) -> HashSet<&str> {
    spine
        .iter()
        .filter_map(|n| match n {
            Node::HoistEq { binder, .. } => Some(binder.as_str()),
            _ => None,
        })
        .collect()
}

fn leading_alls(spine: &[Node]) -> (&[Node], usize) {
    let hoists = hoist_binder_names(spine);
    let n = spine
        .iter()
        .take_while(|n| {
            matches!(n, Node::All { name, ty }
                if ty != "Unit" && !hoists.contains(name.as_str()))
        })
        .count();
    (&spine[..n], n)
}

// ── positional application builder ──────────────────────────────────

#[derive(Clone, Copy)]
struct AppEnv<'a> {
    fn_rel: &'a str,
    /// Scrutinee param name → the arm's pattern expression (fix arms).
    scrut_subst: Option<(&'a str, &'a str)>,
    /// The scrutinee's projection-let alias (`tmp___0`) — N2 field
    /// binders (`tmp___0_val0`) are named after it.
    scrut_alias: Option<&'a str>,
    /// The current arm's variant field accessors, in declaration order
    /// (`val0`… positional / `reqs`… named) — maps an N2 field binder
    /// suffix to its pattern position.
    arm_accessors: &'a [String],
    /// Names for the `have hdec{j}` bindings, consumed in order.
    hdec_names: &'a [String],
    /// Callee sidecars — the callee's leading Alls give the
    /// interleaved (param, h_*_bound) application order.
    sidecars: &'a HashMap<String, FnSidecar>,
    /// The caller's own leading Alls (bound-recipe lookups).
    own_lead: &'a [Node],
    /// Already-closed callees' signature metadata (wf args).
    closed: &'a HashMap<String, ClosedMeta>,
    /// The caller's OWN wf params (param → binder name).
    own_wf: &'a HashMap<String, String>,
    /// Fix-arm component lookup: projection-let name →
    /// (component binder name, rec?). Bound components discharge
    /// expr-fed scalar bounds; rec components feed the IH's wf arg.
    arm_comps: &'a HashMap<String, (String, bool)>,
    /// The being-built fn's own wf params (IH signature mirror).
    own_meta: &'a ClosedMeta,
    /// R-c resolution tables (from Ctx).
    wf_lemmas: &'a HashMap<String, crate::wf_synth::FnWfSig>,
    wf_specs: &'a HashMap<String, crate::wf_synth::DtWfSpec>,
    ns: &'a str,
    /// The VC's term-mode lets (name → value text) — wf-arg texts often
    /// name a let (`tmp__3`); resolution chases the value.
    lets: &'a HashMap<String, String>,
    /// bootstrap-79 (assert VCs in recursive fn): the arm's woven
    /// `if h : <guard_prop> then … else …` — the guard prop text and
    /// the hypothesis name feeding Branch{None} premises and
    /// guard-shaped requires of requires-carrying callees.
    guard_prop: Option<&'a str>,
    guard_h: Option<&'a str>,
}

/// Build the positional application of `vc`'s theorem through the
/// first `upto` spine nodes (None = all). Returns the argument list.
fn app_args(vc: &Vc, upto: Option<usize>, env: &AppEnv) -> Result<Vec<String>, String> {
    let mut args = Vec::new();
    let (_, n_lead) = leading_alls(&vc.spine);
    let hoists = hoist_binder_names(&vc.spine);
    let mut hdec_idx = 0usize;
    for (i, node) in vc.spine.iter().enumerate() {
        if let Some(u) = upto {
            if i >= u {
                break;
            }
        }
        match node {
            Node::All { name, ty } => {
                if i < n_lead {
                    match &env.scrut_subst {
                        Some((p, pat)) if p == name => args.push(format!("({})", pat)),
                        _ => args.push(name.clone()),
                    }
                } else if ty == "Unit" {
                    args.push("()".to_string());
                } else if hoists.contains(name.as_str()) {
                    // Hoisted-let value binder: its `let {name} := v;`
                    // is replayed before the application (replay_lets),
                    // so the binder instantiates with its own name.
                    args.push(name.clone());
                } else if let Some(tok) = n2_field_binder_token(name, env) {
                    // N2 match-splitting field binder ({scrut}_val{i}):
                    // instantiate with the arm's pattern binder; the
                    // constructor-equation premise that follows becomes
                    // rfl-shaped and closes via the usual `(by simp)`.
                    args.push(tok);
                } else {
                    return Err(format!("value-returning callee binder {}", name));
                }
            }
            Node::Let { .. } => {}
            Node::Branch { test } => {
                // bootstrap-79: inside an arm with a woven guard `if`,
                // non-variant branch premises are the guard itself —
                // feed the `if`'s hypothesis. Variant-test branches
                // (and guard-free arms) keep the discriminant path.
                match (test, env.guard_h) {
                    (None, Some(h)) => args.push(h.to_string()),
                    _ => args.push("(by simp)".to_string()),
                }
            }
            Node::Height => {
                let h = env
                    .hdec_names
                    .get(hdec_idx)
                    .ok_or_else(|| "height premise without termination VC".to_string())?;
                args.push(h.clone());
                hdec_idx += 1;
            }
            Node::Call { callee, is_self, args: cargs } => {
                args.push(call_app(callee, *is_self, cargs, vc, env)?);
            }
            // The equation premise `binder = v`: with `let binder := v`
            // in scope (replay_lets), `rfl` closes by zeta-defeq.
            Node::HoistEq { .. } => args.push("rfl".to_string()),
            // The fn's own requires: fed back from the closed
            // theorem's carried hypothesis binder of the same name.
            Node::Req { name, .. } => args.push(name.clone()),
            Node::Other => return Err("other-hyp in spine".to_string()),
        }
    }
    Ok(args)
}

fn app_text(vc: &Vc, upto: Option<usize>, env: &AppEnv) -> Result<String, String> {
    let args = app_args(vc, upto, env)?;
    Ok(format!("{} {}", vc.name, args.join(" ")))
}

/// bootstrap-79 (assert VCs in recursive fn): feed a requires-carrying
/// callee's hypothesis binders at the call site. Each requires premise
/// is either the arm's woven GUARD (`if h : P then … else …` — prop
/// text-matched against `env.guard_prop`, fed `h`) or an IH equality —
/// the caller's OWN postcondition shape, fed by the self-closed
/// application whose recorded self-Call's frame the prop mentions
/// (matched on the full `lib.wp_stm <frame> <stm>` text after chasing
/// the VC's lets; longest frame text wins so a `frame_append(base, …)`
/// frame is not shadowed by its `base` prefix). Anything else pends
/// loud — never a silent mis-feed.
fn feed_requires(
    callee: &str,
    callee_reqs: &[(String, String)],
    post_vc: &Vc,
    env: &AppEnv,
) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    for (name, prop) in callee_reqs {
        if let Some(g) = env.guard_prop {
            if prop == g || *prop == format!("¬({})", g) {
                out.push(env.guard_h.unwrap().to_string());
                continue;
            }
        }
        // The IH shape: the caller's own postcondition with the frame
        // text of one of its recorded self-Calls.
        let mut best: Option<(usize, &Vec<Arg>)> = None;
        for n in &post_vc.spine {
            let Node::Call { is_self: true, args: cargs, .. } = n else { continue };
            // cargs = [hp, he, lv, frame?, stm?, st] — the frame arg is
            // index 3 when present (an expr, possibly a let name).
            let Some(frame_arg) = cargs.get(3) else { continue };
            let frame = env
                .lets
                .get(&frame_arg.text)
                .cloned()
                .unwrap_or_else(|| frame_arg.text.clone());
            let stm = cargs.get(4).map(|a| a.text.clone()).unwrap_or_default();
            let needle = format!("lib.wp_stm ({}) {}", frame, stm);
            if prop.contains(&needle) && best.map_or(true, |(bl, _)| needle.len() > bl) {
                best = Some((needle.len(), cargs));
            }
        }
        let Some((_, cargs)) = best else {
            return Err(format!(
                "requires premise {} of {} (`{}`) is neither the arm guard nor a caller-IH shape",
                name, callee, prop
            ));
        };
        out.push(call_app(env.fn_rel, true, cargs, post_vc, env)?);
    }
    Ok(out)
}

/// The full application of a callee's `_closed` theorem: positional
/// params interleaved with bound proofs (per the callee's own leading
/// Alls), then any REQUIRES feeds (bootstrap-79), then the callee's wf
/// args. `post_vc` is the caller VC carrying the Call node (the
/// requires feeds match their IH shapes against its self-Calls).
fn call_app(
    callee: &str,
    is_self: bool,
    cargs: &[Arg],
    post_vc: &Vc,
    env: &AppEnv,
) -> Result<String, String> {
    let head = if is_self {
        format!("{}_closed", env.fn_rel)
    } else {
        format!("{}_closed", callee)
    };
    // Interleave bound proofs per the callee's own leading-All order
    // (params and their h_*_bound binders).
    let callee_sc = env.sidecars.get(if is_self { env.fn_rel } else { callee });
    let callee_lead: Vec<&Node> = callee_sc
        .and_then(|c| c.vcs.first())
        .map(|v| leading_alls(&v.spine).0.iter().collect())
        .unwrap_or_default();
    // bootstrap-79: a requires-carrying callee's closed theorem carries
    // hypothesis binders after its params — feed them (guard / caller
    // IH), or pend loud when the caller can't.
    let callee_reqs: Vec<(String, String)> = callee_sc
        .map(|c| {
            c.vcs
                .iter()
                .flat_map(|v| v.spine.iter())
                .filter_map(|n| match n {
                    Node::Req { name, prop } => Some((name.clone(), prop.clone())),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    let req_feeds = if callee_reqs.is_empty() {
        Vec::new()
    } else {
        feed_requires(callee, &callee_reqs, post_vc, env)?
    };
    let paren = |txt: &str| {
        if txt.chars().any(|c| c == ' ') && !txt.starts_with('(') {
            format!("({})", txt)
        } else {
            txt.to_string()
        }
    };
    let mut t = format!("({}", head);
    if callee_lead.is_empty() {
        // No callee sidecar (shouldn't happen post-guard):
        // fall back to plain param order.
        for a in cargs {
            t.push(' ');
            t.push_str(&paren(&a.text));
        }
    } else {
        let mut arg_i = 0usize;
        for cl in &callee_lead {
            let Node::All { name, .. } = cl else { continue };
            if name.starts_with("h_") && name.ends_with("_bound") {
                let feeder = cargs
                    .get(arg_i.wrapping_sub(1))
                    .ok_or("bound binder before any param")?;
                match feeder.tag.as_str() {
                    tag if tag.starts_with("param:") => {
                        let bname = format!("h_{}_bound", &tag[6..]);
                        let have = env.own_lead.iter().any(|n| {
                            matches!(n, Node::All { name, .. } if *name == bname)
                        });
                        if !have {
                            return Err(format!(
                                "caller lacks {} for {}",
                                bname, callee
                            ));
                        }
                        t.push(' ');
                        t.push_str(&bname);
                    }
                    "lit" => t.push_str(" (by omega)"),
                    _ => {
                        // R-b: an expr-fed bound whose arg is a
                        // scrutinee projection discharges by the
                        // arm's wf component.
                        match env.arm_comps.get(feeder.text.as_str()) {
                            Some((comp, false)) => {
                                t.push(' ');
                                t.push_str(comp);
                            }
                            _ => {
                                return Err(format!(
                                    "expr-fed bound at {} (wf-transport)",
                                    callee
                                ))
                            }
                        }
                    }
                }
            } else {
                let a = cargs
                    .get(arg_i)
                    .ok_or("callee params exceed recorded args")?;
                t.push(' ');
                t.push_str(&paren(&a.text));
                arg_i += 1;
            }
        }
        if arg_i != cargs.len() {
            return Err("recorded args exceed callee params".into());
        }
        // The requires feeds sit between the params and the wf args
        // (the callee's closed signature order: params, Req binders,
        // wf params).
        for f in &req_feeds {
            t.push(' ');
            t.push_str(f);
        }
        // R-b: append the callee's wf args (its synthesized
        // signature ends with wf params, in meta order).
        let meta = if is_self {
            Some(env.own_meta.clone())
        } else {
            env.closed.get(callee).cloned()
        };
        if let Some(meta) = meta {
            let pnames: Vec<&str> = callee_lead
                .iter()
                .filter_map(|n| match n {
                    Node::All { name, .. }
                        if !(name.starts_with("h_")
                            && name.ends_with("_bound")) =>
                    {
                        Some(name.as_str())
                    }
                    _ => None,
                })
                .collect();
            for (wp, dt) in &meta.wf_params {
                // bootstrap-79: a BOXED callee param's wf demand is
                // keyed `<param>.deref` in the callee meta — match the
                // base param, and feed the arm's wf component for the
                // field (the destructured `hwf_<field>`), not the
                // deref-component path.
                let base_wp = wp.strip_suffix(".deref").unwrap_or(wp);
                let i = pnames
                    .iter()
                    .position(|p| *p == base_wp)
                    .ok_or_else(|| format!("wf param {} not in {}", wp, callee))?;
                let feeder = &cargs[i];
                if wp != base_wp {
                    match env.arm_comps.get(feeder.text.as_str()) {
                        Some((comp, _)) => {
                            t.push(' ');
                            t.push_str(comp);
                            continue;
                        }
                        None => {
                            return Err(format!(
                                "boxed-param wf for {} ({}Wf) not composable at {}",
                                wp, dt, callee
                            ))
                        }
                    }
                }
                if let Some(stripped) = feeder.text.strip_suffix(".deref") {
                    // Scrutinee child: the arm's rec component.
                    if let Some((comp, true)) = env.arm_comps.get(stripped) {
                        t.push(' ');
                        t.push_str(comp);
                        continue;
                    }
                }
                match feeder.tag.as_str() {
                    tag if tag.starts_with("param:") => {
                        let p = &tag[6..];
                        let b = env.own_wf.get(p).ok_or_else(|| {
                            format!("needs own wf for param {} ({}Wf)", p, dt)
                        })?;
                        t.push(' ');
                        t.push_str(b);
                    }
                    _ => {
                        // R-c: spec-fn results / constructors
                        // resolve via synthesized lemmas.
                        let p = resolve_wf_text(&feeder.text, dt, env)
                            .map_err(|e| format!("{} (of {})", e, callee))?;
                        t.push(' ');
                        t.push_str(&p);
                    }
                }
            }
        }
    }
    t.push(')');
    Ok(t)
}

/// Lets that must be replayed in term mode before the applications:
/// those whose NAME is referenced by any call-arg text of the VC.
/// Projection lets (pattern binders) and unreferenced lets are skipped;
/// the scrutinee-alias let replays at the arm's pattern expression.
fn replay_lets(
    vc: &Vc,
    projections: &HashSet<String>,
    alias: Option<(&str, &str)>, // (alias let name, pattern expr)
) -> Vec<String> {
    let mut arg_texts = String::new();
    for n in &vc.spine {
        if let Node::Call { args, .. } = n {
            for a in args {
                arg_texts.push_str(&a.text);
                arg_texts.push('\u{1}');
            }
        }
    }
    let mut out = Vec::new();
    for n in &vc.spine {
        match n {
            Node::Let { name, v } => {
                if projections.contains(name) || !referenced(name, &arg_texts) {
                    continue;
                }
                match alias {
                    Some((an, pat)) if an == name => {
                        out.push(format!("let {} := {};", name, pat))
                    }
                    _ => out.push(format!("let {} := {};", name, v)),
                }
            }
            // Hoisted-let binders replay UNCONDITIONALLY: their ∀ is
            // always instantiated with the let-bound name, and their
            // equation premise closes by rfl against the let value.
            // Spine order preserves later-references-earlier chains.
            Node::HoistEq { binder, v } => {
                out.push(format!("let {} := {};", binder, v));
            }
            _ => {}
        }
    }
    out
}

/// R-b pre-pass: the wf params THIS fn's signature must carry —
/// every callee wf param fed by one of our own params, plus (fix
/// only) the scrutinee when any expr-fed bound or wf demand resolves
/// to a scrutinee projection. Returns (param, dt) in param order.
fn own_wf_demands(
    sc: &FnSidecar,
    ctx: &Ctx,
    param_names: &[&str],
    scrut_param: Option<&str>,
    projections_exist: bool,
) -> Result<Vec<(String, String)>, String> {
    let mut needs: HashMap<String, String> = HashMap::new(); // param → dt
    let mut scrut_dt: Option<String> = None;
    for vc in &sc.vcs {
        for n in &vc.spine {
            let Node::Call { callee, is_self, args } = n else { continue };
            // Callee wf demands (self excluded: own demand mirrors).
            if !is_self {
                if let Some(meta) = ctx.closed.get(callee.as_str()) {
                    let callee_lead: Vec<&Node> = ctx
                        .sidecars
                        .get(callee.as_str())
                        .and_then(|c| c.vcs.first())
                        .map(|v| leading_alls(&v.spine).0.iter().collect())
                        .unwrap_or_default();
                    let pnames: Vec<&str> = callee_lead
                        .iter()
                        .filter_map(|cn| match cn {
                            Node::All { name, .. }
                                if !(name.starts_with("h_") && name.ends_with("_bound")) =>
                            {
                                Some(name.as_str())
                            }
                            _ => None,
                        })
                        .collect();
                    for (wp, dt) in &meta.wf_params {
                        // bootstrap-79: boxed callee params key their
                        // wf demand as `<param>.deref` — match the base.
                        let base_wp = wp.strip_suffix(".deref").unwrap_or(wp);
                        let i = pnames
                            .iter()
                            .position(|p| *p == base_wp)
                            .ok_or_else(|| format!("wf param {} not in {}", wp, callee))?;
                        let a = &args[i];
                        if let Some(t) = a.tag.strip_prefix("param:") {
                            needs.insert(t.to_string(), dt.clone());
                        } else {
                            // Everything else (scrutinee children,
                            // spec-fn results, ctors, let names) is
                            // resolved at APPLICATION time, where the
                            // arm context and let tables exist — and
                            // where the precise error text (with the
                            // let-expanded value) feeds R-c demand
                            // collection.
                        }
                    }
                }
            }
        }
    }
    let _ = (scrut_param, projections_exist);
    let mut out = Vec::new();
    for p in param_names {
        if let Some(dt) = needs.get(*p) {
            out.push((p.to_string(), dt.clone()));
        }
    }
    let _ = scrut_dt;
    Ok(out)
}

// ── the closers ─────────────────────────────────────────────────────

/// Zero-spine: single binders-only postcondition VC.
fn close_zero_spine(rel: &str, sc: &FnSidecar) -> Option<Outcome> {
    if sc.vcs.len() != 1 || !sc.vcs[0].is_post {
        return None;
    }
    if !sc.vcs[0].spine.iter().all(|n| matches!(n, Node::All { .. })) {
        return None;
    }
    let vc = &sc.vcs[0].name;
    Some(Outcome::Closed {
        text: format!("theorem {}_closed : {}_stmt := {}_closed\n", rel, vc, vc),
        kind: "zero-spine",
        meta: ClosedMeta::default(),
    })
}

/// Parse a resolver failure into an own-wf-hypothesis demand: the
/// failing arg must be one of OUR params (`c`) or a boxed param's
/// deref (`inv_hyps.deref`). Returns (arg-key, dt).
fn parse_own_wf_demand(err: &str, param_names: &[&str]) -> Option<(String, String)> {
    let start = err.find("wf-transport for arg `")? + 22;
    let rest = &err[start..];
    let end = rest.find('`')?;
    let x = &rest[..end];
    let base = x.strip_suffix(".deref").unwrap_or(x);
    if !param_names.contains(&base) {
        return None;
    }
    let after = &rest[end..];
    let dstart = after.find(" (")? + 2;
    let dend = after[dstart..].find("Wf")? + dstart;
    Some((x.to_string(), after[dstart..dend].to_string()))
}

/// Straight-line: no branches, no heights, no self-calls.
fn close_straight_line(rel: &str, sc: &FnSidecar, ctx: &Ctx) -> Result<Outcome, String> {
    let posts: Vec<&Vc> = sc.vcs.iter().filter(|v| v.is_post).collect();
    if posts.is_empty() {
        return Err("no postcondition VC".into());
    }
    if sc.vcs.iter().any(|v| !v.is_post) {
        return Err("non-postcondition VCs in straight-line fn".into());
    }
    for w in posts.windows(2) {
        if w[0].spine != w[1].spine {
            return Err("divergent straight-line spines".into());
        }
    }
    for vc in &sc.vcs {
        for n in &vc.spine {
            if let Node::Call { callee, is_self: false, .. } = n {
                if !ctx.closed.contains_key(callee.as_str()) {
                    return Err(format!("awaits {}_closed", callee));
                }
            }
        }
    }
    let p0 = posts[0];
    let (lead, _) = leading_alls(&p0.spine);
    // A hoisted binder in a postcondition leaf would leave the closed
    // statement ill-formed (its `let` replays in the term, not the
    // type) — pend precisely instead of emitting a Lean error.
    for b in hoist_binder_names(&p0.spine) {
        if posts.iter().any(|p| referenced(b, &p.leaf)) {
            return Err(format!("hoisted binder {} in postcondition leaf", b));
        }
    }
    let param_names: Vec<&str> = lead
        .iter()
        .filter_map(|n| match n {
            Node::All { name, .. }
                if !(name.starts_with("h_") && name.ends_with("_bound")) =>
            {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    // R-b: propagated wf demands become own signature hypotheses.
    // R-c: resolver failures naming OWN params (or their derefs) are
    // ALSO own-hypothesis demands — retry, accumulating them, until
    // the build settles or fails for a non-parameter reason.
    let mut wf_params = own_wf_demands(sc, ctx, &param_names, None, false)?;
    let no_comps: HashMap<String, (String, bool)> = HashMap::new();
    let let_table: HashMap<String, String> = p0
        .spine
        .iter()
        .filter_map(|n| match n {
            Node::Let { name, v } => Some((name.clone(), v.clone())),
            _ => None,
        })
        .collect();
    let (apps, own_wf, meta) = loop {
        let own_wf: HashMap<String, String> = wf_params
            .iter()
            .map(|(p, _)| {
                let base = p.strip_suffix(".deref").unwrap_or(p);
                (p.clone(), format!("hwf_{}", base))
            })
            .collect();
        let meta = ClosedMeta { wf_params: wf_params.clone() };
        let env = AppEnv {
            fn_rel: rel,
            scrut_subst: None,
            scrut_alias: None,
            arm_accessors: &[],
            hdec_names: &[],
            sidecars: ctx.sidecars,
            own_lead: lead,
            closed: ctx.closed,
            own_wf: &own_wf,
            arm_comps: &no_comps,
            own_meta: &meta,
            wf_lemmas: ctx.wf_lemmas,
            wf_specs: ctx.wf_specs,
            ns: ctx.ns,
            lets: &let_table,
            guard_prop: None,
            guard_h: None,
        };
        let mut apps = Vec::new();
        let mut err: Option<String> = None;
        for p in &posts {
            match app_text(p, None, &env) {
                Ok(a) => apps.push(a),
                Err(e) => {
                    err = Some(e);
                    break;
                }
            }
        }
        match err {
            None => break (apps, own_wf, meta),
            Some(e) => {
                let demand = parse_own_wf_demand(&e, &param_names);
                match demand {
                    Some((x, d)) if !wf_params.iter().any(|(p, _)| *p == x) => {
                        wf_params.push((x, d));
                    }
                    _ => return Err(e),
                }
            }
        }
    };
    let mut binders: Vec<String> = lead
        .iter()
        .map(|n| match n {
            Node::All { name, ty } => format!("({} : {})", name, ty),
            _ => unreachable!(),
        })
        .collect();
    // The fn's own requires clauses: part of its contract, carried as
    // hypothesis binders (mirrors the hwf_* wf hypotheses) and fed
    // back positionally by app_args' Req arm.
    for n in &p0.spine {
        if let Node::Req { name, prop } = n {
            binders.push(format!("({} : {})", name, prop));
        }
    }
    for (p, dt) in &wf_params {
        let base = p.strip_suffix(".deref").unwrap_or(p);
        binders.push(format!("(hwf_{} : {}Wf {})", base, dt, p));
    }
    let _ = &own_wf;
    let body_ty = posts
        .iter()
        .map(|p| format!("({})", strip_mark(&p.leaf)))
        .collect::<Vec<_>>()
        .join("\n      ∧ ");
    let lets = replay_lets(p0, &HashSet::new(), None);
    let term = if apps.len() == 1 {
        apps.into_iter().next().unwrap()
    } else {
        format!("⟨{}⟩", apps.join(",\n   "))
    };
    let mut text = format!("theorem {}_closed {} :\n    {} :=\n", rel, binders.join(" "), body_ty);
    for l in &lets {
        text.push_str(&format!("  {}\n", l));
    }
    text.push_str(&format!("  {}\n", term));
    Ok(Outcome::Closed { text, kind: "straight-line", meta })
}

/// bootstrap-79 (assert VCs in recursive fn): compose an if-split
/// conjunct — two post VCs sharing one leaf, distinguished by a
/// non-variant guard (the b79 part-lemma calls' first requires
/// premise). Validates the shape (exactly one requires-carrying callee
/// per side, complementary guard props) and emits
/// `if h : <guard> then <pos app> else <neg app>`; inside, the
/// guard-fed premises (Branch{None}, guard-shaped requires) take `h`.
/// Any other shape pends loud.
fn if_split_text(pos: &Vc, neg: &Vc, env: &AppEnv) -> Result<String, String> {
    let req_callee = |vc: &Vc| -> Result<String, String> {
        let mut found: Option<String> = None;
        for n in &vc.spine {
            let Node::Call { callee, is_self: false, .. } = n else { continue };
            let has_reqs = env.sidecars.get(callee.as_str()).map_or(false, |c| {
                c.vcs.iter().any(|v| v.spine.iter().any(|m| matches!(m, Node::Req { .. })))
            });
            if has_reqs {
                if found.is_some() {
                    return Err("if-split branch with >1 requires-carrying call".into());
                }
                found = Some(callee.clone());
            }
        }
        found.ok_or_else(|| "if-split branch without a requires-carrying call".into())
    };
    let first_req_prop = |c: &str| -> Result<String, String> {
        env.sidecars
            .get(c)
            .and_then(|sc| {
                sc.vcs.iter().flat_map(|v| v.spine.iter()).find_map(|n| match n {
                    Node::Req { prop, .. } => Some(prop.clone()),
                    _ => None,
                })
            })
            .ok_or_else(|| format!("callee {} lacks a requires premise", c))
    };
    let c1 = req_callee(pos)?;
    let c2 = req_callee(neg)?;
    let p1 = first_req_prop(&c1)?;
    let p2 = first_req_prop(&c2)?;
    let (guard, vc_pos, vc_neg) = if p2 == format!("¬({})", p1) {
        (p1, pos, neg)
    } else if p1 == format!("¬({})", p2) {
        (p2, neg, pos)
    } else {
        return Err(format!("if-split guards not complementary: `{}` vs `{}`", p1, p2));
    };
    let genv = AppEnv { guard_prop: Some(&guard), guard_h: Some("h"), ..*env };
    Ok(format!(
        "if h : {} then\n        {}\n      else\n        {}",
        guard,
        app_text(vc_pos, None, &genv)?,
        app_text(vc_neg, None, &genv)?
    ))
}

/// Fix synthesis: lowered-match recursion (single scrutinee).
fn close_fix(rel: &str, sc: &FnSidecar, ctx: &Ctx) -> Result<Outcome, String> {
    let posts: Vec<&Vc> = sc.vcs.iter().filter(|v| v.is_post).collect();
    let terms: Vec<&Vc> = sc.vcs.iter().filter(|v| v.is_term).collect();
    // bootstrap-79: assert VCs are allowed in a recursive fn ONLY as
    // `_tactus_precondition_` VCs — the requires discharge of a
    // requires-carrying callee (the b79 part-lemmas). They are not
    // composed directly: the callee's requires are fed at the call
    // site (guard from the woven `if`, caller-IH self-closed apps).
    // Any other assert class stays a loud pend.
    for v in &sc.vcs {
        if !v.is_post && !v.is_term && !v.name.contains("_tactus_precondition_") {
            return Err(format!("unclassified assert VC {} in recursive fn", v.name));
        }
    }
    // Hoist/requires composition is validated on the straight-line
    // path only (no recursive instance exists today) — pend loudly
    // rather than synthesize an unvalidated fix shape.
    if sc.vcs.iter().any(|v| {
        v.spine.iter().any(|n| matches!(n, Node::HoistEq { .. } | Node::Req { .. }))
    }) {
        return Err("hoist/requires spine in recursive fn (unvalidated)".into());
    }
    for vc in &sc.vcs {
        for n in &vc.spine {
            if let Node::Call { callee, is_self: false, .. } = n {
                if !ctx.closed.contains_key(callee.as_str()) {
                    return Err(format!("awaits {}_closed", callee));
                }
            }
        }
    }
    // Scrutinee: every branch must be a variant test on ONE var, one dt.
    // bootstrap-79: test-less Branch nodes (a proof-level non-variant
    // guard, e.g. the break-form `is_skip` if) are exempt — they weave
    // as the arm's nested `if`, not as match discriminants.
    let mut scrut_var: Option<&str> = None;
    let mut dt: Option<&str> = None;
    for vc in &sc.vcs {
        for n in &vc.spine {
            if let Node::Branch { test: Some(t) } = n {
                if *scrut_var.get_or_insert(&t.scrut) != t.scrut {
                    return Err("multi-scrutinee match".into());
                }
                if *dt.get_or_insert(&t.dt) != t.dt {
                    return Err("multi-datatype match".into());
                }
            }
        }
    }
    let scrut_var = scrut_var.ok_or("fix without branches")?;
    let dt = dt.ok_or("fix without datatype")?;
    let variants = ctx.variants.get(dt).ok_or_else(|| format!("unknown datatype {}", dt))?;
    let p0 = posts.first().ok_or("no postcondition VC")?;
    let (lead, _) = leading_alls(&p0.spine);
    let param_names: Vec<&str> = lead
        .iter()
        .filter_map(|n| match n {
            Node::All { name, .. }
                if !(name.starts_with("h_") && name.ends_with("_bound")) =>
            {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    // Resolve the scrutinee var through the alias let to a param.
    let mut alias_of: HashMap<&str, &str> = HashMap::new();
    for n in &p0.spine {
        if let Node::Let { name, v } = n {
            alias_of.insert(name, v);
        }
    }
    let scrut_param: &str = if param_names.contains(&scrut_var) {
        scrut_var
    } else {
        let v = alias_of
            .get(scrut_var)
            .copied()
            .ok_or_else(|| format!("scrutinee {} is neither param nor alias", scrut_var))?;
        if !param_names.contains(&v) {
            return Err(format!("scrutinee alias {} does not resolve to a param", scrut_var));
        }
        v
    };
    let alias_name: Option<&str> =
        if scrut_param == scrut_var { None } else { Some(scrut_var) };

    // R-b: does this fn need `hwf : {Dt}Wf {scrut}`? Yes when any
    // expr-fed bounded callee arg exists (only scrutinee-projection
    // components can discharge them) or any callee/self wf demand is
    // fed by a scrutinee child (`.deref` text).
    let mut need_scrut_wf = false;
    for vc in &sc.vcs {
        for n in &vc.spine {
            let Node::Call { callee, is_self, args } = n else { continue };
            let callee_rel = if *is_self { rel } else { callee.as_str() };
            let callee_lead: Vec<&Node> = ctx
                .sidecars
                .get(callee_rel)
                .and_then(|c| c.vcs.first())
                .map(|v| leading_alls(&v.spine).0.iter().collect())
                .unwrap_or_default();
            let mut arg_i = 0usize;
            for cn in &callee_lead {
                let Node::All { name, .. } = cn else { continue };
                if name.starts_with("h_") && name.ends_with("_bound") {
                    if let Some(a) = args.get(arg_i.wrapping_sub(1)) {
                        if a.tag == "expr" {
                            need_scrut_wf = true;
                        }
                    }
                } else {
                    arg_i += 1;
                }
            }
            if !is_self {
                if let Some(meta) = ctx.closed.get(callee.as_str()) {
                    // Scrut wf is needed only when a deref-of-child arg
                    // feeds a WF-PARAM position specifically.
                    let pnames: Vec<&str> = callee_lead
                        .iter()
                        .filter_map(|cn| match cn {
                            Node::All { name, .. }
                                if !(name.starts_with("h_")
                                    && name.ends_with("_bound")) =>
                            {
                                Some(name.as_str())
                            }
                            _ => None,
                        })
                        .collect();
                    for (wp, _) in &meta.wf_params {
                        if let Some(i) = pnames.iter().position(|p| p == wp) {
                            if args.get(i).map(|a| a.text.ends_with(".deref"))
                                == Some(true)
                            {
                                need_scrut_wf = true;
                            }
                        }
                    }
                }
            }
        }
    }
    let wf_info = ctx.wf.get(dt);
    if need_scrut_wf && wf_info.is_none() {
        return Err(format!("no wf predicate for {}", dt));
    }
    // Self-recursion through a scrut child ⇒ the IH needs the child's
    // wf ⇒ we must take scrut wf whenever the fn is recursive AND has
    // a wf predicate demand anywhere. (A recursive fn with no bound
    // demands anywhere keeps its plain signature — holds_all_append.)
    let propagated = own_wf_demands(sc, ctx, &param_names, Some(scrut_param), true)?;
    let mut wf_params: Vec<(String, String)> = Vec::new();
    for p in &param_names {
        if *p == scrut_param && need_scrut_wf {
            wf_params.push((p.to_string(), dt.to_string()));
        } else if let Some((_, d)) = propagated.iter().find(|(q, _)| q == p) {
            wf_params.push((p.to_string(), d.clone()));
        }
    }
    let own_wf: HashMap<String, String> = wf_params
        .iter()
        .map(|(p, _)| {
            let b = if p == scrut_param { "hwf".to_string() } else { format!("hwf_{}", p) };
            (p.clone(), b)
        })
        .collect();
    let meta = ClosedMeta { wf_params: wf_params.clone() };

    let sig_of = |vc: &Vc| -> Vec<(String, bool)> {
        vc.spine
            .iter()
            .filter_map(|n| match n {
                Node::Branch { test: Some(t) } => Some((t.variant.clone(), t.pos)),
                _ => None,
            })
            .collect()
    };
    let variant_of_sig = |sig: &[(String, bool)]| -> Result<String, String> {
        if let Some((v, _)) = sig.iter().find(|(_, pos)| *pos) {
            Ok(v.clone())
        } else {
            let negated: HashSet<&str> = sig.iter().map(|(v, _)| v.as_str()).collect();
            let rest: Vec<&str> = variants
                .iter()
                .map(|(v, _)| v.as_str())
                .filter(|v| !negated.contains(v))
                .collect();
            if rest.len() == 1 {
                Ok(rest[0].to_string())
            } else {
                Err(format!("else-arm variant ambiguous ({} candidates)", rest.len()))
            }
        }
    };

    let mut arm_sigs: Vec<Vec<(String, bool)>> = Vec::new();
    for p in &posts {
        let sig = sig_of(p);
        if !arm_sigs.contains(&sig) {
            arm_sigs.push(sig);
        }
    }
    let conjuncts: Vec<&str> = {
        let mut seen = Vec::new();
        for p in &posts {
            let l = strip_mark(&p.leaf);
            if !seen.contains(&l) {
                seen.push(l);
            }
        }
        seen
    };

    let mut arms_text: Vec<String> = Vec::new();
    let mut any_heights = false;
    for sig in &arm_sigs {
        let variant = variant_of_sig(sig)?;
        let accessors: &Vec<String> = variants
            .iter()
            .find(|(v, _)| *v == variant)
            .map(|(_, a)| a)
            .ok_or_else(|| format!("variant {} not in datatype {}", variant, dt))?;
        let arity = accessors.len();
        let arm_posts: Vec<&Vc> = posts.iter().copied().filter(|p| sig_of(p) == *sig).collect();
        let arm_terms: Vec<&Vc> = terms.iter().copied().filter(|t| sig_of(t) == *sig).collect();
        // Per-conjunct groups: normally ONE post VC per conjunct leaf.
        // bootstrap-79: TWO post VCs sharing a conjunct leaf are an
        // if-split candidate (the arm's proof branches on a
        // non-variant guard — validated at emission in `if_split_text`).
        let arm_post_groups: Vec<Vec<&Vc>> = conjuncts
            .iter()
            .map(|c| {
                arm_posts
                    .iter()
                    .copied()
                    .filter(|p| strip_mark(&p.leaf) == *c)
                    .collect()
            })
            .collect();
        for g in &arm_post_groups {
            if g.is_empty() {
                return Err("arm missing a conjunct".into());
            }
            if g.len() > 2 {
                return Err("arm has >2 post VCs for one conjunct (unclassified split)".into());
            }
        }
        let arm_posts: Vec<&Vc> = arm_post_groups.iter().map(|g| g[0]).collect();
        let base = alias_name.unwrap_or(scrut_param);
        let mut field_names: Vec<Option<String>> = vec![None; arity];
        let mut field_accessor: Vec<Option<String>> = vec![None; arity];
        let mut projections: HashSet<String> = HashSet::new();
        // Projection lets: `<base>.<Variant>_<accessor>` — accessor is
        // `val<N>` (positional) or the field name. Field INDEX comes
        // from the wf/variant field table via accessor order; for
        // `val<N>` it is N directly, for named accessors we take the
        // conjunct-table order (generate.rs records accessors in
        // declaration order per variant).

        for n in &arm_posts[0].spine {
            if let Node::Let { name, v } = n {
                let pref = format!("{}.{}_", base, variant);
                if let Some(acc) = v.strip_prefix(&pref) {
                    // Accessor → field index: `val<N>` is positional;
                    // named accessors index into the declaration-order
                    // accessor list from the krate.
                    let idx = if let Some(num) = acc.strip_prefix("val") {
                        num.parse::<usize>().ok()
                    } else {
                        accessors.iter().position(|a| a == acc)
                    };
                    if let Some(i) = idx {
                        if i < arity {
                            field_names[i] = Some(name.clone());
                            field_accessor[i] = Some(acc.to_string());
                            projections.insert(name.clone());
                        }
                    }
                }
            }
        }
        let arg_texts_all: String = arm_posts[0]
            .spine
            .iter()
            .filter_map(|n| match n {
                Node::Call { args, .. } => Some(
                    args.iter().map(|a| a.text.as_str()).collect::<Vec<_>>().join("\u{1}"),
                ),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("\u{1}");
        let alias_referenced =
            alias_name.map(|a| referenced(a, &arg_texts_all)).unwrap_or(false);
        let binder_texts: Vec<String> = field_names
            .iter()
            .enumerate()
            .map(|(i, n)| match n {
                Some(n) => n.clone(),
                // Always named (never `_`): N2 field binders in the VC
                // statement instantiate with the pattern's tokens.
                None => format!("_pb{}", i),
            })
            .collect();
        let pattern = if arity == 0 {
            format!("{}.{}", dt, variant)
        } else {
            format!("{}.{} {}", dt, variant, binder_texts.join(" "))
        };
        let arm_accessor_list: Vec<String> = field_accessor
            .iter()
            .enumerate()
            .map(|(i, a)| a.clone().unwrap_or_else(|| format!("val{}", i)))
            .collect();
        // R-b: arm wf destructuring + component lookup table.
        let mut arm_comps: HashMap<String, (String, bool)> = HashMap::new();
        let wf_pattern: Option<String> = if need_scrut_wf {
            let comps: Vec<&WfComp> = wf_info
                .and_then(|w| w.variants.get(&variant))
                .map(|cs| cs.iter().collect())
                .unwrap_or_default();
            let mut names = Vec::new();
            for c in &comps {
                let bname = if c.rec {
                    format!("hwf_{}", c.accessor)
                } else {
                    format!("h_wf_{}", c.accessor)
                };
                // Bind the component to the PROJECTION-LET name that
                // projects this accessor (if the arm projects it) AND
                // to the raw projection text (`tmp___0.Ret_val1`) —
                // unboxed rec conjuncts feed wf resolution directly.
                if let Some(pi) = field_accessor.iter().position(|a| {
                    a.as_deref() == Some(c.accessor.as_str())
                }) {
                    if let Some(pn) = &field_names[pi] {
                        arm_comps.insert(pn.clone(), (bname.clone(), c.rec));
                    }
                }
                arm_comps.insert(
                    format!("{}.{}_{}", base, variant, c.accessor),
                    (bname.clone(), c.rec),
                );
                names.push(bname);
            }
            Some(match names.len() {
                0 => "_".to_string(),
                // Single-conjunct wf clause: bare Prop, no ⟨⟩ pattern.
                1 => names.into_iter().next().unwrap(),
                _ => format!("⟨{}⟩", names.join(", ")),
            })
        } else {
            None
        };
        let heights: Vec<usize> = arm_posts[0]
            .spine
            .iter()
            .enumerate()
            .filter_map(|(i, n)| matches!(n, Node::Height).then_some(i))
            .collect();
        if !heights.is_empty() {
            any_heights = true;
        }
        let let_table: HashMap<String, String> = arm_posts[0]
            .spine
            .iter()
            .filter_map(|n| match n {
                Node::Let { name, v } => Some((name.clone(), v.clone())),
                _ => None,
            })
            .collect();
        let mut hdec_names = Vec::new();
        let mut haves = Vec::new();
        let env0 = AppEnv {
            fn_rel: rel,
            scrut_subst: Some((scrut_param, &pattern)),
            scrut_alias: alias_name,
            arm_accessors: &arm_accessor_list,
            hdec_names: &[],
            sidecars: ctx.sidecars,
            own_lead: lead,
            closed: ctx.closed,
            own_wf: &own_wf,
            arm_comps: &arm_comps,
            own_meta: &meta,
            wf_lemmas: ctx.wf_lemmas,
            wf_specs: ctx.wf_specs,
            ns: ctx.ns,
            lets: &let_table,
            guard_prop: None,
            guard_h: None,
        };
        // Height premises weave in via `have hdec := <term-thm app>`
        // INSIDE the arm (self-refs legal there). The decreasing goals
        // themselves close DIRECTLY — height defs are WF-compiled, so
        // their equations exist and `simp [height] <;> omega` decides
        // every structural-child inequality. Term-thm applications in
        // decreasing_by would be illegal anyway: multi-self-call arms'
        // later term VCs carry self-referencing premises.
        for (j, hi) in heights.iter().enumerate() {
            let tvc = arm_terms
                .iter()
                .find(|t| t.spine.len() == *hi && t.spine[..] == arm_posts[0].spine[..*hi])
                .ok_or("height premise without prefix-matching termination VC")?;
            let name = if heights.len() == 1 {
                "hdec".to_string()
            } else {
                format!("hdec{}", j)
            };
            let tapp = {
                let env_j = AppEnv { hdec_names: &hdec_names, ..env0 };
                app_text(tvc, None, &env_j)?
            };
            haves.push(format!("have {} := {}", name, tapp));
            hdec_names.push(name);
        }
        let env = AppEnv {
            fn_rel: rel,
            scrut_subst: Some((scrut_param, &pattern)),
            scrut_alias: alias_name,
            arm_accessors: &arm_accessor_list,
            hdec_names: &hdec_names,
            sidecars: ctx.sidecars,
            own_lead: lead,
            closed: ctx.closed,
            own_wf: &own_wf,
            arm_comps: &arm_comps,
            own_meta: &meta,
            wf_lemmas: ctx.wf_lemmas,
            wf_specs: ctx.wf_specs,
            ns: ctx.ns,
            lets: &let_table,
            guard_prop: None,
            guard_h: None,
        };
        let lets = replay_lets(
            arm_posts[0],
            &projections,
            alias_name.map(|a| (a, pattern.as_str())),
        );
        let mut apps = Vec::new();
        for g in &arm_post_groups {
            if g.len() == 1 {
                apps.push(app_text(g[0], None, &env)?);
            } else {
                apps.push(if_split_text(g[0], g[1], &env)?);
            }
        }
        let final_term = if apps.len() == 1 {
            apps.into_iter().next().unwrap()
        } else {
            format!("⟨{}⟩", apps.join(",\n     "))
        };
        let arm_head = match &wf_pattern {
            Some(wp) => format!("  | {}, {} =>\n", pattern, wp),
            None => format!("  | {} =>\n", pattern),
        };
        let mut arm = arm_head;
        for l in &lets {
            arm.push_str(&format!("      {}\n", l));
        }
        for h in &haves {
            arm.push_str(&format!("      {}\n", h));
        }
        arm.push_str(&format!("      {}", final_term));
        arms_text.push(arm);
    }

    let measure = {
        let t0 = terms.first().ok_or("recursive fn without termination VC")?;
        let leaf = strip_mark(&t0.leaf);
        let first = leaf.split(" ∨ ").next().unwrap_or(leaf);
        let rhs = first
            .split(" < ")
            .nth(1)
            .ok_or("unrecognized termination leaf shape")?
            .trim()
            .trim_end_matches(')');
        let mut m = rhs.to_string();
        for n in &p0.spine {
            if let Node::Let { name, v } = n {
                if referenced(name, &m) {
                    m = m.replace(name, v);
                }
            }
        }
        m
    };

    let mut binders: Vec<String> = lead
        .iter()
        .map(|n| match n {
            Node::All { name, ty } => format!("({} : {})", name, ty),
            _ => unreachable!(),
        })
        .collect();
    for (p, d) in &wf_params {
        let b = &own_wf[p];
        binders.push(format!("({} : {}Wf {})", b, d, p));
    }
    let body_ty = conjuncts
        .iter()
        .map(|c| format!("({})", c))
        .collect::<Vec<_>>()
        .join("\n      ∧ ");
    let match_head = if need_scrut_wf {
        format!("match {}, hwf with", scrut_param)
    } else {
        format!("match {} with", scrut_param)
    };
    let mut text = format!(
        "theorem {}_closed {} :\n    {} :=\n  {}\n{}\n",
        rel,
        binders.join(" "),
        body_ty,
        match_head,
        arms_text.join("\n")
    );
    text.push_str(&format!("termination_by {}\n", measure));
    if any_heights {
        // `<;>`: simp may CLOSE a goal outright — a sequenced `; omega`
        // then dies with "no goals"; `<;>` applies omega only to
        // whatever simp leaves.
        text.push_str(&format!(
            "decreasing_by all_goals (simp only [{}.height, {}] <;> omega)\n",
            dt,
            crate::tactic_select::TERM_SIMP_LEMMAS
        ));
    }
    Ok(Outcome::Closed { text, kind: "fix", meta })
}

/// One fn: classify and synthesize.
pub fn try_close(rel: &str, sc: &FnSidecar, ctx: &Ctx) -> Outcome {
    if let Some(o) = close_zero_spine(rel, sc) {
        return o;
    }
    let has_branch = sc.vcs.iter().any(|v| v.spine.iter().any(|n| matches!(n, Node::Branch { .. })));
    let has_self = sc.vcs.iter().any(|v| {
        v.spine.iter().any(|n| matches!(n, Node::Call { is_self: true, .. } | Node::Height))
    });
    let r = if has_branch || has_self {
        close_fix(rel, sc, ctx)
    } else {
        close_straight_line(rel, sc, ctx)
    };
    match r {
        Ok(o) => o,
        Err(e) => pend(e),
    }
}

#[cfg(test)]
#[path = "tests/link_discharge.rs"]
mod tests;
