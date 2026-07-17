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
                    // absorbed leading hyp (`_h_ctx_N` binder) — same
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
    /// Relative fn names whose `<rel>_closed` is already emitted.
    pub closed: &'a HashSet<String>,
    /// Datatype (relative name) → ordered [(variant, arity)].
    pub variants: &'a HashMap<String, Vec<(String, usize)>>,
}

pub enum Outcome {
    Closed { text: String, kind: &'static str },
    Pending(String),
}

fn pend(reason: impl Into<String>) -> Outcome {
    Outcome::Pending(reason.into())
}

/// Word-boundary occurrence check (is `name` referenced in `text`?).
fn referenced(name: &str, text: &str) -> bool {
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
fn leading_alls(spine: &[Node]) -> (&[Node], usize) {
    let n = spine
        .iter()
        .take_while(|n| matches!(n, Node::All { ty, .. } if ty != "Unit"))
        .count();
    (&spine[..n], n)
}

/// Does this fn's own or any callee's clean signature carry
/// `h_*_bound` binders? (The wf-rung gap — pending until R-b.)
fn bound_gap(sc: &FnSidecar, ctx: &Ctx) -> Option<String> {
    let has_bounds = |spine: &[Node]| {
        leading_alls(spine).0.iter().any(|n| match n {
            Node::All { name, .. } => name.starts_with("h_") && name.ends_with("_bound"),
            _ => false,
        })
    };
    // Own bound binders are plain leading Alls — positionally harmless
    // — EXCEPT when a self-call (IH) must reproduce them interleaved,
    // which needs the wf rung.
    let recursive = sc.vcs.iter().any(|v| {
        v.spine.iter().any(|n| matches!(n, Node::Call { is_self: true, .. }))
    });
    for vc in &sc.vcs {
        if recursive && has_bounds(&vc.spine) {
            return Some("own scalar bounds on recursive fn (wf rung)".to_string());
        }
        for n in &vc.spine {
            if let Node::Call { callee, is_self: false, args } = n {
                let csc = match ctx.sidecars.get(callee) {
                    Some(c) => c,
                    None => return Some(format!("no sidecar for callee {}", callee)),
                };
                // A bounded callee param is dischargeable when its arg
                // is a caller param (own h_*_bound binder) or a literal
                // (by omega); only EXPR-fed bounds need the wf rung.
                let Some(first) = csc.vcs.first() else { continue };
                let mut arg_i = 0usize;
                for a in leading_alls(&first.spine).0 {
                    if let Node::All { name, .. } = a {
                        if name.starts_with("h_") && name.ends_with("_bound") {
                            let feeder = args.get(arg_i.wrapping_sub(1));
                            match feeder.map(|f| f.tag.as_str()) {
                                Some(t) if t.starts_with("param:") || t == "lit" => {}
                                _ => {
                                    return Some(format!(
                                        "bound-gap via {} (wf rung)",
                                        callee
                                    ))
                                }
                            }
                        } else {
                            arg_i += 1;
                        }
                    }
                }
            }
        }
    }
    None
}

// ── positional application builder ──────────────────────────────────

struct AppEnv<'a> {
    fn_rel: &'a str,
    /// Scrutinee param name → the arm's pattern expression (fix arms).
    scrut_subst: Option<(&'a str, &'a str)>,
    /// Names for the `have hdec{j}` bindings, consumed in order.
    hdec_names: &'a [String],
    /// Callee sidecars — the callee's leading Alls give the
    /// interleaved (param, h_*_bound) application order.
    sidecars: &'a HashMap<String, FnSidecar>,
    /// The caller's own leading Alls (bound-recipe lookups).
    own_lead: &'a [Node],
}

/// Build the positional application of `vc`'s theorem through the
/// first `upto` spine nodes (None = all). Returns the argument list.
fn app_args(vc: &Vc, upto: Option<usize>, env: &AppEnv) -> Result<Vec<String>, String> {
    let mut args = Vec::new();
    let (_, n_lead) = leading_alls(&vc.spine);
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
                } else {
                    return Err(format!("value-returning callee binder {}", name));
                }
            }
            Node::Let { .. } => {}
            Node::Branch { .. } => args.push("(by simp)".to_string()),
            Node::Height => {
                let h = env
                    .hdec_names
                    .get(hdec_idx)
                    .ok_or_else(|| "height premise without termination VC".to_string())?;
                args.push(h.clone());
                hdec_idx += 1;
            }
            Node::Call { callee, is_self, args: cargs } => {
                let head = if *is_self {
                    format!("{}_closed", env.fn_rel)
                } else {
                    format!("{}_closed", callee)
                };
                // Interleave bound proofs per the callee's own leading-
                // All order (params and their h_*_bound binders).
                let callee_lead: Vec<&Node> = env
                    .sidecars
                    .get(if *is_self { env.fn_rel } else { callee.as_str() })
                    .and_then(|c| c.vcs.first())
                    .map(|v| leading_alls(&v.spine).0.iter().collect())
                    .unwrap_or_default();
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
                                    return Err(format!(
                                        "expr-fed bound at {} (wf rung)",
                                        callee
                                    ))
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
                }
                t.push(')');
                args.push(t);
            }
            Node::Other => return Err("other-hyp in spine".to_string()),
        }
    }
    Ok(args)
}

fn app_text(vc: &Vc, upto: Option<usize>, env: &AppEnv) -> Result<String, String> {
    let args = app_args(vc, upto, env)?;
    Ok(format!("{} {}", vc.name, args.join(" ")))
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
        if let Node::Let { name, v } = n {
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
    }
    out
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
    })
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
                if !ctx.closed.contains(callee) {
                    return Err(format!("awaits {}_closed", callee));
                }
            }
        }
    }
    let p0 = posts[0];
    let (lead, _) = leading_alls(&p0.spine);
    let binders: Vec<String> = lead
        .iter()
        .map(|n| match n {
            Node::All { name, ty } => format!("({} : {})", name, ty),
            _ => unreachable!(),
        })
        .collect();
    let env = AppEnv {
        fn_rel: rel,
        scrut_subst: None,
        hdec_names: &[],
        sidecars: ctx.sidecars,
        own_lead: lead,
    };
    let mut apps = Vec::new();
    for p in &posts {
        apps.push(app_text(p, None, &env).map_err(|e| e)?);
    }
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
    Ok(Outcome::Closed { text, kind: "straight-line" })
}

/// Fix synthesis: lowered-match recursion (single scrutinee).
fn close_fix(rel: &str, sc: &FnSidecar, ctx: &Ctx) -> Result<Outcome, String> {
    let posts: Vec<&Vc> = sc.vcs.iter().filter(|v| v.is_post).collect();
    let terms: Vec<&Vc> = sc.vcs.iter().filter(|v| v.is_term).collect();
    if sc.vcs.iter().any(|v| !v.is_post && !v.is_term) {
        return Err("assert VCs in recursive fn".into());
    }
    // Callee availability.
    for vc in &sc.vcs {
        for n in &vc.spine {
            if let Node::Call { callee, is_self: false, .. } = n {
                if !ctx.closed.contains(callee) {
                    return Err(format!("awaits {}_closed", callee));
                }
            }
        }
    }
    // Scrutinee: every branch must be a variant test on ONE var, one dt.
    let mut scrut_var: Option<&str> = None;
    let mut dt: Option<&str> = None;
    for vc in &sc.vcs {
        for n in &vc.spine {
            if let Node::Branch { test } = n {
                let t = test.as_ref().ok_or("non-variant branch in recursive fn")?;
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
        .map(|n| match n {
            Node::All { name, .. } => name.as_str(),
            _ => unreachable!(),
        })
        .collect();
    // Resolve the scrutinee var through the alias let to a param.
    let mut alias_of: HashMap<&str, &str> = HashMap::new(); // let name → value
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

    // Arm signature = the branch-test sequence of a VC's spine.
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

    // Group posts into arms (first-appearance order) and conjuncts.
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
    let mut dec_bullets: Vec<String> = Vec::new();
    for sig in &arm_sigs {
        let variant = variant_of_sig(sig)?;
        let arity = variants
            .iter()
            .find(|(v, _)| *v == variant)
            .map(|(_, a)| *a)
            .ok_or_else(|| format!("variant {} not in datatype {}", variant, dt))?;
        let arm_posts: Vec<&Vc> = posts.iter().copied().filter(|p| sig_of(p) == *sig).collect();
        let arm_terms: Vec<&Vc> = terms.iter().copied().filter(|t| sig_of(t) == *sig).collect();
        // One post per conjunct, in conjunct order.
        if arm_posts.len() != conjuncts.len() {
            return Err("arm/conjunct grid mismatch".into());
        }
        let arm_posts: Vec<&Vc> = conjuncts
            .iter()
            .map(|c| {
                arm_posts
                    .iter()
                    .copied()
                    .find(|p| strip_mark(&p.leaf) == *c)
                    .ok_or_else(|| "arm missing a conjunct".to_string())
            })
            .collect::<Result<_, _>>()?;
        // Pattern binders from projection lets off the alias.
        let base = alias_name.unwrap_or(scrut_param);
        let mut field_names: Vec<Option<String>> = vec![None; arity];
        let mut projections: HashSet<String> = HashSet::new();
        for n in &arm_posts[0].spine {
            if let Node::Let { name, v } = n {
                let pref = format!("{}.{}_val", base, variant);
                if let Some(idx) = v.strip_prefix(&pref) {
                    if let Ok(i) = idx.parse::<usize>() {
                        if i < arity {
                            field_names[i] = Some(name.clone());
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
                None if alias_referenced => format!("_pb{}", i),
                None => "_".to_string(),
            })
            .collect();
        let pattern = if arity == 0 {
            format!("{}.{}", dt, variant)
        } else {
            format!("{}.{} {}", dt, variant, binder_texts.join(" "))
        };
        // Termination VCs of this arm: match each Height position in
        // the (per-arm identical) post spine to the term VC whose spine
        // is the prefix ending right there.
        let heights: Vec<usize> = arm_posts[0]
            .spine
            .iter()
            .enumerate()
            .filter_map(|(i, n)| matches!(n, Node::Height).then_some(i))
            .collect();
        let mut hdec_names = Vec::new();
        let mut haves = Vec::new();
        let env0 = AppEnv {
            fn_rel: rel,
            scrut_subst: Some((scrut_param, &pattern)),
            hdec_names: &[],
            sidecars: ctx.sidecars,
            own_lead: lead,
        };
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
            let tapp = app_text(tvc, None, &env0)?;
            haves.push(format!("have {} := {}", name, tapp));
            dec_bullets.push(format!(
                "  · exact ({}\n      ).resolve_right (fun h => h.2.elim)",
                tapp
            ));
            hdec_names.push(name);
        }
        let env = AppEnv {
            fn_rel: rel,
            scrut_subst: Some((scrut_param, &pattern)),
            hdec_names: &hdec_names,
            sidecars: ctx.sidecars,
            own_lead: lead,
        };
        let lets = replay_lets(
            arm_posts[0],
            &projections,
            alias_name.map(|a| (a, pattern.as_str())),
        );
        let mut apps = Vec::new();
        for p in &arm_posts {
            apps.push(app_text(p, None, &env)?);
        }
        let final_term = if apps.len() == 1 {
            apps.into_iter().next().unwrap()
        } else {
            format!("⟨{}⟩", apps.join(",\n     "))
        };
        let mut arm = format!("  | {} =>\n", pattern);
        for l in &lets {
            arm.push_str(&format!("      {}\n", l));
        }
        for h in &haves {
            arm.push_str(&format!("      {}\n", h));
        }
        arm.push_str(&format!("      {}", final_term));
        arms_text.push(arm);
    }

    // termination_by: the measure is the RHS of the `<` in a term leaf,
    // with spine lets (decrease snapshots) substituted by their values.
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

    let binders: Vec<String> = lead
        .iter()
        .map(|n| match n {
            Node::All { name, ty } => format!("({} : {})", name, ty),
            _ => unreachable!(),
        })
        .collect();
    let body_ty = conjuncts
        .iter()
        .map(|c| format!("({})", c))
        .collect::<Vec<_>>()
        .join("\n      ∧ ");
    let mut text = format!(
        "theorem {}_closed {} :\n    {} :=\n  match {} with\n{}\n",
        rel,
        binders.join(" "),
        body_ty,
        scrut_param,
        arms_text.join("\n")
    );
    text.push_str(&format!("termination_by {}\n", measure));
    if !dec_bullets.is_empty() {
        text.push_str("decreasing_by\n");
        text.push_str(&dec_bullets.join("\n"));
        text.push('\n');
    }
    Ok(Outcome::Closed { text, kind: "fix" })
}

/// One fn: classify and synthesize.
pub fn try_close(rel: &str, sc: &FnSidecar, ctx: &Ctx) -> Outcome {
    if let Some(o) = close_zero_spine(rel, sc) {
        return o;
    }
    if let Some(gap) = bound_gap(sc, ctx) {
        return pend(gap);
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
