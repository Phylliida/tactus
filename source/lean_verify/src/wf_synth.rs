//! R-c: wf-preservation lemma synthesis (board bootstrap-73, probe35/36).
//!
//! For a spec fn `g : … → D` (D scalar-carrying), synthesize
//! `theorem g_wf … : DWf (lib.g …)` whose proof term is ISOMORPHIC to
//! g's own body: constructor ↦ anonymous constructor of components,
//! recursive call ↦ recursive lemma call, spec-fn call ↦ that fn's
//! `_wf` lemma, `match` ↦ match-mirror destructuring the scrutinee's
//! wf hypothesis, `if` (in an arm) ↦ `(congrArg DWf (if_pos h)).mpr`
//! defeq transport, `let` ↦ inline re-synthesis at use. Everything
//! rides defeq iota — no equation lemmas are consulted, so the rec_1
//! gap (no equations for Box-recursing structural defs) never bites.
//! Bound conjuncts discharge by `(by omega)` reading the destructured
//! components from the local context.
//!
//! Failures are Err, never panics — the driver censuses them and the
//! dependent discharge stays pending (honest).

use crate::lean_ast::{Def, Expr, ExprNode, Pattern};
use std::collections::HashMap;

/// One datatype's wf-conjunct structure (mirror of the emitted
/// `{Dt}Wf` def; conjunct order = field order).
pub struct DtWfSpec {
    /// variant → ordered conjuncts (field index, kind).
    pub variants: HashMap<String, Vec<(usize, ConjKind)>>,
}

pub enum ConjKind {
    /// `0 ≤ x ∧ x < N` — proof is `(by omega)`.
    Bound,
    /// `{dt}Wf x[.deref]` — proof synthesized recursively.
    Rec { dt: String, boxed: bool },
}

/// A candidate spec fn's wf-relevant signature.
#[derive(Clone)]
pub struct FnWfSig {
    /// Params in declaration order.
    pub params: Vec<(String, ParamKind)>,
    /// Scalar-carrying return datatype (relative name).
    pub ret_dt: String,
}

#[derive(Clone)]
pub enum ParamKind {
    /// Bounded int (u64 etc.) — lemma takes `(h_{p}_bound : {pred})`.
    Bounded(String),
    /// Scalar-carrying datatype — lemma takes `(hwf_{p} : {dt}Wf {p})`.
    Dt(String),
    /// Anything else — no hypothesis.
    Other,
}

pub struct SynthCtx<'a> {
    pub ns: &'a str,
    pub dts: &'a HashMap<String, DtWfSpec>,
    pub sigs: &'a HashMap<String, FnWfSig>,
    /// dt → [(variant, field accessors in declaration order)] — for
    /// single-variant struct projections (`c.typ_params`).
    pub accessors: &'a HashMap<String, Vec<(String, Vec<String>)>>,
    /// Lemmas already synthesized (callees must precede callers).
    pub done: &'a std::collections::HashSet<String>,
}

/// What a name in scope proves / stands for.
enum Res<'e> {
    /// A hypothesis or destructured component proving wf of the name.
    Proof(String, Option<String> /* dt */),
    /// A let-bound value — re-synthesize (or substitute) at use.
    Inline(&'e Expr),
}

struct Synth<'a, 'e> {
    ctx: &'a SynthCtx<'a>,
    rel: &'a str,
    env: Vec<(String, Res<'e>)>,
    fresh: usize,
    /// Saw a self-call (recursive lemma needs termination_by).
    recursive: bool,
}

fn head_name(e: &Expr) -> Option<&str> {
    match &e.node {
        ExprNode::Var(n) => Some(n.as_str()),
        _ => None,
    }
}

impl<'a, 'e> Synth<'a, 'e> {
    fn lookup(&self, name: &str) -> Option<&Res<'e>> {
        self.env.iter().rev().find(|(n, _)| n == name).map(|(_, r)| r)
    }

    /// pp with `Inline` let-names substituted by their (parenthesized)
    /// values, transitively — used for `by_cases`/`if` condition text
    /// and spec-fn value arguments, where let names from the def body
    /// are not in scope in the lemma.
    fn subst_pp(&self, e: &Expr) -> String {
        let mut t = crate::lean_pp::pp_expr(e);
        // Fixpoint: values may reference earlier lets. BOUNDED — a
        // self-referential value (a shadowing `let x := x.deref` /
        // `let x := x + 1`) reintroduces its own name on every round
        // and the textual fixpoint never converges; without the cap
        // this loop hangs with unbounded string growth. Each round
        // substitutes every inline let once, so `env.len() + 1`
        // rounds suffice for any non-shadowing chain (values only
        // reference EARLIER lets). On cap-out we return the partial
        // text: the leftover name is unbound in the lemma, Lean
        // elaboration fails, and the driver censuses it — the honest
        // failure mode this module promises (never a hang).
        for _ in 0..=self.env.len() {
            let mut changed = false;
            for (n, r) in self.env.iter().rev() {
                if let Res::Inline(v) = r {
                    if crate::link_discharge::referenced(n, &t) {
                        let vp = format!("({})", crate::lean_pp::pp_expr(v));
                        t = crate::link_discharge::replace_word(&t, n, &vp);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        t
    }

    /// A proof of the BOUND conjunct for `e` — named hypotheses when
    /// available. `(by omega)` only as a context-free fallback: tactic
    /// goals inside term-mode match arms can be postponed OUTSIDE the
    /// arm, losing pattern-bound hypotheses (the 686 lesson).
    fn bound_proof(&mut self, e: &'e Expr) -> String {
        match &e.node {
            ExprNode::Var(n) => match self.lookup(n.as_str()) {
                Some(Res::Proof(p, None)) => p.clone(),
                Some(Res::Inline(v)) => {
                    let v = *v;
                    self.bound_proof(v)
                }
                _ => "(by omega)".to_string(),
            },
            _ => "(by omega)".to_string(),
        }
    }

    /// Synthesize a proof of `{want}Wf e`.
    fn term(&mut self, e: &'e Expr, want: &str) -> Result<String, String> {
        match &e.node {
            ExprNode::Var(n) => {
                let name = n.as_str().to_string();
                // Nullary constructors (`lib.FrameList.FNil`) render as
                // bare Vars, not zero-arg Apps.
                if let Some(rest) = name.strip_prefix(&format!("{}.", self.ctx.ns)) {
                    if let Some((d, v)) = rest.split_once('.') {
                        if let Some(spec) = self.ctx.dts.get(d) {
                            if d != want {
                                return Err(format!("ctor {} where {}Wf wanted", d, want));
                            }
                            let conjs = spec
                                .variants
                                .get(v)
                                .ok_or_else(|| format!("unknown variant {}.{}", d, v))?;
                            return if conjs.is_empty() {
                                Ok("trivial".to_string())
                            } else {
                                Err(format!("nullary ctor {}.{} with conjuncts", d, v))
                            };
                        }
                    }
                }
                match self.lookup(&name) {
                    Some(Res::Proof(p, _)) => Ok(p.clone()),
                    Some(Res::Inline(v)) => {
                        let v = *v;
                        self.term(v, want)
                    }
                    None => Err(format!("no wf source for var `{}`", name)),
                }
            }
            ExprNode::FieldProj { expr, field } if field == "deref" => {
                let inner = head_name(expr)
                    .ok_or_else(|| "deref of non-var".to_string())?;
                match self.lookup(inner) {
                    Some(Res::Proof(p, _)) => Ok(p.clone()),
                    _ => Err(format!("no wf source for `{}.deref`", inner)),
                }
            }
            // Single-variant struct projection (`c.typ_params`): the
            // param's wf hyp is a right-nested conjunction; project by
            // `.1`/`.2` path at the field's conjunct position.
            ExprNode::FieldProj { expr, field } => {
                let inner = head_name(expr)
                    .ok_or_else(|| "projection of non-var".to_string())?;
                let (p, d) = match self.lookup(inner) {
                    Some(Res::Proof(p, Some(d))) => (p.clone(), d.clone()),
                    _ => return Err(format!("no wf source for `{}.{}`", inner, field)),
                };
                let variants = self
                    .ctx
                    .accessors
                    .get(&d)
                    .filter(|v| v.len() == 1)
                    .ok_or_else(|| format!("projection on multi-variant {}", d))?;
                let (vname, accs) = &variants[0];
                let fidx = accs
                    .iter()
                    .position(|a| a == field)
                    .ok_or_else(|| format!("unknown field {}.{}", d, field))?;
                let conjs = self
                    .ctx
                    .dts
                    .get(&d)
                    .and_then(|sp| sp.variants.get(vname))
                    .ok_or_else(|| format!("no wf spec for {}", d))?;
                let k = conjs
                    .iter()
                    .position(|(i, _)| *i == fidx)
                    .ok_or_else(|| format!("field {}.{} has no wf conjunct", d, field))?;
                match &conjs[k].1 {
                    ConjKind::Rec { dt, .. } if dt == want => {}
                    ConjKind::Rec { dt, .. } => {
                        return Err(format!("{}.{} is {}Wf, wanted {}Wf", d, field, dt, want))
                    }
                    ConjKind::Bound => {
                        return Err(format!("{}.{} is a bound, wanted {}Wf", d, field, want))
                    }
                }
                let mut path = String::new();
                for _ in 0..k {
                    path.push_str(".2");
                }
                if k < conjs.len() - 1 {
                    path.push_str(".1");
                }
                Ok(format!("{}{}", p, path))
            }
            ExprNode::App { head, args } => {
                let h = head_name(head).ok_or_else(|| "non-var app head".to_string())?;
                // Constructor `{ns}.{D}.{V}`?
                if let Some(rest) = h.strip_prefix(&format!("{}.", self.ctx.ns)) {
                    if let Some((d, v)) = rest.split_once('.') {
                        if let Some(spec) = self.ctx.dts.get(d) {
                            if d != want {
                                return Err(format!("ctor {} where {}Wf wanted", d, want));
                            }
                            let conjs = spec
                                .variants
                                .get(v)
                                .ok_or_else(|| format!("unknown variant {}.{}", d, v))?;
                            let mut parts = Vec::new();
                            for (idx, kind) in conjs {
                                let arg = args
                                    .get(*idx)
                                    .ok_or_else(|| format!("ctor {}.{} arity", d, v))?;
                                match kind {
                                    ConjKind::Bound => {
                                        let bp = self.bound_proof(arg);
                                        parts.push(bp);
                                    }
                                    ConjKind::Rec { dt, boxed } => {
                                        let inner: &Expr = if *boxed {
                                            match &arg.node {
                                                ExprNode::App { head, args }
                                                    if head_name(head)
                                                        == Some("Tactus.Box.mk")
                                                        && args.len() == 1 =>
                                                {
                                                    &args[0]
                                                }
                                                // A bare Box var `t` in ctor
                                                // position: its comp proves
                                                // wf of `t.deref` — same
                                                // thing.
                                                ExprNode::Var(n) => {
                                                    match self.lookup(n.as_str()) {
                                                        Some(Res::Proof(p, _)) => {
                                                            parts.push(p.clone());
                                                            continue;
                                                        }
                                                        _ => return Err(format!(
                                                            "boxed ctor arg of {}.{} unresolved",
                                                            d, v
                                                        )),
                                                    }
                                                }
                                                _ => {
                                                    return Err(format!(
                                                        "boxed ctor arg of {}.{} not Box.mk",
                                                        d, v
                                                    ));
                                                }
                                            }
                                        } else {
                                            arg
                                        };
                                        parts.push(self.term(inner, dt)?);
                                    }
                                }
                            }
                            return Ok(match parts.len() {
                                0 => "trivial".to_string(),
                                1 => parts.into_iter().next().unwrap(),
                                _ => format!("⟨{}⟩", parts.join(", ")),
                            });
                        }
                    }
                    // Spec fn `{ns}.{g}`?
                    let g = rest;
                    if let Some(sig) = self.ctx.sigs.get(g) {
                        if sig.ret_dt != want {
                            return Err(format!("{} returns {}Wf, wanted {}Wf", g, sig.ret_dt, want));
                        }
                        if g != self.rel && !self.ctx.done.contains(g) {
                            return Err(format!("callee lemma {}_wf unavailable", g));
                        }
                        if g == self.rel {
                            self.recursive = true;
                        }
                        if args.len() != sig.params.len() {
                            return Err(format!("{} arity mismatch", g));
                        }
                        // Value args and hyps INTERLEAVED per param —
                        // matches the lemma's binder order.
                        let mut t = format!("({}_wf", g);
                        for (a, (_, kind)) in args.iter().zip(&sig.params) {
                            t.push(' ');
                            t.push_str(&format!("({})", self.subst_pp(a)));
                            match kind {
                                ParamKind::Bounded(_) => {
                                    let bp = self.bound_proof(a);
                                    t.push(' ');
                                    t.push_str(&bp);
                                }
                                ParamKind::Dt(d) => {
                                    let p = self.term(a, d)?;
                                    t.push(' ');
                                    t.push_str(&p);
                                }
                                ParamKind::Other => {}
                            }
                        }
                        t.push(')');
                        return Ok(t);
                    }
                }
                Err(format!("unknown head `{}`", h))
            }
            ExprNode::Let { name, value, body } => {
                self.env.push((name.as_str().to_string(), Res::Inline(value)));
                let r = self.term(body, want);
                self.env.pop();
                r
            }
            ExprNode::Match { scrutinee, arms } => {
                let s = head_name(scrutinee)
                    .ok_or_else(|| "match on non-var scrutinee".to_string())?
                    .to_string();
                let (hyp, sdt) = match self.lookup(&s) {
                    Some(Res::Proof(p, Some(d))) => (p.clone(), d.clone()),
                    _ => return Err(format!("match scrutinee `{}` lacks a wf hypothesis", s)),
                };
                let spec = self
                    .ctx
                    .dts
                    .get(&sdt)
                    .ok_or_else(|| format!("no wf spec for {}", sdt))?;
                let mut out = format!("match {}, {} with", s, hyp);
                for arm in arms {
                    let Pattern::Ctor { name, args: pargs } = &arm.pattern else {
                        return Err("non-ctor match pattern".into());
                    };
                    let v = name
                        .rsplit('.')
                        .next()
                        .ok_or_else(|| "empty ctor name".to_string())?;
                    let conjs = spec
                        .variants
                        .get(v)
                        .ok_or_else(|| format!("unknown variant {} of {}", v, sdt))?;
                    let mut comp_names = Vec::new();
                    let depth = self.env.len();
                    for (idx, kind) in conjs {
                        self.fresh += 1;
                        let cn = format!("hw{}", self.fresh);
                        if let Some(Pattern::Var(b)) = pargs.get(*idx) {
                            let d = match kind {
                                ConjKind::Rec { dt, .. } => Some(dt.clone()),
                                ConjKind::Bound => None,
                            };
                            self.env.push((b.as_str().to_string(), Res::Proof(cn.clone(), d)));
                        }
                        comp_names.push(cn);
                    }
                    // Single-conjunct wf clauses are bare Props (no
                    // And) — ⟨…⟩ patterns fail on them; bind bare.
                    let wfpat = match comp_names.len() {
                        0 => "_".to_string(),
                        1 => comp_names[0].clone(),
                        _ => format!("⟨{}⟩", comp_names.join(", ")),
                    };
                    let body = self.term(&arm.body, want)?;
                    self.env.truncate(depth);
                    out.push_str(&format!(
                        "\n  | {}, {} =>\n      {}",
                        crate::lean_pp::pp_pattern(&arm.pattern),
                        wfpat,
                        body
                    ));
                }
                Ok(out)
            }
            ExprNode::If { cond, then_, else_ } => {
                let e2 = else_
                    .as_ref()
                    .ok_or_else(|| "if without else".to_string())?;
                self.fresh += 1;
                let hn = format!("hc{}", self.fresh);
                let c = self.subst_pp(cond);
                let pt = self.term(then_, want)?;
                let pe = self.term(e2, want)?;
                // Parenthesized: this term lands in ARGUMENT position
                // (a callee-lemma wf slot — seed_frame_wf's closer
                // branch, bootstrap-77); a bare `if` there is a Lean
                // syntax error ("unexpected token 'if'").
                Ok(format!(
                    "(if {} : {} then\n        (congrArg {}Wf (if_pos {})).mpr ({})\n      else\n        (congrArg {}Wf (if_neg {})).mpr ({}))",
                    hn, c, want, hn, pt, want, hn, pe
                ))
            }
            _ => Err("unsupported body node".into()),
        }
    }
}

/// All spec fns `{ns}.{g}` referenced from a def body (g must be a
/// known candidate) — the demand-closure edges.
pub fn body_spec_refs(def: &Def, ns: &str, sigs: &HashMap<String, FnWfSig>) -> Vec<String> {
    fn walk(e: &Expr, ns: &str, sigs: &HashMap<String, FnWfSig>, out: &mut Vec<String>) {
        if let ExprNode::Var(n) = &e.node {
            if let Some(rest) = n.as_str().strip_prefix(&format!("{}.", ns)) {
                if !rest.contains('.') && sigs.contains_key(rest) && !out.iter().any(|x| x == rest)
                {
                    out.push(rest.to_string());
                }
            }
        }
        e.for_each_child(|c| walk(c, ns, sigs, out));
    }
    let mut out = Vec::new();
    walk(&def.body, ns, sigs, &mut out);
    out
}

/// Synthesize the full `theorem {rel}_wf … := …` text.
pub fn synth_wf_lemma(
    ctx: &SynthCtx,
    rel: &str,
    def: &Def,
    sig: &FnWfSig,
) -> Result<String, String> {
    // Binders: reuse the def's own (names must line up with sig).
    let mut binders = Vec::new();
    let mut env: Vec<(String, Res)> = Vec::new();
    if def.binders.len() != sig.params.len() {
        return Err("binder/param count mismatch".into());
    }
    for (b, (p, kind)) in def.binders.iter().zip(&sig.params) {
        let name = b
            .name
            .as_ref()
            .ok_or_else(|| "anonymous binder".to_string())?
            .as_str();
        if name != p {
            return Err(format!("binder `{}` vs param `{}`", name, p));
        }
        binders.push(format!("({} : {})", name, crate::lean_pp::pp_expr(&b.ty)));
        match kind {
            ParamKind::Bounded(pred) => {
                binders.push(format!("(h_{}_bound : {})", p, pred));
                env.push((p.clone(), Res::Proof(format!("h_{}_bound", p), None)));
            }
            ParamKind::Dt(d) => {
                binders.push(format!("(hwf_{} : {}Wf {})", p, d, p));
                env.push((p.clone(), Res::Proof(format!("hwf_{}", p), Some(d.clone()))));
            }
            ParamKind::Other => {}
        }
    }
    let goal = format!(
        "{}Wf ({}.{} {})",
        sig.ret_dt,
        ctx.ns,
        rel,
        sig.params.iter().map(|(p, _)| p.as_str()).collect::<Vec<_>>().join(" ")
    );
    let mut s = Synth { ctx, rel, env, fresh: 0, recursive: false };

    // Top-level If (possibly under lets) in a NON-recursive fn: the
    // congrArg transport works in arms, but at top level the cond may
    // reference let names — use the probe36 tactic form instead
    // (`unfold` has equations for non-recursive defs).
    let mut peel: &Expr = &def.body;
    loop {
        match &peel.node {
            ExprNode::Let { name, value, body } => {
                s.env.push((name.as_str().to_string(), Res::Inline(value)));
                peel = body;
            }
            _ => break,
        }
    }
    let text = if let ExprNode::If { cond, then_, else_ } = &peel.node {
        if !def.termination_by.is_empty() {
            return Err("top-level if in recursive fn".into());
        }
        let e2 = else_.as_ref().ok_or_else(|| "if without else".to_string())?;
        let c = s.subst_pp(cond);
        let pt = s.term(then_, &sig.ret_dt)?;
        let pe = s.term(e2, &sig.ret_dt)?;
        if s.recursive {
            return Err("unexpected self-call under top-level if".into());
        }
        format!(
            "theorem {}_wf {} :\n    {} := by\n  unfold {}.{}\n  by_cases hc : {}\n  · rw [if_pos hc]\n    exact {}\n  · rw [if_neg hc]\n    exact {}\n",
            rel, binders.join(" "), goal, ctx.ns, rel, c, pt, pe
        )
    } else {
        let body = s.term(&def.body, &sig.ret_dt)?;
        let mut t = format!(
            "theorem {}_wf {} :\n    {} :=\n  {}\n",
            rel, binders.join(" "), goal, body
        );
        if s.recursive {
            if !def.termination_structural || def.termination_by.len() != 1 {
                return Err("recursive lemma needs structural termination".into());
            }
            t.push_str(&format!(
                "termination_by structural {}\n",
                crate::lean_pp::pp_expr(&def.termination_by[0])
            ));
        }
        t
    };
    Ok(text)
}

#[cfg(test)]
mod tests {
    //! First unit coverage for the wf-lemma synthesizer (2026-07-25
    //! audit) — the `subst_pp` textual fixpoint (incl. the
    //! self-referential-shadow termination guard) and the top-level
    //! ctor happy path of `synth_wf_lemma`.
    use super::*;
    use crate::lean_ast::{Binder, BinderKind, BinOp, Def, Expr};

    fn empty_ctx<'a>(
        dts: &'a HashMap<String, DtWfSpec>,
        sigs: &'a HashMap<String, FnWfSig>,
        accessors: &'a HashMap<String, Vec<(String, Vec<String>)>>,
        done: &'a std::collections::HashSet<String>,
    ) -> SynthCtx<'a> {
        SynthCtx { ns: "lib", dts, sigs, accessors, done }
    }

    /// A shadowing inline value (`let x := x + 1`) reintroduces its
    /// own name on every substitution round — the textual fixpoint
    /// can never converge. Before the audit fix this looped forever
    /// with unbounded string growth; now the bound caps it and the
    /// partial text fails downstream at Lean elaboration (the
    /// module's honest-failure contract: Err/census, never a hang).
    #[test]
    fn subst_pp_self_referential_shadow_terminates() {
        let dts = HashMap::new();
        let sigs = HashMap::new();
        let accessors = HashMap::new();
        let done = std::collections::HashSet::new();
        let ctx = empty_ctx(&dts, &sigs, &accessors, &done);
        let val = Expr::binop(BinOp::Add, Expr::var_synthetic("x"), Expr::lit_int("1"));
        let s = Synth {
            ctx: &ctx,
            rel: "g",
            env: vec![("x".to_string(), Res::Inline(&val))],
            fresh: 0,
            recursive: false,
        };
        // Must return (bounded), not hang.
        let out = s.subst_pp(&Expr::var_synthetic("x"));
        assert!(out.contains('1'), "at least one substitution round ran: {}", out);
    }

    /// Well-behaved chains (values referencing EARLIER lets only)
    /// still substitute to a closed form under the bound.
    #[test]
    fn subst_pp_chain_reaches_fixpoint() {
        let dts = HashMap::new();
        let sigs = HashMap::new();
        let accessors = HashMap::new();
        let done = std::collections::HashSet::new();
        let ctx = empty_ctx(&dts, &sigs, &accessors, &done);
        let a_val = Expr::lit_int("7");
        let b_val = Expr::binop(BinOp::Add, Expr::var_synthetic("a"), Expr::lit_int("2"));
        let s = Synth {
            ctx: &ctx,
            rel: "g",
            env: vec![
                ("a".to_string(), Res::Inline(&a_val)),
                ("b".to_string(), Res::Inline(&b_val)),
            ],
            fresh: 0,
            recursive: false,
        };
        let out = s.subst_pp(&Expr::var_synthetic("b"));
        assert!(out.contains('7') && out.contains('2'), "fully substituted: {}", out);
        assert!(!out.contains('a') && !out.contains('b'), "no let names remain: {}", out);
    }

    /// Happy path: `g (x : u64) = D.mk x` synthesizes a lemma whose
    /// proof is the param's bound hypothesis.
    #[test]
    fn synth_simple_ctor_lemma() {
        let mut dts = HashMap::new();
        dts.insert(
            "D".to_string(),
            DtWfSpec {
                variants: HashMap::from([("mk".to_string(), vec![(0usize, ConjKind::Bound)])]),
            },
        );
        let mut sigs = HashMap::new();
        sigs.insert(
            "g".to_string(),
            FnWfSig {
                params: vec![(
                    "x".to_string(),
                    ParamKind::Bounded("0 ≤ x ∧ x < 256".to_string()),
                )],
                ret_dt: "D".to_string(),
            },
        );
        let accessors = HashMap::new();
        let done = std::collections::HashSet::new();
        let ctx = empty_ctx(&dts, &sigs, &accessors, &done);
        let def = Def {
            attrs: vec![],
            name: "lib.g".to_string(),
            binders: vec![Binder {
                name: Some(crate::lean_name::LeanName::synthetic("x")),
                ty: Expr::var_lit("Int"),
                kind: BinderKind::Explicit,
            }],
            ret_ty: Expr::var_lit("lib.D"),
            body: Expr::app(Expr::var_synthetic("lib.D.mk"), vec![Expr::var_synthetic("x")]),
            termination_by: vec![],
            termination_structural: false,
            decreasing_by: None,
        };
        let sig = sigs["g"].clone();
        let text = synth_wf_lemma(&ctx, "g", &def, &sig).expect("simple ctor synthesizes");
        assert!(text.contains("theorem g_wf"), "{}", text);
        assert!(text.contains("(h_x_bound : 0 ≤ x ∧ x < 256)"), "{}", text);
        assert!(text.contains("DWf (lib.g x)"), "{}", text);
        assert!(text.trim_end().ends_with("h_x_bound"), "proof is the bound hyp: {}", text);
    }

    /// A ctor arg the synthesizer has no wf source for is an honest
    /// Err (never a panic).
    #[test]
    fn synth_unknown_var_is_err() {
        let mut dts = HashMap::new();
        dts.insert(
            "D".to_string(),
            DtWfSpec {
                variants: HashMap::from([("mk".to_string(), vec![(0usize, ConjKind::Bound)])]),
            },
        );
        let sigs_empty: HashMap<String, FnWfSig> = HashMap::new();
        let accessors = HashMap::new();
        let done = std::collections::HashSet::new();
        let ctx = empty_ctx(&dts, &sigs_empty, &accessors, &done);
        let mut s = Synth { ctx: &ctx, rel: "g", env: vec![], fresh: 0, recursive: false };
        let e = Expr::var_synthetic("mystery");
        let err = s.term(&e, "D").expect_err("no wf source");
        assert!(err.contains("mystery"), "{}", err);
    }
}
