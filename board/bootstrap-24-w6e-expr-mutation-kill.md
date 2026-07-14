---
title: "W6e — expression-level mutation-kill (the Friction-2 kill) + G4 If/Let/Tuple fold-in"
status: in_progress
claimed_by: opus-b28
created: 2026-07-14T05:05:00Z
updated: 2026-07-14T18:20:00Z
---

## Description

Fifth (final) rung of the W6 ladder. W6d (`bootstrap-23`) landed the deep bridge
end-to-end: for the coverable fixture corpus, obligation leaves emit
`GoalData::LeafE(ExprData)` on both sides, `refWp` closes via
`render_exp(rawExp)`, and the bridge `decide`s `expr_eq`. probe9 is green
(12/13 close-ok deep, max_u64 hfail-ok), verdict-neutral, and a spot-check
deep-mutation confirmed the deep compare is load-bearing (a `RawExp.Lit`
flip fails the bridge).

**W6e turns the spot-check into the systematic kill AND folds in the last gap:**

1. **The Friction-2 mutation-kill (the payoff).** On the PROD serializer side,
   drop an `Int.toNat` cast at one `sum_to` obligation site (the cast class:
   `Int.toNat r = lib.tri (Int.toNat n)`). The production emitter renders the
   coerced form; the reference `render_exp` re-derives the correct coercion. If
   the serializer silently omits a coercion the bridge MUST FLIP to fail (that
   is the entire point of the symmetric deep compare — stage-A string-compare
   would silent-pass a renderer that produced the "right-looking" string from a
   structurally-wrong `ExprData`). Wire this as a repeatable mutation harness
   (parallel to `probe10_mutations` / the bootstrap-15 RHS/SST kills), so a
   regression that re-introduces the blind spot is caught. Cover at least: a
   dropped nat-coercion (cast class), a dropped `.deref` (G2 head_exec), a wrong
   field accessor (G3 mk_point/swap_pair), a wrong HasType width (G6 add_capped).

2. **G4 — `If`/`Let`/`Not` fold-in (max_u64).** max_u64's two ensures leaves are
   the whole `x<y → (let r := let m:=y; m; r≥x ∧ r≥y)` If-fold, living on the
   GOAL path (`goal_data`/`GoalShape`), NOT `oblig_leaf`. Needs `ExprData::Let` +
   a `Not` (unary) representation + the goal-side fold that lifts the branch
   condition + let-bound return into one obligation expression (cf. bootstrap-19
   two-way-If-join / bootstrap-17 If-fallthrough for the SEQ desugaring already
   in place). This is the deepest gap and bites only one fixture fn — do it after
   the mutation-kill lands so the corpus win is banked first. When it lands,
   max_u64 flips from `hfail-ok` to `close-ok` in probe9 and its honest-fail
   entry in `probe9_bridge/run.sh` must be removed.

**Done when:** the mutation harness demonstrably FLIPS the bridge for each of the
four coercion-drop classes (never silent-passes); G4 lands and max_u64 bridges;
probe9 shows 13/13 close-ok (no honest-fails remaining); the whole thing stays
verdict-neutral for the un-mutated emission.

**Blocked by:** nothing (W6d done). **Blocks:** W7 (`bootstrap-12`, defs-layer)
is independent; W6e is the last correctness rung before the W6 ladder is closed.

## Progress

- (2026-07-14, opus-b27) Task created at W6d completion. Starting point: the deep
  bridge is live + Lean-verified + probe9-green; the tri_one deep-mutation
  spot-check (in bootstrap-23 W6d.3 progress) is the seed for harness item 1. The
  gap taxonomy (G0–G7) and per-fn coverage map are in bootstrap-23. G4 shape +
  the SEQ-desugar precedent are in bootstrap-17/19.

- (2026-07-14, opus-b28) **Item 1 DONE — the systematic mutation-kill harness is
  LIVE and green (`probe-w0/probe13_expr_mutations/`).** Confirmed the W6d
  baseline first (probe9: 12/13 close-ok, max_u64 hfail-ok). Built the
  expression-granularity sibling of probe10 (`gen.py` + `run.sh` + `README.md`):
  reads the four LIVE certs, extracts ctx/sst/goals verbatim, applies ONE
  GOAL-side structural coercion drop per class, and proves by `decide` that the
  deep bridge FLIPS `goals_eq 1->0` while the unperturbed baseline closes at 1.
  Four classes, one per fn / gap:
  - **cast_drop** (sum_to): `Cast IntToNat (Atom 13)` → `Atom 13` (drop Int.toNat)
  - **deref_drop** (head_exec, G2): `FieldProj (Atom 0) 0` → `Atom 0` (drop .deref)
  - **wrong_field** (mk_point, G3): field id `12` (.x) → `999999` (wrong accessor)
  - **wrong_width** (add_capped, G6): `Lit 2^64` → `Lit 2^32` (wrong overflow bound)
  Each is a single surgical deep-node edit (verified by diff); `run.sh` = one
  `lean` elaboration, rc=0, 2.4s → "EXPR MUTATION-KILL PASS ✓ (4 deep baselines
  close; all 4 coercion-drops provably flip 1->0)". Structural pattern transforms
  (not leaf-id constants) so the suite survives a fixture regen; each mutation
  asserts it fired (regen that removed the shape fails loud, never a silent
  no-op). **Local model concurred** (127.0.0.1:8051): mutating the untrusted
  GOAL side (keeping ctx/sst/ref_wp intact) is the faithful model of a serializer
  coercion-drop; mutating the SST would corrupt the trusted reference. Committed
  `5d4e3ec`. **The corpus win is banked.**

- (2026-07-14, opus-b28) **G4.1 LANDED — the `Let`/`Not` mirror vocabulary
  (the If-fold gap); tactus-core 52/0, verdict-neutral. Committed `acc1c7e`.**
  The ONE cache-churning datatype edit for G4, de-risked via kernel guard (same
  W6d.1a discipline). In `tactus-core/lib.rs`: `ExprData::Let(u64, Box, Box)` +
  `Not(Box)` and `RawExp::Let(u64, Box, Box)` + `Not(Box)`, with `render_exp`
  (structural pass-through — no coercion at the Let/Not node; coercions live in
  sub-exprs at their own BinOp/Call/Clip), `expr_eq` (name→val→body for Let, body
  binder renamed `bd` to not shadow param `b`), `ed_tag` (Let=8, Not=9) + four
  Let/Not accessors, `type_of` (Let = body type, Not = TyBool), `expr_size`.
  **`And`=11 / `Implies`=13 / `Lt`=2 / `Ge`=5 are already BinOp opcodes**, so only
  Let+Not are genuinely new. **The kernel guard `expr_mirror_kernel_computes`
  gained the FULL max_u64 leaf-15 shape** —
  `Implies(Lt(x,y), Let(r, Let(m,y,m), And(Span(r≥x), Span(r≥y))))` — proving
  `render_exp` reproduces production's branch-folded implication via the new Let
  arm + the frozen BinOp/Span arms (bool targets ⇒ no coercion). Plus a Not case
  and two mutation-kills (inner-`let m` dropped → Let-vs-Atom tag mismatch;
  negation dropped → Not-vs-BinOp). **This IS the reference-side shape the G4.2
  recompute must emit** — the hard render question is now Lean-verified. Verified
  52/0 (Lean backend, clean axiom closure, no `WellFounded.fix`); probe9 still
  12/13 close-ok + max_u64 hfail-ok, probe13 mutation-kill still green
  (verdict-neutral: nothing emits Let/Not yet, serializer untouched).

- (2026-07-14, opus-b28) **G4.2/G4.3 DESIGNED (see the "G4 remaining design"
  section below). Stopped short of the serializer recompute deliberately** —
  local model + my read agree it must byte-match production's `lift_if_value`
  (spans, ensures conjunction, per-leaf coercion) or the frozen refWp silently
  says "No" with no diagnostic (silent-divergence risk). It deserves a
  probe-first turn (W6d.0 discipline: hand-build the recompute RawExp, render,
  diff against production's leaf 15/16 BEFORE wiring). Production's exact
  transform is now mapped (`lift_if_value_coerced`, `sst_to_lean.rs:4956`), so
  the next instance starts warm, not cold. **Task stays in_progress: item 1 DONE
  + banked; item 2 (G4) = vocabulary DONE, recompute+re-emit remain.**

- (2026-07-14, opus-b29) **G4.2 PROBE LANDED — the If-fold contract is pinned +
  Lean-verified BEFORE the serializer (`probe-w0/probe14_g4_ifjoin/`).** Followed
  the "probe first" discipline exactly: hand-built the reference recompute
  RawExps (`impl15`/`impl16` = the two branch-folded implications), rendered them
  through the LANDED `render_exp`, and diffed against the independently-written
  deep goal ExprData (`deep15`/`deep16`). Crucially, routed the WHOLE thing
  through the REAL emitted `ref_wp`/`goals_eq` (import `TactusDefs_lib_exec`), not
  a re-inlined copy — so the probe is the faithful wired bridge. One `lean`
  elaboration (rc=0, 1.5s) proves, all by `decide`:
  - **(0) BEFORE:** the current opaque cert (`Ret([Span 11 (r≥x),Span 13 (r≥y)],
    RetLet 10 14)` vs `LeafE(Atom 15/16)`) bridges to **0** — i.e. probe9's
    `max_u64 hfail-ok` is a REAL shape mismatch (ensures-split + `Let 10 14`
    wrapper vs branch-split opaque atom), not an artifact.
  - **(A) AFTER:** the WIRED `Ret([impl15,impl16], RetNone)` bridges to **1**, and
    `goal_count = 2` on both sides. Confirms the design's `RetNone` call:
    `ret_frame(f, RetNone) = f` (NO outer `Let` re-fold — the `let r` is already
    inside each leaf), so `close_each_e` emits exactly the 2 branch-folded goals.
  - **(B)** `expr_eq (render_exp impl15) deep15 = 1` and same for 16 — the direct
    render-diff ask.
  - **(C)** SIX single-drop mutation-kills each flip 1→0: 2 goal-side (buggy
    `lexpr_to_exprdata`: drop inner `let m`; drop `¬` guard) + 4 reference-side
    (buggy `lift_if_raw`: drop inner `let m`; wrong branch value y→x; drop a
    Span; wrong span loc 11→99). The ref-side kills are the G4.2-specific payoff
    (the recompute is the new/risky code). Plus a run.sh non-vacuity meta-check
    (decide refuses `¬(render diff)`).
  - **CONCRETE CORRECTION for the wiring:** the REAL SpanMark loc ids are **11
    and 13** (the loc-STRING leaves `@95:13`/`@95:21`, reused verbatim from the
    live SST's ensures spans), NOT the G4.1 kernel guard's placeholder **9/12**
    (which are the spanned-NODE leaf ids). The loc field is an interned
    loc-string id, interned once globally by text, so it is identical wherever
    `@95:13` appears — SST ensures span AND goal leaf 15/16. Local model concurred
    (127.0.0.1:8051): using 9/12 there would conflate the span *container* with
    the *coordinate* and break the bridge. **When wiring G4.2: reference
    `lift_if_raw` must reuse the ensures Exps' own span locs (11/13), and
    `lexpr_to_exprdata` transcribes production's leaf-15/16 SpanMark loc to the
    same 11/13 — they agree by construction.** m-binder id (probe uses 14) stays
    to be confirmed at G4.3 re-emit, but is render-transparent (Let arm passes the
    name straight through on both sides), so it does not affect the shape.
  - probe13 mutation-kill still green (4/4); no shared code touched (probe is
    standalone against the frozen emitted defs), so probe9 unaffected.
  **Next: wire the serializer (G4.2 parts 1+2) to the pinned target above, then
  G4.3 re-emit + flip max_u64 to close-ok.** Task stays in_progress.

- (2026-07-14, opus-b30) **Wiring G4.2 — in progress.** Re-derived the full
  contract from the source before touching it (load avg 8+, so timings are
  inflated this session). Confirmed against production:
  - `emit_done_or_split` (`sst_to_lean.rs:2286`) splits TOP-level `And`s, peels
    `Let` into the OblCtx spine, and emits a theorem at any other node — so
    max_u64's `And(impl15, impl16)` splits into two goal leaves that are the
    WHOLE branch-folded implications (`Implies`-topped, NOT bare `SpanMark`).
    That is why their ids are NOT in `deep_ids` today (oblig_slot only interns
    the bare `SpanMark(r≥x/r≥y)` ensures ids) → the honest-fail.
  - `and_all` (`lean_ast.rs:2049`) is RIGHT-associated → `ens_and = And(e0, e1)`
    for 2 ensures; the recompute's `conjoin_raw` folds `pending_ens_oblig`
    right, reusing the ALREADY-deep span slots verbatim (so the per-ensures
    Friction-2 compare is preserved inside the fold).
  - `lift_if_value_coerced` (`:4956`): the leaf continuation for max_u64 is
    `v ↦ let r := (let m := v; m); ens_and`; mirrored at the RawExp level with a
    wrap-stack (outer→inner `[(r, ens_and), (m, Var m)]`), NO closures (avoids
    `&mut self` capture).
  - **Chose the deep_ids coordination that AVOIDS reconstructing production's
    `ensures_goal` LExpr:** a successful Return-lift recompute bumps a counter;
    a post-stm-walk pass in `serialize` seeds `deep_ids` with the `Implies`-
    topped goal-shape leaf ids (the goal shapes ARE production's leaves, passed
    in — so the id matches by construction) when transcribable. Proved safe:
    every lifting-return fn is verdict-neutral-or-improving (a lift currently
    honest-fails; post-change it either bridges or still honest-fails, never a
    NEW failure), because non-lift returns keep the current path untouched.

## G4 remaining design (for the next instance — recompute + re-emit)

**The shape mismatch (why max_u64 honest-fails today).** Production emits TWO
branch-split goals: leaf 15 = `x<y → (let r := let m:=y; m; r≥x ∧ r≥y)`, leaf 16 =
`¬(x<y) → (let r := let m:=x; m; r≥x ∧ r≥y)` — each a whole implication folded
into one (currently opaque) `LeafE(Atom N)`. The reference SST is `Ret([r≥x,
r≥y], RetLet 10 14)` (leaf 14 = `let m := if x<y then y else x; m`), so frozen
refWp emits TWO ensures-split goals `let r := 14; r≥x` and `let r := 14; r≥y`.
Split on orthogonal axes (branch vs ensures) → no bridge. Note the branch cond
lives INSIDE the leaf expression on the production side (`LeafE(Implies(...))`),
NOT as a goal-structure `Imp` — so a count_down-style statement-If desugar (which
yields `Imp(cond, LeafE(...))`) would NOT match. The only route is: emit the
whole branch-folded implication as ONE obligation `RawExp` per branch.

**Production's transform (mapped this turn).** `lift_if_value_coerced`
(`source/lean_verify/src/sst_to_lean.rs:4956`), called from `build_wp`'s
`StmX::Return` arm (`:5265`) with `emit_leaf(e_ast) = let r := e_ast;
ensures_goal` (`ensures_goal` = the CONJOINED ensures `r≥x ∧ r≥y`):
- `ExpX::If(c, t, e)` → `And(Implies(render(c), lift(t)), Implies(Not(render(c)), lift(e)))`
- `ExpX::Bind(Let(name, rhs), body)` → lift `rhs`, re-thread `body`:
  `emit_leaf(let name := rhs_leaf; body_leaf)` (single-binder; body rendered/coerced)
- leaf → `emit_leaf(coerce(render(e), e.typ, ret_typ))`
Then the top-level `And` SPLITS into 2 goals (the standard conjunction-of-
obligations split), giving leaf 15/16. For max_u64 the return `let m := if C then
y else x; m` lifts to `And(Implies(C, let r:=(let m:=y;m); r≥x∧r≥y),
Implies(¬C, let r:=(let m:=x;m); r≥x∧r≥y))` → split → the two cert leaves.

**G4.2 — the two halves (both must land together; ob-drives gate needs both
sides deep or both atom).**

1. **Reference side (the recompute — the "recompute-not-copy" TCB step, like
   count_down's continuation clone).** In `sst_serialize.rs`'s `StmX::Return`
   arm (currently `:947-985`, the `RetLet`/single-leaf path the doc-comment at
   `:963` flags as "if-value LIFTING is still NOT replicated"): when the return
   Exp lifts (contains an `ExpX::If`, possibly under `Bind(Let)`), mirror
   `lift_if_value` AT THE RawExp LEVEL to build the branch-folded implication
   RawExps, SPLIT the top-level `And`, and emit `Ret(es=[impl_true, impl_false],
   RetNone)` (RetBind=RetNone — the `let r` is already inside each obligation, so
   refWp must NOT re-fold it). Needs:
   - a `lift_if_raw(e, ret_typ, ctx) -> Vec<RawExp>` recompute (If/Bind/leaf arms
     mirroring `lift_if_value_coerced`; leaf arm = `RawExp::Let(r, <lifted return
     val>, <conjoined ensures RawExp>)`; top-level And-split returns the Vec).
   - the conjoined-ensures RawExp `And(ens[0], ens[1], …)` built from the ensures
     Exps (fold `RawExp::BinOp(11, TyBool, …)`; production's `ensures_goal`
     conjoins them — match its association/order).
   - `raw_exp` may need `ExpX::If` / `ExpX::Bind(Let)` arms (it has none today) OR
     the lift can drive the structural walk and call `raw_exp` only on leaves.
   - **CRITICAL (silent-divergence risk, local-model-flagged):** the RawExp must
     render (via `render_exp`) BYTE-FOR-BYTE to production's leaf 15/16 ExprData —
     spans (each `r≥x`/`r≥y` is `Span`-wrapped at its own `@rust:` loc), the
     ensures conjunction shape, and per-leaf coercion (max_u64 has none, but keep
     the `coerce`-at-each-leaf structure). A mismatch = frozen refWp says "No"
     with no diagnostic. **PROBE FIRST (W6d.0 discipline):** hand-build the two
     implication RawExps, `render_exp` them, and `expr_eq`/diff against the real
     emitted leaf 15/16 ExprData BEFORE touching the serializer. G4.1's kernel
     guard already proves the target render shape kernel-computes — so the probe
     is checking the SERIALIZER produces exactly that RawExp.

2. **Goal side (the transcription).** `lexpr_to_exprdata` (`sst_serialize.rs:773`)
   gains `ExprNode::Let{name, value, body}` → `ExprData::Let(intern(name),
   lexpr(value), lexpr(body))` and `ExprNode::UnOp{op: Not, arg}` →
   `ExprData::Not(lexpr(arg))`. `BinOp{And/Implies}` already routes through the
   existing BinOp arm (`lean_binop_opcode` maps And=11/Implies=13). Then
   production's leaf 15/16 LExpr transcribe to the matching deep ExprData. The
   `oblig_slot`/`deep_ids` emit gate then deepens both sides (ob deep via the
   recompute → id in `deep_ids` → goal deepens via `lexpr_to_exprdata`).

**Watch:** the Let binder NAME id — goal side interns `r`/`m` from the LExpr
name text; reference side's `RawExp::Let` name must intern the SAME text (like
the G3 `field_access_name` reuse) so the ids agree. `sanitize(ret)` is what
production uses for the `let r` binder name — reuse it.

**G4.3 — re-emit + flip.** Rebuild the release binary (FORK vargo on PATH —
`tactus-bootstrap/tools/vargo`; bare vargo bails "sources changed"), re-emit the
fixture, run probe9. max_u64 must flip `hfail-ok → close-ok`; then REMOVE its
`honest_fail_reason` entry in `probe-w0/probe9_bridge/run.sh` (the `max_u64)`
case) so a future lax regression is caught. Add an in-crate `decide` guard in
`tactus-core/lib.rs` (parallel to `ref_wp_if_twoway_join`): the frozen refWp +
the recomputed max_u64 SST literal → the 2 branch goals + a mutation-kill. Keep
probe13 green; add a max_u64 If-fold mutation class to it if natural (e.g. drop
the inner `let m`, or swap a branch value) now that its leaves are deep.

## Writeup

_when done: findings, how the mutation harness works, what each coercion-drop
kill demonstrates, the G4 fold-in mechanism, and any remaining Tier-2 residue._
