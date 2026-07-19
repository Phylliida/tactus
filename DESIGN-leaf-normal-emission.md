# Leaf-normal emission & provenance-driven closers

**Date:** 2026-07-17
**Status:** DRAFT v0.1 — a plan to refine iteratively (Danielle + Claude); not
yet sliced into board cards. Nothing here is landed.
**Companions:** `DESIGN-transparent-automation.md` (the squeeze arc — this doc
inherits its end-state and transparency criteria),
`BUG-first-chain-phantom-diagnostics.md` (cause B below),
`DESIGN-link-discharge.md` (the provenance infrastructure: spine sidecars,
`HypProvenance`, `BranchTest`), `board/mainline-05` (S2c derived closer).

---

## 0. TL;DR

Two principles, applied to the default-emission closer problem:

1. **Information flows forward.** The WP calculus knows what every goal node
   is — this let is an assignment, this discriminator application came from a
   match on scrutinee `c`, this conjunct is an overflow VC. The closer should
   consume that knowledge (bootstrap-73 already records it: spine sidecars,
   `HypProvenance` on every hyp frame), not re-derive it from goal text.
2. **Normalize at emission, not in-tactic.** Most closer rungs undo emission
   artifacts: goal-position lets (hence `+zetaDelta`), `if True` residue from
   Prop discriminators, stuck accessor matches on abstract scrutinees. Emit
   goals already in leaf-normal form and the closer shrinks instead of
   growing.

End state: default emission is (a) flat arithmetic goals that S1 classifies
straight to `omega`, (b) structured goals emitted leaf-normal with a fully
determined per-goal script, (c) a generic fallback closer whose share of
emissions trends to zero — that share is the progress bar, in the same spirit
as the `tactus_auto` removal. A fully determined script has no `first`-chain,
so the phantom-diagnostic class (cause B) dissolves structurally rather than
being dodged.

---

## 1. Evidence (2026-07-17, the squeeze-regression sweep)

The S2c derived closer regressed 26 e2e tests its battery never ran (the
battery had the pool gate, gt gate, tutorial, and the *examples* suite — not
`vargo test -p rust_verify_test --test tactus`). Root causes found by
artifact-level bisection:

* **Let-opacity:** `omega` treats goal-position let-fvars as opaque atoms;
  `simp_all` does not substitute them without `+zetaDelta` (off by default).
  The WP calculus produces these lets for every assignment.
* **Stuck accessor matches:** generated discriminators/accessors/heights are
  `@[simp]` defs, invisible to `simp_all only [CORE]`; on abstract scrutinees
  they need `cases` before any equation fires.
* **Truth-residue stranding:** CORE lacked `true_or/or_true/if_true/if_false`,
  so partially-reduced disjunctions/ites strand goals `omega` cannot consume
  (`True` is not an arithmetic atom).

An interim **structural rung** (goal-text scan deriving named intros, `cases`
targets, per-goal unfold lists, `simp_all +zetaDelta only [CORE′ ∪ unfolds]
<;> omega`) recovered 11 of the 27 red tests. The remaining 16 split into
exactly two causes, and both argue for this doc's principles:

* **Cause A — re-derivation gaps.** The rung's mention-scan reads the goal
  expression; datatypes that appear only in theorem *binder types*
  (`c : test_crate.Choice`) are missed, so no unfolds/cases derive. Third
  such gap in one day; each was information the emitter had and discarded.
* **Cause B — phantom diagnostics.** With Mathlib in scope, a backtracked
  peel arm's `omega` failures persist as error diagnostics; files fail with
  sound proofs. See the BUG doc. Generic multi-arm search closers are
  fragile in ways unrelated to proof power.

---

## 2. The pieces

### N1 — Let-hoisting (goal-position lets → binders + equation hypotheses)

> **STATUS (2026-07-17, `e522317`): LANDED for default-closer emission —
> e2e suite 547/4 (+12 vs the 535/16 baseline, 0 regressions; the 4
> residue tests were red at baseline too).** Three iterations:
> 1. v1 regressed to 520/31 — three findings: Prop-typed condition-temp
>    lets hoist into propositional equations that loop simp
>    (`eq_iff_iff`) and starve omega/decide; S1's classifier ignored
>    unmentioned hypothesis binders, so a hoisted equation with an
>    out-of-fragment RHS (`val = Int.ofNat 1`) let bare omega get
>    selected into a loud failure; the structural rung's goal-text scan
>    missed everything that moved into binder types.
> 2. Bool-typed lets excluded from hoisting (fall back to the wrap —
>    N2's condition splitting is their real home); classifier chases
>    hoisted equations to a fixpoint before claiming the fragment.
> 3. The structural rung scans binder TYPES for mentions, unfolds, and
>    cases targets (the Cause-A class closed for good).
>
> Predictions confirmed: the mul_overflow phantom dissolved exactly as
> §0 argued (flat goal → S1 bare omega, no `first`-chain runs), and the
> SCC/termination/match families all closed. Residue: LetRaw-path tuple
> lets + a user-simp-prefix/derived-intro mismatch (two tests), the
> mut-ref `.deref` rendering probe, Seq-view atoms (one each). Gates
> run — ALL GREEN: e2e suite 547/4 (residue pre-existing), lean_verify
> units, gt gate (2840 verified / 0 errors, package gate live), tutorial
> chapters 9/9 (note: bare binary invocations need the lean-project
> LEAN_PATH exported or the package gate can't resolve Mathlib).
> Pool-gate re-measure still open (squeeze census tooling).

Emit `let tmp__1 := x; G[tmp__1]` as theorem-level
`(tmp__1 : Int) (h_tmp__1 : tmp__1 = x)` with goal `G[tmp__1]`.

* **Why not substitution:** chained assignment lets (`x = x * (i+1)` iterated)
  duplicate exponentially under substitution — that is why WP calculi keep
  lets. Hoisting is linear, and `omega` consumes equation hypotheses
  natively. `+zetaDelta` becomes unnecessary everywhere.
* **Expected side effect:** most of the current red goals become flat
  arithmetic after hoisting, so S1's classifier sends them to bare `omega`
  — no `first`-chain runs at all. Cause B disappears for this class.
* **Mechanics to work out:** the hoist point (`emit_split`/wrap vs the WP
  builder); freshening for shadowed let names (`tmp__` appears twice in one
  goal today); which lets are spine-position (hoistable) vs term-position
  (keep); `GoalSpine` frames for hoisted lets (a `Binder` + `Imp` pair with
  a new provenance variant?); sourcemap spans; interaction with `old(x)`
  prophecy lets and `&mut` shadows.

### N2 — Match splitting (per-arm theorems with constructor equations)

> **STATUS (2026-07-17, session 2): v1 slice LANDED — suite 547/4,
> identical to the N1 baseline (0 regressions, 0 residue movement).**
> Positive IsVariant branch hypotheses now emit as field binders + a
> constructor equation at both if-fork sites. Probe-driven shape rules
> that matter: constructor names are crate-qualified (`lean_name`);
> the equation LHS is the scrutinee LOWERED through the walk's render
> ctx; each wrapper typ decoration (Ref/MutRef/Box/Rc/Arc) adds one
> `.deref` projection on the LHS so the equation matches the arm
> body's accessor chains. Measurement: 84 constructor-equation
> theorems across the e2e artifacts; structural-rung `cases` targets
> survive in only 10 files, and the survivors are exactly the
> not-yet-covered classes — spec-level matches in ensures (goal-
> position match expressions, not branch forks), `Dt::Tuple`
> scrutinees, and the mut-ref shadow family (which also has a
> pre-existing spurious-`.deref` rendering bug, see residue).
> Tooling note: `cargo build -p lean_verify` does NOT refresh
> `target-verus/release/verus` — probe runs need `vargo build`, and a
> mid-suite binary rebuild taints the suite run.
>
> **Follow-up same session:** (1) the upgrade is gated on the DEFAULT
> closer — a fn-level `tactus_tactic` pin is positional against the
> un-upgraded shape (tgt apply_hom_symbol_exec broke until gated;
> same rule as N1's emit_split gate). (2) bootstrap merged into main
> (R-c wf-preservation synthesizer). (3) `tools/check-no-search.py`
> written to the tgt check.sh spec — package-layout scope; current
> emission is derivation-first with 0 violations. Full battery green
> on the merged state: units, suite 547/4 (squeeze-debt residue), gt
> gate + package gate + no-search claim, tutorial 9/9.

Extend the existing if-split (clamp_low already emits one theorem per branch,
via `BranchTest`) to expression-level matches and datatype-discriminator ites:
one theorem per arm, with hypothesis `h : c = Choice.Left x` (fresh binders
named from the source arm).

* Constructor equations make accessors, discriminators, and height equation
  lemmas reduce by `simp only [<named defs>]` — the emitter knows the exact
  def names at the match site (no inventory matching, no `cases` in-tactic).
  Termination VCs get the same treatment (the height measure reduces on the
  constructor form).
* **Mechanics to work out:** where to intercept (SST level, where the match
  is still a match, vs lean_ast, where exec matches are already lowered to
  `isX` chains); nested matches (arm-count product — policy: split only
  datatype-scrutinee matches, cap depth, fall back to N3's script above the
  cap); spec-level matches inside expressions; theorem-count/artifact-size
  measurement.
* **v1 slice (settled 2026-07-17, Danielle's N2 go):** the WP already
  forks value-position ifs into Branch-provenance `Hyp` frames, and
  `branch_test_of` already extracts `BranchTest { scrutinee, datatype,
  variant, positive }` from the lowered-match `IsVariant` chains — it is
  currently documentation-only. Upgrade the POSITIVE-test frames at push
  time: instead of `Hyp(scrut.is<V>)`, push field `Binder`s (fresh names
  per variant field) + `Hyp(scrut = Dt.V f0 f1 …, Branch(bt))`. N1's
  hoisting then lands the equation as a theorem binder, and accessor /
  height applications reduce by simp with the goal-mentioned generated
  defs — no `cases` in-tactic. Negative tests stay `¬ is<V>` in v1
  (multi-variant negatives need the arm-product policy first).
  Plumbing: a per-datatype field-type map alongside `DtDefInventory`
  (field binders need `typ_to_expr` of each field). Validation: the
  same gate set as N1; expect the structural rung's `cases` targets to
  go quiet for lowered-match goals — measure that share.

### N3 — Provenance-driven residual scripts

For goals that still carry structure after N1+N2, derive the script from the
recorded provenance instead of goal text:

* named intros from the goal spine (already in `GoalSpine`);
* the unfold list = the generated defs the emitter *rendered into this goal*
  (collect at render time — kills cause A by construction);
* leaf choice per obligation kind (`AssertKind`/`ObligationKind` are already
  on every theorem): `omega` for arithmetic, `simp only [eqs] <;> omega`
  for accessor-bearing goals, `rfl`/`decide` for the defeq class.

The interim structural rung's goal-walk retires here. The generic derived
closer remains only as the fallback tier for goals outside provenance
coverage, and §3.4's loud-failure semantics stay as the residue signal.

### N4 — Measurement & retirement

* Closer histogram by tier: S1 `omega` / determined script / generic
  fallback. The fallback share is the progress bar.
* Strip the structural rung once N3 covers its cases; strip the peel arm's
  conjunction branch once N1 empties it (also closes the BUG doc's interim
  question).

---

## 3. Ladder (each step gates on 0 regressions before the next)

| step | content | gates |
|---|---|---|
| N0 (optional, Danielle's call) | stopgap green: fix cause A (scan binder types too) + interim cause-B handling (BUG doc options) | e2e suite green |
| N1 | let-hoisting | e2e suite, pool gate, tutorial, gt gate; closer histogram (expect S1 share jump) |
| N2 | match splitting | same + artifact count/size delta |
| N3 | provenance scripts; retire structural rung | same + fallback-share histogram |
| N4 | docs, gate-reporter progress bar, peel-conj removal | full battery |

Validation corpus note: the e2e tactus suite is IN the battery from N0 on —
its absence is how the S2c regression shipped.

---

## N3 investigation notes (2026-07-19, pre-design probes)

> Probes in `probe-n3-scripts/` (all hand-validated on tactus-algebra
> artifacts). Findings that shape the N3 design:
>
> 1. **Hypothesis completeness holds.** User proof-body lemma calls
>    land as complete hoisted hypotheses (N1). "The body is the script
>    skeleton" is viable for proof fns: transcribe the call sequence,
>    close leaves by assumption/omega.
> 2. **Two script forms validated.** Form A (branch + axiom-call):
>    subst hoist-eqs → unfold goal spec fns → split → guard-omega /
>    exact-hyp. Form B (definitional step of recursive spec fn):
>    spine-intros → ONE-STEP `rw [head-fn]` → branch-hyp guard simp →
>    rfl. Both fully derivable from provenance + goal shape.
> 3. **Recursive spec fns can never ride simp sets** — their `eq_1`
>    loops (rewritten RHS re-matches; observed maxRecDepth). One-step
>    `rw` is the tool, and bare `rw` suffices (first-match
>    instantiation spares differently-instantiated recursive calls).
>    This also bounds the unfold-list rule: the non-recursive filter
>    stays; recursion is script territory, period.
> 4. **Interim rung win available without provenance:** a
>    `split <;> simp_all <;> omega` arm after the simp tail closes the
>    unfold-exposes-omega-guarded-if class (zpoly_generic probe).
> 5. **Corpus taxonomy** (tactus-algebra 171): pmul family ~100+
>    (forms A/B + eqv-transitivity chains), Rational nonlinear ~16
>    (ring/field power — out of script scope, needs its own story),
>    divmod 9, tail = split-arm food.

## 3a. Residue notebook (squeeze debt — RESOLVED to 1, 2026-07-18)

> **STATUS: the proper Return→Wp::Let landed (session 3) with four
> derived-closer completions — suite 550/1, gt gate green.** The
> experiment's two blockers resolved as predicted: the ctor slot gate
> became env-aware (var-like args with walker-visible binders take
> the declared slot), and the route is gated on default-closer AND
> no-proof-block-prefix (body scan). Completions the fixes forced,
> each derived-not-searched: `.injEq` (field-carrying variants) +
> `reduceCtorEq` for equation-vs-equation goals; goal-mentioned USER
> spec fn unfolds (hoisting trades rfl's definitional transparency
> for hypothesis equations — simp carries the delta now); prefix-
> aware rung (bare `intros` under user prefixes); `with_reducible
> rfl` (bare rfl on stuck matches dies with maxRecDepth, which
> `first` cannot catch — the closing omega arm never ran).
> Bonus: cross_crate_probe_5 promoted Err→Ok — the axiomatic-Seq gap
> its 2026-05-12 comment predicted would close, closed.
>
> **RESIDUE ZERO (2026-07-18 evening): suite 551/0 — vec_field CLOSED
> same-day.** vstd `vec_clone_view_eq_u8` (proved broadcast surface
> for what the axiomatized call_ensures body withholds) + derived
> equation-eliminator arms (signature-derived apply candidates, last
> in chain, both orientations). See BUG-vecfield-clone-ensures.md.
>
> Historical: **Remaining (1): `vec_field_index_clone`** — diagnosis CORRECTED
> and pinned with a machine-checked witness, see
> `BUG-vecfield-clone-ensures.md` + `probe-vecfield-clone/`. NOT an
> extensionality gap: `axiom_seq_ext_equal` is in the haves and (via
> the `=~=`→`Eq` collapse) renders as full extensionality — a 20-line
> hand proof closes the theorem given ONE extra fact,
> `strictly_cloned Int a b → a = b`. That fact is unrecoverable
> today: `strictly_cloned`'s body is `call_ensures(T::clone, …)`,
> and BuiltinSpecFun bodies are deliberately axiomatized (no Lean
> encoding). Blocking arc = call_ensures/trait-ensures encoding
> (B6-adjacent); secondary = an ext-capable closer step (N3
> provenance script or Seq-eq structural-rung extension) since
> simp_all+omega cannot do the ∀-instantiation/disjunction/ext dance
> even with the fact granted (second probe).

## 3a-old. Residue notebook (squeeze debt, 4 e2e tests)

Probed 2026-07-17 late session. Current split and the experiment that
maps them:

* **`let_bound_tuple_projection` + `typed_renderer_adversarial_probes`
  + `match_enum` family root:** the `StmX::Return` arm hand-builds
  `Done(let ret := e; ensures)` as a RAW LExpr — the ret-let is
  untyped (blocks N1 hoisting via the leaf-peel `None`-typ path) and
  a match in return position never forks (blocks N2; the
  `tmp__.deref.isGen` value-position if stays in the postcondition
  goal). On top, a user `proof {}` simp prefix rewrites the goal
  before the derived closer's positional intros run (`introN` fails
  on the transformed state).
* **Experiment (built, validated, REVERTED):** `Return(Some e)` →
  `Wp::Let(ret_name, Validated(e), ret_typ, Done(ensures))`, reusing
  walk_let's typed frames + if-fork + N2 equations. Result 540/11:
  it FIXED `mut_ref_is_variant_probe` (confirming the spurious
  `.deref` lives in the old Return-leaf rendering) but broke 8 —
  decisively, `lift_if_value_coerced`'s PER-LEAF slot coercion is
  load-bearing exactly as its comment says (`sst_ctor_box_slot_
  coercion`: `tmp__5.deref : Tree` where `Tactus.Box Tree` expected),
  and return-position forking changes goal shapes for USER closers
  (`match_enum_with_per_arm_proof`) — the fork itself needs the same
  default-closer gate as the N2 ctor upgrade.
* **The proper version (next session):** same route, plus (1)
  replicate `lift_if_value_coerced`'s slot coercion in the Wp::Let
  path (or teach `into_slot` the per-leaf behavior — needs the
  typed-renderer doc open), (2) gate return-position forking on the
  fn's default closer (statically known from the attr — thread
  `fn_closer_is_default` through WpCtx), (3) re-audit the two
  `call_result_*_in_assert` omega misfires that appeared under the
  new shape (S1 classifier interaction).
* **`vec_field_index_clone`:** untouched by the experiment — Seq-view
  atoms in omega; needs its own look (likely unfold/axiom coverage,
  not emission shape).

## 3b. Far pole (reference point, not scheduled): certificate replay

The tier ladder has a known floor. A Z3 `unsat` is a finite object —
finitely many quantifier instantiations plus ground theory steps — so
every soundly-Verus-accepted VC has a Lean proof, and *replaying a found
proof* dodges every decidability obstruction that binds provers. Three
routes, best-first for tactus's transparency ethos:

1. **Instantiation logging** — dump Z3's quantifier instantiations per
   VC and emit them as explicit `have := axiom … args` lines + a ground
   closer (omega / bv_decide / congruence). Name-is-spec readable; the
   same "information flows forward" principle as N3 — Z3's e-matching
   already found the instances, don't re-search for them. Residue:
   nonlinear (nlsat doesn't decompose this way) → nlinarith /
   Positivstellensatz certificates, a fenced gap.
2. **cvc5 + lean-smt** — same AIR queries through cvc5's well-specified
   proof production, reconstructed in Lean. Opaque-er artifacts,
   near-total coverage.
3. **Z3 proof objects** — under-specified format, coarse theory steps;
   Isabelle-era art shows it's possible and unpleasant.

Combined with the bootstrap R2 arch (the VC-generation half), any of
these completes end-to-end kernel-checked Verus: Z3 demoted from
trusted oracle to untrusted proof-finder. Recorded here so the N4
fallback-share progress bar has a defined zero — "loud failure" can
eventually mean "spend a certificate," not only "write an inline
proof." (Danielle, 2026-07-17: direction endorsed as worth thinking
toward; not scheduled.)

## 4. Relation to other arcs

* **B6 (user traits under `--lean-all-proofs`,
  `BUG-lean-all-proofs-user-traits.md`):** independent — trait class/instance
  connection, not closer/normal-form work. Verified still-reproducing on
  merged main 2026-07-17. Keep the arcs unentangled.
* **Squeeze arc:** this is its continuation — same transparency criteria
  (T1 decision procedures + fixed/derived name lists, no ambient search),
  the derivation rule generalizes from "one text" to "one function of
  recorded provenance".

---

## 5. Open questions for refinement

1. N1 hoist point: WP builder (before `GoalSpine` records) or emit_split
   (after)? Affects how spine sidecars describe hoisted lets for
   link-discharge.
2. N1 naming: freshen shadowed lets by position (`tmp___0_1`) or by source
   span?
3. N2 intercept level: SST match nodes vs lowered `isX` chains — do we
   *unlower* exec matches, or split on the discriminator chain the WP
   already built?
4. N2 arm-product policy: cap? dedup shared prefixes? measure first on the
   e2e corpus before choosing.
5. N3 leaf table: is obligation-kind granularity enough, or do we need
   per-node provenance (e.g., nonlinear VCs → keep the user's composed
   closer path)?
6. Does the mainline-07 (B4 peel-to-codegen) card get absorbed into N3, or
   does peel survive for the fallback tier only?
7. Cause B mechanism: pin the Mathlib component that breaks message-log
   rollback (BUG doc open question) — even with N1 landed, the fallback
   tier keeps a `first`-chain.
