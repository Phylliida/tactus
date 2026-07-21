# DESIGN — N3: Provenance-Driven Proof Scripts

**Status:** DRAFT v0.1 (2026-07-19), for iteration with Danielle.
**Infra review + pool experiment (2026-07-20):** the closer
infrastructure audited against the transparency/predictability law.
Already of the requested kind: the script author (computed matches —
`ExactHyp` only when the emitter holds both texts), the Move
vocabulary (named bounded steps, `FirstOf` the only backtracking),
the certificate arc (quotient R1–R4, cancel, form G,
denom-injectivity), the kernel decision procedures, and the
census/span transparency layer. Noted debt (plan doc's Infra-debt
section): `structural_rung`'s silent `take(3)` cases cap, default-scope
failure legibility (no `proof {}` remedy message), broadcast-haves
consumed by simp search (watch item). Lesson (24) — the pool
experiment (`TACTUS_NONLIN_NO_POOL=1`): the congrArg pool arm is the
workhorse, not search-debt — 132 obligations across ~45 fns fail
without it. The menu-vs-tactic distinction: the deleted monomial menu
was 8 enumerated branches tried in hope (unpredictable); the pool arm
is ONE deterministic `nlinarith` call with a fixed, visible, computed
fact set — the internal search lives inside nlinarith, same genus as
omega's. It stays, with its caps (≤8 atoms, ≤12 haves, emission order)
now documented at the emission site as part of the ladder's contract;
the R-arms are the cap-free computed backstop. The env flag stays as
an attribution tool.
**Certificate-computation arc LANDED (2026-07-20):** quotient
derivation + partial hoist + R3/R4 le-multipliers + denom-injectivity.
Algebra: 107 → 112 verified, 86 → 76 errors. All 24 Rational impls
green except the recip sign-split trio (mul_recip_right,
recip_congruence ×2). Lessons: (18) the transparency/predictability
law (Danielle): COMPUTE certificates, never menu for them — a capped
menu is luck-bounded search and silently cuts winners; failures that
fall outside the statable rules go loud to `proof {}`, and that is a
feature. The quotient derivation replaces the menu: multiset-diff of
the (definition-folded) goal's and kernel's monomials — `dc * dc`
falls out of `{a.num, dc, db, dc} − {a.num, db}` structurally.
(19) `have x : T := by tac;` inside a `;`-separated single-line chain
SWALLOWS the rest of the sequence into the by-block — the by's goal
closes, then "No goals to be solved" kills the arm invisibly. Every
by-have in an emitted chain must be `(by tac)`. Latent in the cancel
branch since R2 (masked by the pool arm); the R4 chain-have tripped
it. (20) application-precedence: bare pp-atoms spliced as function
ARGS need parens — `mul_self_nonneg lib.Rational.denom c` parses as
`(mul_self_nonneg lib.Rational.denom) c` (the FUNCTION squared). Same
class as the congrArg pool's `(X + Y) * d` bug. (21) the trailing
equation wrapper (`let tmp := v; tmp`) hides the goal core from any
gate that peels `Let → body` — look through to the VALUE when the
body is the same var (N1's spine rule); it had gated the
denom-injectivity arm off. (22) partial hoist: Bool-lets become
goal-position residue lets, everything else hoists — Prop EQUATIONS
in the telescope are the simp-loop hazard N1 avoided (nested_if), but
bailing the whole hoist stranded every requires-hyp anonymous
(mul_distributes). Bail only when a hoisted binder would mention a
residue name. (23) denom-injectivity: `.den` equalities follow from
`denom` equations (`denom x = ↑(x.den + 1)`) — targeted
`simp only [denom, denom_nat] at ⊢ <names>; omega`, gated on an Eq
core with a FieldProj LHS plus a denom-mentioning binder (never bare
`at *`). R4 (two-sided congruence): each fact multiplied by the
denominators it does NOT mention; the inequality's own denominators
are the cancel factor (`mul_le_mul_iff_left₀`).
**Congruence arc LANDED (2026-07-20):** eliminator apply-guard +
trait-impl body-refs closure + form G (goal-only collapse) + the
NONLIN-scope hoist with the rewrite-ladder (commits in tactus).
Algebra: 98 → 107 verified fns, 102 → 86 failing obligations;
rust_verify_test 138/140 (2 pre-existing); lean_verify unit 407/0.
GREEN newly: axiom_add_zero_right / mul_one_right / mul_zero_right /
add_inverse_right / one_ne_zero / div_is_mul_recip / neg_congruence /
sub_is_add_neg / add_congruence_left (full fn), recip_congruence 5→4.
Lessons: (13) eliminator arms need an apply-guard — conclusion-LHS-head
must textually match the goal's LHS head (same `lean_name` contract on
both sides) or the blind `apply` misfire's "could not unify" masks the
real failure on EVERY equation goal; unknown head → keep the arm.
(14) simp's projection unfolding strands impl-body callees: a class
projection reduces to the instance's INLINE field value (`zero :=
from_int_spec 0`), so `spec_fn_body_refs` must map trait method DECLS
to their impls' spec-fn callees or the unfold closure stops one def
short. (15) form G for trait-projection-headed goals: the simp_all
rung maxRecDepth-loops when let-wrapped equation antecedents become
rewrites, but those goals need NO hyps — `intros; simp +zetaDelta only
[COLLAPSES, unfolds] at ⊢; first | omega | done`; the collapse set
needs SUB-distribution (`Int.sub_mul`/`Int.mul_sub` — `neg_spec` emits
`0 - self.num`), and the terminator is omega-only because nlinarith is
NOT import-safe (per-obligation artifacts import
`Mathlib.Tactic.Linarith` only when the fn has a `by(nonlinear_arith)`
scope — the 32/275 "unknown tactic" regression). (16)
`by(nonlinear_arith)` scopes must HOIST (emit_split matches
NONLIN_MARKER): the ladder's congrArg/rw steps reference requires-hyps
BY NAME and anonymous `→` antecedents starve the pool; surfacing it
exposed two latent pool bugs — congrArg is a TYPE CHECK (Rational-Eq
hyps must be excluded by a structural Int-side check) and the have's
multiplied type needs PARENTHESIZED sides (`(X + Y) * d` vs `X + Y *
d` is not defeq → elaboration kills the primary). (17) the
cross-multiply rw-ladder: fold definition hyps INTO the goal with `rw`
first, then congrArg-multiply the kernel hyp by a denom MONOMIAL
(squares first — `dc * dc`); nlinarith's hyp×hyp products can never
build atom-monomial certificates.
**M2 + the Rational story LANDED (2026-07-19):** script IR +
author v1 (forms A, B) + form C (M4) + the R1/R2 Rational arc
(commits `733546a`, `d5706f2`, `4f166a8`). Algebra: 205 → 139
failing obligations, 85 → 91 verified fns; 627/874 theorems (72%)
script-authored. axiom_eqv_transitive / le_transitive /
add_associative / mul_associative fully green. Additional lessons:
(9) `exact h` by defeq bridges projection-vs-raw-form (Rational's
inlined instances make requires-reestablishment free); (10) bare
`nlinarith` can't multiply hyps by atoms — the congrArg-multiplier
pool (beta-reduced types) + `mul_eq_zero` cancel is the shape for
equality chains, while single-step identities and pure inequality
chains close plain; (11) the transitive non-recursive unfold closure
(`denom` → `denom_nat`) — one-level unfolds strand the closer one
def short; (12) NEVER bare `at *` on large contexts — it
whnf-times-out and burns the theorem's heartbeat budget before the
fallback runs; unfold targeted (`at ⊢ <mentioning hyps>`).
**M2 LANDED (2026-07-19):** script IR (`script.rs`: 14-move
vocabulary + render + render-time name discipline) + author v1
(forms A, B) + primary-with-fallback emission. Census:
`script:formA`/`script:formB` classes live (algebra: 444 script
(A:413 B:31) / 393 rung:formE / 37 rung-only — form B covers 31/31
of the recursive-LHS obligations, subsuming M1's UnfoldOnce arm
entirely). Algebra: 205 → 166 failing obligations, 87 verified, zero
fn-level regressions; rust_verify_test 138/140 (2 pre-existing);
phantom audit: all 27 direct-Mathlib pkg files elaborate clean.
Lessons beyond M1's: (5) the definitional asserts live on the WRAP
path (Prop-typed lets block N1 hoisting) — the author must walk the
let spine itself (intro+subst, naming antecedents `h_scr_N`);
(6) `simp only [facts] at *` is the one-move normalization for
fact-hyp bounds (h_len rewrites h_sub's `↑(len x)` to `↑1`) — the
exact case M1 couldn't reach; (7) the structural tail's `simp_all`
must exclude the PROP-valued equation rewrites (ext_equal family) BY
LOCAL HAVE NAME or it explodes the goal's Seq equality — the emitter
computes `bc_ext_haves` from the broadcast list itself;
(8) `rfl`/`omega`/`intro` ERROR on zero goals — every script close
ends `| done` or a GuardSimp that closed the goal mid-script kills
the arm with "No goals to be solved".
**M0 LANDED (2026-07-19):** provenance completion + census harness.
`Other` split into `Requires/HoistEq/CtorEq/LoopInv/AssertFact/
AssumeFact` (+ `LoopPhase`); CallFactInfo carries the coarse ensures
shape summary (form D's input); every emitted theorem carries the
fixed-format `-- tactus-closer: <class>` comment (s1-omega /
rung-only / rung:formB / rung:formE / rung:formB+formE / user);
the N4 summary line prints unconditionally at crate end (algebra:
0 s1 / 3 formB / 806 formE / 28 formB+formE / 37 rung-only / 0 user).
Link-discharge's sidecar parser falls unknown tags through to Other
— no consumer change needed. Requires marked by binder POSITION
(`req_binder_start`), never by name-sniffing.
**M1 LANDED (2026-07-19):** form E (two-phase) + UnfoldOnce (form B)
rung arms — tactus-algebra 205 → 177 failing obligations, 85 → 87
verified fns, zero fn-level regressions; rust_verify_test 138/140
(the 2 state_machines example failures are pre-existing, Z3-path).
Details in the commit message. Key implementation lessons: (1) the
form-E phases must be ONE arm (bare `split` chain-arms never see the
ite guards hidden inside unfolded spec fns); (2) form-E phase-1 set =
goal-mentioned unfolds ONLY (adding CORE leaves residuals the split
can't close); (3) the guard simp must EXCLUDE the broadcast haves by
name or the ext axioms explode the goal's own Seq equality;
(4) fact-hyps whose bounds need arithmetic normalization
(`↑(len x)` vs `↑1`) are out of M1's provenance-free reach — that is
exactly form-B-script (M2) territory.
**Prereqs landed:** N1 let-hoisting, N2 match-splitting, B6 emission
phase, derived-closer completions through the eliminator arms.
**Validated groundwork:** `probe-n3-scripts/` (three hand-validated
probes on tactus-algebra artifacts), `probe-vecfield-clone/` (the
ext-split hand proof), plus this doc's §10 corpus data.
**Companion docs:** DESIGN-leaf-normal-emission.md (N1/N2, the N-ladder
frame), DESIGN-transparent-automation.md (the squeeze program N3
supersedes), bootstrap-73 boards (the spine/provenance substrate).

---

## 0. One-paragraph thesis

Every failure mode of the derived closers this month had the same
signature: a classifier re-deriving from rendered goal TEXT something
the emitter knew directly moments earlier — which constructor arm we
are in, which call's ensures just landed, which recursive unfold an
assert exists to perform. N3 stops reconstructing. At emission time,
for each obligation, the emitter — which holds the obligation's full
causal history (its frame list with provenance, the goal's shape, the
user's proof-body structure) — **authors the Lean proof script
directly**. The script is plain tactic text in the artifact, each step
citing named in-artifact hypotheses, with no proof-time search beyond
fail-fast leaf closers. The searched `first|`-chain becomes a fallback
whose usage is *measured and ratcheted down* (N4), not the default.

The slogan, from the frontier notes: **information flows forward.**

---

## 1. Why now — evidence that this is the right next mountain

1. **The searched closers have hit their ceiling on real math.**
   tactus-algebra post-B6: 171 obligations elaborate cleanly and fail
   in `simp_all + omega` — poly/ring lemmas whose proofs need
   *structure* (one-step unfolds, if-splits, hypothesis instantiation,
   relation chaining) that no flat simp set expresses. The gt census
   under the always-on default (running as this doc is written) will
   add the second corpus.

2. **The central bet is validated, not hoped.** Probes (all
   elaborate clean, see `probe-n3-scripts/README.md`):
   * Inlined call-ensures hypotheses are COMPLETE — the user's Verus
     proof body (a sequence of lemma calls) lands as hoisted, named
     hypotheses containing exactly the facts the proof needs.
   * Script form A (branch + axiom-call) closes `lemma_zpoly_empty`'s
     failing obligation in 5 derivable lines.
   * Script form B (one-step recursive unfold) closes
     `lemma_pmul_empty_right`'s definitional assert in 5 derivable
     lines.
   * The vec_field ext-split hand proof (20 lines) was already fully
     derivable from call-site knowledge — it prefigured this design.

3. **The substrate exists.** Bootstrap-73 built `HypProvenance` for
   the wp-cert discharge generator; N1 hoisting gives every frame a
   stable theorem-binder name in the same emission pass. N3 is largely
   a CONSUMER of machinery already paid for.

4. **A hard law was discovered that only scripts satisfy.**
   Recursive spec fns can NEVER ride a simp set: their `eq_1`
   equation's RHS contains the recursive call, which re-matches —
   observed maxRecDepth blowup, and maxRecDepth is not recoverable by
   `first|`. One-step `rw` at a specific goal position is the only
   sound tool, and "apply this rewrite once, here" is intrinsically a
   script move, not a rung.

---

## 2. Philosophy and non-goals

**Transparency = faithfulness** (the standing rule): every injected
tactic carries its own justification at the site; no ambient context;
the artifact reader can replay the reasoning. Scripts strengthen this:
where a `first|`-chain says "one of these eight things worked, guess
which," a script says "this step, because that hypothesis, from that
call."

**What N3 is NOT:**
* Not a general ATP. Leaf goals still close with the fail-fast trio
  (`assumption` / `omega` / `with_reducible rfl`) or a bounded
  `simp only` — small, transparent, fail-fast alternation at LEAVES is
  acceptable; the search being eliminated is *structural* search.
* Not user-facing syntax. Users write Verus (or inline Lean); N3
  changes only what the EMITTER writes for default-closer obligations.
* Not a replacement for S1. The omega-fragment classifier already
  emits the perfect script for arithmetic goals: `omega`. S1 is the
  degenerate happy case of N3 and stays exactly as is.
* Not speculative planning: every script form ships only with a
  corpus customer and a hand-validated probe first. (This document
  itself follows the rule — forms A/B/E below are probe-backed;
  forms C/D carry their probes as milestone entry criteria.)

---

## 3. The substrate today (inventory, verified 2026-07-19)

### 3.1 Provenance carried on frames

`lean_ast.rs`:

```rust
pub enum HypProvenance {
    CallFact(CallFactInfo),   // callee ensures woven by a body call
    Branch(Option<BranchTest>),// if/match/loop condition (variant test kept)
    HeightFact,               // recursive-call decrease fact
    Other,                    // assumes, invariants, plain asserts, …
}
pub struct CallFactInfo {
    pub callee: String,       // stable dotted Lean name
    pub is_self: bool,        // self-recursion → this hyp is the IH
    pub args: Vec<SpineArg>,  // rendered instantiation, callee param order
}
```

Built for bootstrap-73's wp-cert discharge generator; carried on
`CtxFrame::Hyp` through `walk_obligations`. Serialized per-fn in the
`.spine.json` sidecars (tactus-core), so it survives to disk already.

### 3.2 What N1/N2 already guarantee

* Every frame an obligation depends on is a NAMED theorem binder
  (`h_req{i}`, `_h_hoist_{n}`, `_h_{x}_hoist1`, ctor-equation hyps),
  hoisted flat — no goal-side lets for default-closer fns.
* N2 gives constructor equations (`s = Gen v`) instead of
  discriminator opacity, with field binders.
* The emitter runs script-authoring at the SAME point that names are
  assigned (`ObligationEmitter::emit_*`), so name↔script consistency
  is by construction, not by contract (see §7).

### 3.3 Gaps to fill (M0)

`Other` currently swallows: requires-hyps (they DO get `h_req{i}`
names but no typed provenance), loop invariants, assume/assert
pass-throughs, N1 hoist equations (binder name is recoverable but the
"this is a let-equation for binder x" fact should be typed), N2 ctor
equations. M0 splits these:

```rust
    Requires { index: usize },
    HoistEq { binder: LeanName },          // N1 let-equation
    CtorEq { scrutinee: LeanName, variant: String, fields: Vec<LeanName> }, // N2
    LoopInv { index: usize, at: LoopPhase }, // entry / maintained
    AssertFact,                            // passed user assert
    AssumeFact,                            // assume(P) — census-critical
```

plus, on `CallFactInfo`, the callee's **ensures shape summary** (see
§6 form D) — conjunct kinds recorded at weave time, since the emitter
is holding the callee's ensures right then.

---

## 4. The script IR

A script is a `Vec<Move>`; each `Move` renders to fixed Lean tactic
text. The IR is deliberately tiny; growth requires a corpus customer
(rule §2). Initial vocabulary, with validation status:

| Move | Renders to | Derivation source | Status |
|---|---|---|---|
| `Intros(spine)` | `intro a b _ h …` | goal spine (existing `spine_intro_names`) | in prod (rung) |
| `SubstHoists` | `subst h1 h2 …` (all substitutable `HoistEq` hyps) | provenance | probe A |
| `UnfoldSet(fns)` | `simp only [f, g, …]` | goal-mentioned NON-recursive spec fns (existing inventory) | in prod (rung) |
| `UnfoldOnce(f)` | `rw [f]` | goal is `Eq` whose LHS head is a RECURSIVE spec fn | probe B |
| `GuardSimp(h)` | `simp only [h, if_false, if_true]` | Branch provenance names the guard hyp | probe B |
| `SplitIf` | `split` | post-unfold goal contains `ite` | probe A |
| `LeafClose` | `first \| assumption \| omega \| with_reducible rfl` | terminal | in prod (shape-split rfl law applies) |
| `LeafSimpClose` | `simp_all only [CORE ∪ unfolds] <;> omega` | terminal, when LeafClose insufficient by shape | in prod (rung tail) |
| `ExactHyp(h)` | `exact h` | provenance: the goal syntactically equals a hyp (post-normalization) | probe A |
| `Defeq` | `rfl` | goal sides differ only by let-defeq / ctor-eta | probe B |
| `InstForall(h, t)` | `have h' := h t` | hyp with ∀-Int spine + a script-known index term | vec_field hand proof |
| `CasesDisj(h)` | `rcases h with h \| h` | hyp whose core is `∨` (e.g. `cloned` unfold) | vec_field hand proof |
| `ExtSplit(ax)` | `rw [ax]; constructor` | goal is non-Prop `Eq` at a type with a recorded ext axiom | vec_field hand proof |
| `ApplyLemma(L, orient)` | `apply L` / `apply Eq.symm; apply L` | signature-derived eliminator (subsumes today's eliminator arms) | in prod |

Rendering rules:
* Every referenced name must be a binder/have introduced earlier in
  the same theorem — checked at render time (a script citing an
  unknown name is an EMITTER bug and must panic in debug, not emit).
* No `Raw` escape hatch in the IR. If a shape needs a move we don't
  have, it falls back (§8) and the N4 census names it.
* Determinism: no iteration over hash-ordered containers may reach
  move order (mainline-20's law applies to scripts doubly).

---

## 5. The authoring algorithm

Per obligation, at `emit_with_extras` time (same place the derived
closer is chosen today), with inputs: goal `Expr`, binder list with
provenance, the fn's classification (S1 verdict), and the inventories
(DtDefInventory + recursive-fn set + ext-axiom table):

```
author(goal, frames) -> Option<Script>:
  1. if S1 says omega-fragment        -> Some([omega])          (S1 unchanged)
  2. normalize:  moves += SubstHoists (substitutable hoist-eqs only:
                 binder occurs nowhere in its own RHS, RHS well-scoped)
  3. unfold:     G := goal after mental substitution
                 if G is Eq/Iff and lhs-head ∈ recursive-fns:
                     moves += UnfoldOnce(head)
                     if a Branch hyp matches the unfolded guard:
                         moves += GuardSimp(that hyp)
                 mentioned := goal+binder mentioned non-rec spec fns
                 if mentioned nonempty: moves += UnfoldSet(mentioned)
  4. structure:  if ite reachable in G:  moves += SplitIf
                 (legs get the same close layer via <;>)
  5. close:      pick by final shape:
                 - Defeq        when Eq with let/eta-only difference
                 - ExactHyp(h)  when a hyp (post-normalization) matches
                                the goal syntactically  [cheap check at
                                emission — we HOLD both texts]
                 - ExtSplit+legs when Eq at ext-registered type and a
                                CallFact's shape summary provides the
                                pointwise+len conjuncts (form D)
                 - else LeafClose then LeafSimpClose as <;>-tail
  6. confidence: if every move's precondition was established from
                 typed provenance/goal facts -> HIGH (script emitted
                 as primary). If any step used a fallback guess ->
                 return None (derived closer path, censused).
```

Two crucial properties:
* **The author can check its own preconditions cheaply** because at
  emission time it holds all the texts — e.g. `ExactHyp` is emitted
  only when the emitter literally compared goal text to hyp text. No
  "hope simp finds it."
* **Authoring is total but Option-valued.** Returning `None` is not
  failure, it is honesty; N4 counts it.

### 5.1 What "body as script skeleton" means operationally

We do NOT walk the user's Verus body separately to build scripts. The
insight from the probes is that N1's frame list, in order, IS the
body's trace: each user call contributed a `CallFact` frame, each
branch a `Branch` frame, each let a `HoistEq`. The author consumes
frames, not the AST — one source of truth, already provenance-typed.
(The vec_field "call site knows the callee's ensures shape" story is
the same statement about `CallFactInfo`.)

---

## 6. Script forms, per corpus family

**Form A — branch + woven fact** (probe `zpoly_probe.lean`):
`SubstHoists; UnfoldSet; SplitIf <;> [guard-omega | ExactHyp]`.
Customer: assert-forall-by obligations whose by-block called axioms;
the tail of tactus-algebra; scattered gt shapes.

**Form B — definitional step of a recursive fn** (probe
`pmul_conv.lean`): `Intros; UnfoldOnce; GuardSimp; Defeq/LeafClose`.
Customer: the definitional asserts throughout the pmul family (the
single biggest block of the 171). LAW: this is the ONLY sanctioned
contact between recursive spec fns and tactics — never simp sets.

**Form C — equivalence chaining** (NOT yet probe-backed — M4 entry
criterion): goals `eqv X Z` where the user's calls produced `eqv`
facts and the trait's congruence/transitivity axioms are class Prop
fields. Expected script: `ExactHyp` in most cases (the user called
trans explicitly, so the final fact IS a hyp — validate on corpus);
where not, `InstForall` on axiom fields + `ExactHyp`. Open question
§11.2.

**Form D — callee-ensures elimination** (hand proof
`probe-vecfield-clone/repro_hand_proof.lean`): when a `CallFact`'s
shape summary records `len-eq ∧ ∀-pointwise ∧ trigger ∧ …`, and the
goal is Eq at an ext-registered type: `ExtSplit; [len-leg via
UnfoldSet+LeafClose | pointwise-leg via Intros; InstForall;
UnfoldSet(cloned); CasesDisj <;> close]`. Customer: vec_field-class
view-equality postconditions; subsumes and retires the vstd
`vec_clone_view_eq_u8` special-case ONLY when the general
`call_ensures` encoding lands (separate arc; not blocked on it —
form D works off the shape summary regardless).

**Form E — the interim, provenance-free harvest** (probe
`zpoly_generic.lean`): a `split <;> simp_all <;> omega` arm appended
to today's structural rung. Not a script at all — ships in M1 as a
plain rung extension because it is validated and cheap, and its
harvest shrinks the corpus the script forms must explain.

---

## 7. The naming contract

Scripts cite binder names (`h_req0`, `_h_hoist_3`, `_h_x_hoist1`).
These are positional and WILL churn across emitter changes. This is
sound because:

* Script and names are produced in the same emission pass from the
  same frame list — they cannot disagree within an artifact.
* Cross-run churn affects only cache/diff hygiene, identical to
  today's theorem-text churn. (Cache key is content-hashed anyway.)

M0 nicety (optional, not load-bearing): provenance-flavored names
(`h_call_lemma_zpoly_empty_1`, `h_ih_2`, `h_if_neg_1`) — better
artifact readability and N4 census greppability, at the cost of one
round of pinned-test churn. Decision: Danielle's call; the author
works either way.

---

## 8. Fallback architecture and N4 (the ratchet)

Rollout stance: **script primary, rung fallback, everything counted.**

```
by
  <haves block (unchanged)>
  first
  | (<script>)          -- when author returned Some + HIGH
  | (<derived closer>)  -- today's chain, verbatim
```

with an artifact-visible census marker (a fixed-format comment per
theorem: `-- tactus-closer: script:formB` / `script-fallback:rung` /
`rung-only`) so N4 metrics are computable from artifacts alone by
grep — same census philosophy as the no-search gate.

**Known hazard (must be handled, not hoped away):** the
first-chain phantom-diagnostics bug (BUG-first-chain-phantom-
diagnostics.md) — backtracked arm errors persisting in
Mathlib-importing files. Scripts make this WORSE if the script arm
fails messily. Mitigations, in order of preference:
1. HIGH-confidence scripts skip the `first|` entirely (no fallback,
   no phantom surface) once their form's corpus pass-rate clears a
   bar (M5 ratchet);
2. else the script arm's leaf moves stay fail-fast (no simp_all
   inside script arms that precede a fallback).

**N4 report**: per crate run, one summary line
`closers: N script (A:x B:y D:z) / M rung-fallback / K rung-only /
E failed` + the suite/gates asserting "script share never decreases"
(a ratchet test, exactly like the no-search claim).

---

## 9. Relationship to existing machinery (what changes, what dies)

| Machinery | Fate under N3 |
|---|---|
| S1 omega classifier | unchanged; becomes "form 0" |
| Structural rung | becomes fallback; gains form E split-arm in M1 |
| Eliminator arms | subsumed by `ApplyLemma` move + form D; retire after M3 |
| trait-method/spec-fn unfold inventories | reused as-is by `UnfoldSet` |
| Non-recursive unfold filter | KEPT permanently (the loop law) — recursion is `UnfoldOnce` script territory |
| decreasing_by dispatch | untouched (termination is its own channel); Ladder kind stays |
| Broadcast haves | unchanged (scripts may cite `_tactus_bc_*` via `ApplyLemma`/`InstForall`) |
| wp-cert discharge generator (bootstrap) | sibling consumer of the same provenance; watch for shared-enum needs, don't couple release trains |

---

## 10. Corpus data (2026-07-19)

tactus-algebra, post-B6, all elaboration-clean; 171 failing
obligations by family:

| Family | ~Count | Form |
|---|---|---|
| pmul definitional asserts + branches | ~100+ | B, A |
| pmul/padd eqv-chain postconditions | inside above | C (investigate) |
| Rational recip/mul nonlinear | ~16 | OUT OF SCOPE for scripts — genuine `ring`/`field_simp`-class power; own story, censused separately |
| divmod | 9 | B + C likely |
| misc tail | rest | E harvest |

gt census under the always-on default: RUNNING (first cold all-proofs
run); its taxonomy slots in here when it lands and becomes the second
acceptance corpus. Expectation from the 16%-era taxonomy: heavy
translator-reject tail (assert-forall-by, choose, fuel/reveal shapes)
that N3 does NOT address — those are WP-translator gaps, censused as
`rung-only`/`failed`, and become their own backlog.

---

## 11. Open questions (each with its probe)

1. **Substitutability of hoist-eqs**: `SubstHoists` needs binder-not-
   in-RHS and no shadowing. Probe: count non-substitutable hoists
   across algebra artifacts (script author must fall back to
   `simp only [h]` rewriting for those — cheap alternative move).
2. **Form C reality check**: sample 5 eqv-goal failures; determine
   whether `ExactHyp` post-normalization suffices (bet: mostly yes)
   or axiom-field instantiation is needed. Blocks M4 only.
3. **`split` vs `by_cases` stability**: `split` on nested ites
   produces goal orders we must treat as canonical; pin with a probe
   + a unit test on move rendering.
4. **Leaf `simp_all` budget**: does any validated form NEED simp_all
   in a leg (vs `simp only` + omega)? Prefer bounded `simp only`
   everywhere inside script arms (phantom hazard, §8).
5. **Loop obligations**: invariants are `Other` today; loop-heavy gt
   exec fns are the customer. M0 types them; which script form do
   maintenance obligations take? (Likely A-shaped with LoopInv hyps.)
   Needs its own probe before any loop-specific move ships.
6. **Name flavor** (§7): positional vs provenance-flavored — decide
   at M0 with Danielle.

---

## 12. Milestones

* **M0 — provenance completion + census harness.** Split `Other`
  (§3.3); record CallFact ensures-shape summaries; emit the
  closer-census comment; N4 summary line + ratchet test. No behavior
  change to proofs. Gate: suite 551/0 unchanged, census visible.
* **M1 — form E harvest (rung split-arm) + `UnfoldOnce` rung-arm
  experiment.** Pure derived-closer extensions, no script IR yet;
  measures how much falls before scripts do. Gate: suite green +
  algebra number moves + census shows the delta.
* **M2 — script IR + author v1 (forms A, B).** Primary-with-fallback
  emission for proof-fn assert/postcondition obligations. Gate:
  algebra ≥ baseline+form-A/B families; zero suite regressions;
  phantom-audit on Mathlib-importing artifacts.
* **M3 — form D + ApplyLemma migration.** Retire eliminator arms.
  Gate: vec_field-class closes via script (censused), suite green.
* **M4 — form C** (entry: Q11.2 probe). Gate: pmul eqv family delta.
* **M5 — ratchet.** Per-form: when a form's fallback-rate over the
  acceptance corpora is 0 for N consecutive full runs, drop the
  fallback arm for that form (phantom surface shrinks; artifacts get
  cleaner). Never ratchet a form with nonzero fallback.

Each milestone lands with its probes committed under
`probe-n3-scripts/` — the probe IS the spec of the move's rendering.

---

## 13. Risks

| Risk | Mitigation |
|---|---|
| Phantom diagnostics via failing script arms | §8: fail-fast leaves in script arms; ratchet to no-fallback |
| maxRecDepth (uncatchable) re-entering via script moves | LAW: no bare `rfl` except `Defeq` (shape-proven); no recursive fns in any simp set; `UnfoldOnce` only |
| Script size blowup on huge obligations | moves are O(frames); cap + census `rung-only` above threshold |
| Emission nondeterminism reaching scripts | mainline-20 law; unit test: same SST → byte-identical script |
| Author bugs producing wrong-name citations | debug-panic at render (names checked against binder list) |
| Memory (the 25GB emission peak) | scripts add per-obligation text only; the peak is routing-volume, tracked separately (Nonempty cache landed; profile after gt census) |
| Lean version sensitivity (`split`, `rw` behavior) | probes are pinned per toolchain bump, same as closer text today |

---

## 14. Glossary

* **Frame / CtxFrame**: one hypothesis-or-binder an obligation
  depends on, pushed during the Wp walk; N1 hoists frames to theorem
  binders.
* **Provenance**: the typed record on a frame of WHY it exists
  (`HypProvenance`).
* **Spine**: bootstrap-73's serialized per-fn record of frames +
  instantiations (`.spine.json`).
* **Move / Script**: §4. **Author**: §5.
* **Rung / derived closer**: today's searched `first|` machinery
  (DESIGN-transparent-automation.md).
* **Ratchet**: monotone script-share enforcement, §8/M5.
