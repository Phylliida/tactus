# Transparent automation — shrinking the prelude and the closer

**Date:** 2026-07-09
**Status:** proposed (design only; the instrumentation brick B1 is the entry point)
**Scope:** reduce the heuristic-search surface in *checked artifacts* to near zero,
split the prelude into trusted vocabulary vs. dev-time search, and make every
replayed proof explicit and deterministic — without paying the usability cost of
hand-writing arithmetic leaf proofs.

Companion to `DESIGN-axiom-closure-check.md`: that doc inventories what a proof
*rests on* (axioms); this one inventories what a proof *does* (tactics). Together
the artifact both declares its trust base and names its reasoning.

---

## TL;DR

- **Reframe: transparency is a property of the artifact, not the workflow.** The
  ladder (`tactus_first` / `tactus_auto`) stays as a development-time *search* tool;
  the checked, replayed artifact contains only explicit, deterministic tactics.
- Three-tier classification of what's in the prelude + ladder today:
  - **T0 vocabulary** (defs: Int rendering, `usize_hi`, decoration types, height
    machinery, `Decidable` promotion, conditional `HXor` instances) — keep; a small
    definitional prelude is read-once and auditable. Axiom hygiene is tracked in
    DESIGN-axiom-closure-check §4.
  - **T1 specified-domain decision procedures** (`rfl`, `decide`, `omega`,
    `bv_decide`, and `simp only [explicit lemma list]`) — allowed in artifacts.
    Criterion: success is a function of the goal's theory fragment — complete for a
    documented domain, no mutable lemma database, no drift.
  - **T2 heuristic search** (`simp_all` with the default set, `tactus_case_split`,
    the `tactus_first` ladder itself) — dev-time only; successes are **squeezed**
    to `simp only [...]` and **pinned**; never appears in a replayed artifact.
- **Squeeze-and-pin:** discovery runs the ladder as today and captures the winning
  rung per obligation; `simp_all` winners are minimized to named-lemma `simp only`
  calls; pins persist in a sidecar keyed like the verus-dev cache and are replayed
  deterministically. Pin changes are surfaced ("N pins updated"), so proof drift is
  visible in review instead of silent.
- **`tactus_peel` gets deleted into codegen** — the emitter knows each goal's exact
  shape and can emit explicit structure.
- **Prelude splits into `TactusDefs` (imported by artifacts) and `TactusSearch`
  (dev-only)** — the prelude that participates in the trust/audit story becomes
  pure definitions.
- **Brick 1 is measurement, not policy:** instrument the ladder, get the
  rung-winner histogram across the gate crates, and let the data set how aggressive
  removal can be.

---

## 1. Motivation

None of this is soundness — the kernel checks every proof term regardless. It is
the other two legs of the design triad (transparency = faithfulness +
predictability, DESIGN.md principle #1):

1. **Predictability.** `simp_all`'s behavior is a function of the ambient simp set,
   which changes under every Mathlib/toolchain bump. Today a bump can silently
   change *what verifies* — the moral equivalent of an rlimit cliff, except
   data-dependent and unannounced. A pinned `simp only [Bool.xor_comm]` breaks
   *loudly* on a renamed or removed lemma, at the exact obligation affected.
2. **Transparency.** `tactus_auto` succeeding tells the reader nothing about *why*
   the goal is true. `omega` succeeding says "linear integer arithmetic."
   `simp only [X, Y] <;> omega` names the facts. The existing design already
   prefers this direction — the `tactus_auto` comment block mandates "NO extra simp
   lemmas; the preferred response is for the user to write the proof explicitly" —
   this doc extends that principle from *not growing* the closer to *shrinking its
   artifact footprint to zero*.
3. **Encoding pressure.** The closer's power currently shapes the encoding: the
   prelude deliberately omits `usize`/`isize` refinement bounds because
   "tactus_auto's current toolbox can't reason about symbolic exponents"
   (TactusPrelude.lean, `arch_word_bits` comment). That is automation weakness
   propagating into *specification weakness*. Once explicit proofs are a normal,
   supported artifact form, encoding decisions stop being hostage to what the
   ladder can close.

---

## 2. Tier classification

| Component | Tier | Disposition |
|---|---|---|
| Vocabulary defs (`usize_hi`, decoration types, height fns, `Decidable` promotion, conditional bitwise instances) | T0 | keep in `TactusDefs`; definitionalize remaining axioms per DESIGN-axiom-closure-check §4 |
| `rfl`, `decide`, `omega` | T1 | allowed in artifacts, guilt-free |
| `bv_decide` | T1 | allowed, but inventoried via the `ofReduceBool` closure knob (see closure doc §3) |
| `simp only [named lemmas]` (+ `<;> omega` tails) | T1 | allowed — deterministic given named inputs; drift is loud |
| `simp_all` (default set) | T2 | discovery only; squeezed on success |
| `tactus_case_split (simp_all …)` | T2 | discovery only; pins record the case split + per-case T1 closer |
| `tactus_first` ladder / `tactus_auto` | T2 | discovery only; never emitted in replay artifacts |
| `tactus_peel`, structural `refine`/`intro` wrapping | T3 | eliminate — codegen emits explicit structure (§4) |

The T1 criterion, stated once: **automation is artifact-acceptable iff its success
is determined by the goal's membership in a specified theory fragment** — complete
for that fragment, independent of any mutable database. `decide`'s caveat is kernel
reduction cost (fine — it either elaborates in budget or it doesn't, still
deterministic); `bv_decide`'s caveat is compiled execution, already a tracked knob.

---

## 3. Squeeze-and-pin

### 3.1 Modes

- **Discover** (dev default): closer behavior exactly as today, plus capture. When
  the ladder closes a goal, record the winning rung. For `simp_all` winners, re-run
  in squeeze mode to obtain the used-lemma list (`simp_all?` / `Simp.Stats`
  used-theorem tracking — confirm exact API on v4.25.0) and minimize to
  `simp only [...]` (+ `omega` tail when the winning rung was the composed one).
  Write the resulting explicit tactic as the obligation's **pin**.
- **Replay** (gate/CI): the emitter substitutes each obligation's pinned tactic for
  the closer. **No search runs at all.** A pin miss (new fn, changed goal) is a
  hard error in strict replay; in dev replay it falls back to discover-for-that-
  goal and reports `N pins updated` — proof drift becomes a reviewable diff.

### 3.2 The pin store

- Sidecar per crate (e.g. `tactus-pins/<crate>/<module>__<fn>.json`), mapping
  **obligation id → tactic text**. `obligation_naming.rs` already exists to give
  obligations stable names — that's the key. Invalidation keys off the same SST
  hashing the verus-dev cache uses: pin validity = cache-key validity, one
  mechanism, already built.
- Pins are the per-obligation generalization of the existing per-fn/per-assert
  `#[verifier::tactus_tactic("...")]` override — same substitution point in
  `sst_to_lean` (the closer seeding at the fn level, currently defaulting to
  `Tactic::Named("tactus_auto")`), finer granularity.
- **Source anchoring, honestly:** user-visible `assert(P) by { … }` sites can
  optionally have their pins suggested *into the source* ("this assert needed
  `simp only [Bool.xor_comm]` — consider writing it explicitly"), matching the
  existing UX principle. But most obligations are WP-internal (loop init/maintain,
  overflow side conditions) with **no source expression to attach to** — the
  sidecar is the general mechanism, source suggestions are the opt-in nicety for
  the sites that have anchors.
- Pins are committed to the repo. They are part of the proof, and reviewing a pin
  diff is reviewing a proof change.

### 3.3 What replay buys

- **Determinism:** a crate that verified yesterday verifies today, byte-identical
  tactics, or fails at a named obligation with a named missing lemma.
- **Speed:** no ladder search on the hot path — each rung that used to fail before
  the winner is elaboration work eliminated. (The ladder tries up to ~7 rungs;
  goals that close on rung 6 currently pay for 5 failures every run, forever.)
- **Auditability:** the emitted `.lean` artifact reads as a proof, not as an
  invocation of a search procedure.

---

## 4. `tactus_peel` → codegen

The prelude's own comment assigns structural peeling to codegen ("the emitter
knows exactly what goal shape each theorem has") — `tactus_peel` exists only
because loop goals stack `init ∧ maintain ∧ use` with data-dependent nesting. But
the emitter *built* that conjunction; it knows the exact tree. Emit the explicit
`refine ⟨?_, ?_⟩` / `intro` sequence per subgoal instead of a recursive macro.

Wins beyond transparency: each subgoal gets its own tactic position, so sourcemap
spans point at the *specific* conjunct that failed rather than at a macro
invocation — better error UX for free. The macro is then deleted from the prelude.

---

## 5. Prelude split

- **`TactusDefs.lean`** — vocabulary only: defs, instances, decoration types,
  `arch_word_bits` + validity. No tactics. This is the file that participates in
  the trust/audit story; target state per the closure doc is "definitions plus the
  arch-word axiom pair."
- **`TactusSearch.lean`** — imports `TactusDefs`; the ladder
  (`tactus_first`/`tactus_auto`/`tactus_case_split`/`tactus_bit_vector`/
  `tactus_peel` until §4 lands). Imported only in discover mode.
- Replay artifacts import `TactusDefs` alone; their pinned tactics reference only
  core/Mathlib T1 procedures. The gate can then assert a second one-line claim
  next to the axiom-closure one: **"no artifact imports the search module."**
- `prelude.rs`'s content-hashed olean cache extends naturally to two oleans.

---

## 6. Brick 1: instrument before deciding

Before any removal, get the data: extend `tactus_first` (or wrap it in an elab
that logs) to record the winning rung per obligation, and sweep the gate crates
(tactus-group-theory, tactus-computability-theory, the tutorial).

Output: a histogram — what fraction of goals close on `rfl`/`decide`/`omega` vs.
the `simp_all` rungs vs. `tactus_case_split`, and how many fns already carry
explicit user tactic blocks. Decision table:

- **`simp_all` share small (≲10%):** consider dropping the T2 rungs from the
  *default* ladder entirely — the affected sites migrate to explicit proofs via
  one-time squeeze suggestions, and the pin machinery shrinks to "suggestions
  only." Cheapest possible end state.
- **`simp_all` share large:** full squeeze-and-pin (§3) is the path; outright
  removal would be a usability cliff.

Either way B1's cost is small and its output also serves the `--lean-all-proofs`
arc: as DeadEnd lowering moves ~1300 more proof fns onto the Lean path, the rung
distribution should be watched, not guessed.

---

## 7. What we deliberately do NOT remove

- **The vocabulary prelude.** Inlining defs into every emitted file would trade
  one small audited file for massive duplication — strictly worse transparency.
- **`omega`/`decide`/`rfl`.** Removing specified-domain decision procedures means
  hand-writing linear-arithmetic proofs: pure cost, no transparency gain under the
  T1 criterion.
- **The discover-mode ladder.** It is the UX that makes tactus writable. It just
  stops being part of what's checked.
- **`Decidable` promotion, conditional `HXor` instances, decoration types.** These
  are encoding needs, not automation; they live in `TactusDefs`.

---

## 8. Relation to other arcs

- **Axiom-closure check:** complementary inventories (trust base vs. reasoning
  content). Both are one-line claims at the gate.
- **`--lean-all-proofs` / DeadEnd lowering:** more goals on the Lean path = more
  ladder traffic; land B1 alongside so the histogram tracks coverage growth.
- **Package mode (whole-crate emission):** pins key on obligation ids, not file
  layout — unchanged by the island→package move. Strict replay is the gate mode.
- **Verified-WP (tactus-core):** §4's explicit structural emission reduces the
  degrees of freedom in goal shapes, which directly simplifies what the Lean-side
  reference WP must reproduce.

---

## 9. Bricks

| Brick | Content | Size | Depends on |
|---|---|---|---|
| B1 | Ladder instrumentation + rung-winner histogram over gate crates | small | — |
| B2 | Squeeze machinery: used-lemma extraction → `simp only [...]` minimization | medium | B1 (API spike) |
| B3 | Pin store (sidecar, obligation-id keyed, cache-coupled invalidation) + replay mode in the emitter | medium | B2 |
| B4 | `tactus_peel` → codegen explicit structure; delete macro | medium | — |
| B5 | Prelude split `TactusDefs`/`TactusSearch`; two-olean build | small | — |
| B6 | Gate policy: strict replay + "no search import" assertion in crate check.sh gates | small | B3, B5 |

B1, B4, B5 are mutually independent. B1's histogram may shrink B2/B3 to
"suggestions only" (§6 decision table) — measure first.

---

## Brick 1 result (2026-07-11): rung-winner histogram

Measured per-THEOREM via minimal-prefix chains (`rfl` → `+decide` → `+omega` →
`+tactus_peel∘T1` → full `tactus_auto`) over a stratified sample of currently-passing
fns' emitted artifacts (post Option-B naming; 75 theorems / 38 fns; harness =
`tools/rung-attrib/fast_attrib.py` — combined file per fn with variant-suffixed theorem
copies, preamble elaborated once, bare `lean`, 8-way parallel; ~2 min a run):

| minimal closer | share (full pool: 215 thms / 114 fns) | (first sample: 75 thms) |
|---|---:|---:|
| `rfl` | 6.0% | 4.0% |
| `omega` | 18.1% | 18.7% |
| `tactus_peel` ∘ {rfl,decide,omega} | 8.4% | 12.0% |
| **T2 (`simp_all`/`tactus_case_split`)** | **67.4%** | 64.0% |

Full-pool re-run after harness adoption (`tools/rung-attrib/`, composed
`first | tactus_auto | fallback` sites excluded by design — they carry explicit
user proofs already): zero unexplained failures, stable shares.

**Decision-table read (§6): the `simp_all` share is LARGE** — outright removal of T2
from the default ladder would be a usability cliff. The indicated path is
**squeeze-and-pin (§3)**: the ladder stays dev-time-only, `simp_all` winners minimize to
named-lemma `simp only [...]` pins, artifacts replay deterministically. ~35% of passing
goals already need nothing beyond T1(+peel), and the F7 taxonomy suggests peel∘omega
additionally closes a large slice of the currently-FAILING bucket (46% of 24k goals are
quantified/let-wrapped shapes validated against peel∘omega in scratch) — so the
deterministic floor is substantially higher than today's default suggests. Danielle's
standing direction: `tactus_auto` disappears from artifacts; with `tactus_tactic("...")`
also being removed, the end state is two surfaces — emitter-derived tactics + inline
proofs.
