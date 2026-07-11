# Bootstrap: verifying tactus in tactus — master plan

**Date:** 2026-07-11
**Status:** proposed (consolidates + updates the R-ladder from 2026-07-09; details R2 for the first time)
**Supersedes:** the ladder framing scattered across session notes. Component docs remain
authoritative for their components: `DESIGN-axiom-closure-check.md` (R0b),
`DESIGN-lean-all-proofs.md` + followons (R0a), `DESIGN-emit-module.md` /
`DESIGN-exec-packages.md` (R1, on branch `emit-module`),
`DESIGN-transparent-automation.md` (T).
**Scope:** what "formally verify tactus in tactus" can honestly mean, the full trust
inventory it has to cover, and a staged architecture (W0–W8) for the new heart of it:
making the 25k-line Lean emitter *untrusted* via kernel-checked certificates, with the
reference semantics authored in tactus itself.

---

## TL;DR

- **The goal is not "tactus proves tactus correct" — that's Gödel-blocked and the wrong
  target anyway.** The goal is the de Bruijn criterion, pushed as far as it will go:
  every claim tactus makes should be checkable by a small independent checker (the Lean
  kernel) from a self-contained artifact, with every trust extension inventoried
  per-run. Rust becomes an untrusted *producer* of checked artifacts.
- **Proofs are already untrusted by construction** — tactic text goes to the elaborator
  and the kernel re-checks the result. The entire soundness exposure is in
  **statements**: does the emitted goal mean what the `.rs` source means? That is what
  the remaining program attacks.
- Three arcs are already designed/landed and slot in unchanged: **R0b axiom-closure**
  (live on `emit-module`: closure ⊆ core ∪ prelude, `sorryAx` fatal), **R1 package
  emission** (M0–M6.1 landed: same-crate axioms gone, circularity/statement-drift
  impossible by construction), **T transparent-automation** (search out of artifacts).
- **The new arc (R2) is a certificate architecture, not "verify the Rust":** the
  emitter additionally serializes each fn's SST as a Lean data literal; a **reference
  WP**, authored as tactus spec fns and emitted as ordinary Lean definitions, recomputes
  the obligations from that literal; the kernel checks — per obligation, per run — that
  the production emitter's goal **equals** the reference's. The 25k-line emitter drops
  out of the TCB without verifying a line of it. What remains trusted on the Rust side
  is a boring ~1k-line SST serializer.
- **The bootstrap loop closes at W5:** the reference WP's *soundness proof* (WP ⟹
  operational semantics of SST) is written as tactus proof fns, verified by tactus,
  emitted as a Lean package, and checked by the kernel with the axiom-closure gate.
  This is non-circular because the fixed point is checked by the kernel, not by tactus:
  the Lean artifact — reference definition + soundness theorem + per-run bridges +
  closure check — is self-contained and externally checkable. Tactus is merely how we
  *author* it.
- **End-state TCB:** Lean kernel; `TactusDefs` prelude (target: definitions + the
  `arch_word_bits` axiom pair); the SST serializer; the frontend
  (rustc/HIR→VIR→SST, shared with Verus); and the adequacy judgment that the Lean-side
  SST semantics is the semantics of the SST. Everything else — WP calculus, expression
  rendering, goal assembly, dep ordering, all 25k lines — is checked, not trusted.
- **Entry brick is W0, a hand-written Lean spike** (probe-first, the M0 methodology):
  one toy exec fn, its SST as a literal, a mini reference WP, both bridge forms
  (data-equality `decide` vs. defeq `rfl`), measured. No tactus code changes.

---

## 1. What "verify tactus in tactus" can honestly mean

Full self-verification is off the table twice over: Gödel (a consistent checker cannot
establish its own consistency), and scope (tactus's frontend is rustc — nobody verifies
rustc). What *is* achievable, and worth the name "bootstrap":

1. **Artifact self-containment (de Bruijn).** Each verified crate produces a Lean
   package whose composition, axioms, and statements are kernel-checked with no
   reference back to the Rust that produced it. — *R1, mostly landed.*
2. **Statement faithfulness by certificate.** The goals in that package are
   kernel-checked to equal the output of a *reference* obligation-generator over the
   program's serialized SST. — *R2, this doc's heart.*
3. **Reference soundness, proven in tactus.** The reference generator is proven sound
   against an operational semantics of SST — authored and verified in tactus, the
   proof itself landing as one more kernel-checked Lean package. — *R2/W5, the loop.*
4. **Trust inventory as a per-run fact.** Axiom closure checked per theorem; search
   automation absent from checked artifacts. — *R0b landed on branch, T designed.*

After all four, a skeptic needs to trust: the Lean kernel; a definitions-only prelude
plus one honest axiom pair; a small SST serializer; the frontend's `.rs → SST`
lowering; and the adequacy of the SST semantics as a spec. Nothing else — in
particular, not the emitter, not the tactic ladder, not Mathlib beyond the three core
axioms, and not tactus's own proof-search behavior.

What a skeptic must ALSO still trust, and always will: that the SST literal fed to the
reference is the SST of the program they read (serializer + frontend), and that the
operational semantics we wrote down is the one they mean (spec adequacy). §8 keeps
this list explicit.

---

## 2. Trust inventory today (2026-07-11)

Sizes from `source/lean_verify/src/` (25,383 lines total in the crate).

| # | Surface | Size | Risk class | Covered by |
|---|---|---|---|---|
| 1 | Lean kernel (+ elaborator, kernel re-checks it) | — | audited, external | accepted; lean4lean ruled out (upstream-report policy instead) |
| 2 | WP calculus: `sst_to_lean.rs` (`Wp`, `CtxFrame`, `walk_loop`…) | 6,304 | **silent unsoundness** — wrong goal verifies cleanly | **R2 stage A** |
| 3 | Expression/type rendering: `to_lean_sst_expr` 1,757 + `expr_shared` 1,504 + `to_lean_expr` 1,162 + `to_lean_type` 626 | 5,049 | silent unsoundness (cast/coercion class especially — cf. `DECISION-cast-rendering.md`) | **R2 stage B** |
| 4 | Statement assembly: `to_lean_fn` 1,627 + `trait_emit` 1,207 + `impl_subst` 863 + `generate` 2,077 | 5,774 | drift between axiom-statement and discharged theorem | R1 packages (drift impossible: shared defs) + R2 bridge |
| 5 | `lean_ast` 1,928 + `lean_pp` 931 | 2,859 | mis-printing a correct AST | R2 Bridge-D leaves pp trusted-but-tiny; Bridge-R eliminates it (§5.3) |
| 6 | Dep ordering / same-crate axiomatization: `dep_order` 948, islands' circularity | 948 | circular axiomatization | **R1 landed** (import DAG + Link — structurally impossible) |
| 7 | Broadcast/cross-crate/vstd axioms | — | stipulated theorems | R1 Boundary module (explicit, whitelisted) → shrinks when vstd becomes a package (R1/M-later) |
| 8 | Prelude axioms (5: `arch_word_bits`, `arch_word_bits_valid`, `Tactus.heightLt`, `Tactus.index`, `Tactus.hasResolved`) | — | genuine axioms | closure-doc §4 hygiene: definitionalize ≥3; `arch_word_bits` pair stays (honest platform assumption) |
| 9 | Axiom-environment consistency (`nonempty.rs` brackets) | 516 | inconsistent env ⇒ user tactics prove False | landed (DESIGN-nonempty-axioms, model argument in DESIGN.md); brackets carry into stmt defs unchanged |
| 10 | Tactic ladder / `tactus_auto` / Mathlib simp drift | — | *not soundness* (kernel checks); predictability/transparency | T (squeeze-and-pin) |
| 11 | Frontend: rustc, `builtin_macros`, HIR→VIR, `ast_to_sst*`, `inline_spec`, `mut_ref_normalize` | large | shared with Verus; silent lowering bugs | trusted; R4 sketch (§7) is the only known attack; differential-vs-Verus testing mitigates |
| 12 | Tactic-block text (tree-sitter-tactus, verbatim pass-through) | — | none for soundness (proofs untrusted); span mapping only | accepted |
| 13 | Serialization/caching sidecars (verus-dev cache, `.verified` markers, ladder sidecars, olean reuse) | — | stale-result reuse | content-addressed keys; Link always re-checks; sorry now fatal on islands (island-cache arc) |

Rows 2–5 are the ~19k-line core the R2 certificate removes from trust. Row 11 is the
honest floor.

---

## 3. The ladder, updated

| Rung | Content | Status 2026-07-11 |
|---|---|---|
| **R0a** | `--lean-all-proofs` — route plain proof fns to Lean; kill the Z3 hybrid | flag landed; after B1–B4 + F1–F4: **0 codegen rejections** on tgt, 723/2953 fns pass Lean-only; remaining gap = tactic strength (honest auto bucket ≈ 24k obligations); F7 taxonomy next; **Danielle driving** |
| **R0b** | axiom-closure check | **live on `emit-module`** (`#tactus_check_axioms` in TactusPrelude, M3); per-crate gate form specified; reaches main when R1 merges |
| **R1** | whole-crate packages (Defs/Stmts/Proofs/Link) | **M0–M5 complete**, island verdict cache, M6 spec'd (`DESIGN-exec-packages.md`), **M6.1+M6.1b (dual-krate render unification) landed**; tgt: cold 225s 3116/0 zero fallbacks, warm 88s; remaining: M6.0b Ref-ABI → M6.2 exec stmt/pkg → **M6.3 (exec obligations join the Link + closure gate — a soundness rung, not just speed)** → M6.4/5 default-flip; merge to main planned soon, gated on the F6 arc (chained-op associativity, separate fable driving) |
| **T** | transparent automation (T0/T1/T2, squeeze-and-pin, prelude split) | design only; the island-cache arc's ladder sidecars (`<scope>.ladder`) already record rung winners — B1's histogram is now cheap |
| **R2** | verified obligation generation (reference WP + certificates + soundness) | **this doc, §4–6** |
| **R3** | frontend | agreed not a priority; §7 records the only credible partial attack (R4) |

Arc dependencies, so nobody discovers them mid-build:

- **R2's bridge (W4) wants R1's package layers** as its home (Stmts is where a goal has
  a *name* to bridge against), so R1's merge precedes W4 — though W0–W3 are
  branch-independent. (R1 merge is near but not immediate: gated on the F6 arc plus
  remaining in-progress TODOs on the branch.)
- **R1's M6.1 render unification helps R2 directly**: one authoring/render world means
  one goal-shape surface for `refWp` to reproduce — the same simplification the T doc
  notes for `tactus_peel`→codegen. Bridging against two render worlds would have
  roughly doubled W2/W6. Corollary: don't start W2 until M6.1 semantics are merged and
  stable.
- **R1's M6.3 is the exec precondition**: exec obligations enter the Link/closure gate
  there; W4's bridge for exec fns naturally lands after it (proof-fn bridging can go
  first).
- **R2's bootstrap loop (W5) needs R0a-quality coverage** on the reference-WP crate
  itself: the loop's claim is "tactus verified this producing a *pure Lean* artifact,"
  which means the crate must verify with everything routed to Lean. Write the W2/W5
  crates lean-only-clean from day one (the tgt migration idioms exist for exactly
  this). R0a does *not* gate W1–W4.
- **T is orthogonal** but multiplies R2's value: pinned deterministic tactics + bridged
  goals + closure checks = an artifact that is simultaneously faithful, predictable,
  and inventoried — the design triad, each leg machine-checked.

---

## 4. R2 architecture: checker, not generator

### 4.1 The principle

Three ways to deal with 19k lines of trust:

1. **Verify the Rust directly in tactus.** Infeasible and wrong-shaped: production Rust
   (Arc, interning, rustc types) far outside tactus's verifiable subset; and even
   verified, the *spec* would have to state Lean-semantics faithfulness — the hard part
   smuggled into a `requires`/`ensures` nobody checks.
2. **Reimplement in Lean, make Lean authoritative.** Clean end state, but big-bang: UX
   (goal readability), cost, and a year of parallel maintenance before parity.
3. **Certificate (chosen).** Production emitter emits what it emits today, *plus* the
   fn's SST as a Lean data literal. A reference implementation recomputes the
   obligations from the literal. The kernel checks, per obligation, per run, that the
   two agree. Disagreement = verification error at that fn.

(3) is the same move the repo has made twice already — `sanity.rs` checks references
resolve; `#tactus_check_axioms` checks trust is declared; the R2 bridge checks **the
goal is the right goal**. Three per-run checks, three shrunk trust surfaces. And (3)
contains (2) as a cheap later flip: once the bridge has held over the whole corpus for
a while, making the reference authoritative is a UX decision, not a soundness one (§6,
W8).

### 4.2 The three artifacts

Per verified fn, the emitter additionally produces:

1. **The SST literal.** `def f_sst : Tactus.Sst := ⟨…⟩` — a first-order data literal in
   a `Tactus.Sst` inductive family mirroring `vir::sst` (the subset tactus supports).
   Snapshot point: **exactly the input to `build_wp`** — post `ast_to_sst`, post
   `inline_spec`, post `mut_ref_normalize` — so reference and production consume the
   same thing and the comparison is apples-to-apples. (Each upstream pass can later be
   peeled with the same pattern: serialize *its* input, reference-implement it, bridge.
   That is R4's shape, §7.)
2. **The reference obligations.** `Tactus.refWp : Sst → List GoalAst` (or `→ List Prop`
   under Bridge-R) — *not hand-written Lean*: authored as **tactus spec fns** in a new
   crate `tactus-core`, emitted as ordinary Lean definitions through the existing
   crate-defs pipeline. Pure data → data, structurally recursive — precisely the idiom
   tactus-group-theory exercises at scale every day.
3. **The bridge.** A kernel-checked equality between what the production emitter
   emitted and what the reference computes. Two candidate forms, both probed in W0:

### 4.3 Bridge-D vs. Bridge-R

**Bridge-D (data equality — recommended default).** The production pipeline already
builds its goals as `lean_ast::LExpr` *values* before pretty-printing. Serialize the
produced goal-AST too, and the bridge is first-order data equality, decided by the
kernel:

```lean
def f_sst : Tactus.Sst := ⟨…⟩                 -- serializer output
def f_goals : List Tactus.GoalAst := [⟨…⟩]     -- serialized production LExprs
example : Tactus.refWp f_sst = f_goals := by decide   -- or rfl; kernel-evaluated
```

- Fast and robust: structural evaluation of a computable function on concrete data;
  no defeq gymnastics, no elaborator cleverness. `DecidableEq` derived on the mirror
  types.
- `lean_pp` (931 lines) stays trusted: it prints the *checked* AST. It is the smallest,
  most mechanical layer, and it can get its own micro-certificate later (a Lean-side
  parser + round-trip `decide`, or W8's flip which deletes the question).
- The soundness theorem (W5) is stated through a denotation
  `Tactus.GoalAst.toProp : GoalAst → Prop` written once: *if `(refWp s).all toProp`
  then `safe s`*. The user-proved theorems are connected to `toProp` of the checked
  ASTs by the bridge plus one `rfl`-shaped lemma per goal shape (probe W0-d3).

**Bridge-R (defeq — the shortest chain, higher risk).** The reference produces `Prop`s
via a type-indexed denotation of deep expressions, and the emitted statement *is* the
reference form; a `rfl` check ties it to the pretty rendered form:

```lean
example : f_goal_rendered = Tactus.refWpProp f_sst 0 := by rfl
```

- Eliminates `lean_pp` and `lean_ast` from trust entirely.
- Risks: defeq must hold between denote-unfoldings and rendered terms (instance
  applications, `Int.toNat` materialization sites, decoration wrappers `Tactus.Box.mk`
  etc.); kernel cost scales with WP size; intrinsically-typed syntax or a
  type-checking denotation is real design work.

**Decision by probe (W0):** if Bridge-R's `rfl` holds naturally on the toy and costs
tolerably, prefer it for statements while keeping Bridge-D for the goal *list*
structure. Expected outcome: Bridge-D everywhere first (it also IS the W3 differential
gate, run in-kernel); Bridge-R adopted opportunistically per goal family; W8 flip makes
the residual pp question moot.

### 4.4 Where the bridge lives

Package mode (R1). The Stmts layer gives each obligation a named `def : Prop`; the
bridge modules sit beside Proofs — per-fn `Tgt/Bridge/<fn>.lean` importing the fn's
Stmts + the `tactus-core` package + the fn's literal module. Cached like everything
else: the M5e content-compare/superset machinery covers bridge modules with zero new
code (the same argument `DESIGN-exec-packages.md` makes for exec pkg modules), and
they join the artifact ledger with an explicit invalidation key (literal + stmts +
tactus-core olean). Link re-checks composition; the crate axiom-closure line now also
covers the bridge modules (they must close over core ∪ prelude ∪ tactus-core's own
defs — no new axioms).

Island-mode fallback exists (emit the `example` into the island file) so W3/W4 can be
exercised before the R1 merge if sequencing demands it — but the package home is the
real one.

---

## 5. R2 staging (W-ladder)

Probe-first throughout; every stage independently valuable; no stage bets on a later
one.

| Stage | Content | Validates / buys | Size |
|---|---|---|---|
| **W0** | **Hand-written Lean spike** (`probe-w0/`): mini-`Sst` (≤8 constructors: Let, If, Assert, Assume, Loop, Call, Return + an expr leaf), mini-`GoalAst`, mini-`refWp`; hand-serialize ONE real toy exec fn (the CRATEDEFS chain-crate style); write both bridges; measure kernel time; d1: does `decide`/`rfl` on data equality scale in the kernel? d2: does Bridge-R defeq survive `Int.toNat`/instance unfolding? d3: the `toProp`-connection lemma shape; d4: is emitted-spec-fn `refWp` computable in the kernel (no `Classical` in its body) or does it need `native_decide` (= `ofReduceBool` knob — avoid)? | the whole concept, zero tactus changes | small, days |
| **W1** | **Mirror types + serializer.** `Tactus.Sst`/`GoalAst` inductives (Lean, generated-or-checked against a single Rust source of truth); Rust serializer `sst_serialize.rs` from `build_wp` input + from produced `LExpr`s. Boring, 1:1, no cleverness — **this is the new trusted code; target <1k lines, reviewed as TCB.** Subset = what tactus supports today (documented deferrals excluded, serializer *fails loudly* on anything else). | the data pipeline; corpus coverage numbers (what % of tgt/suite fns serialize) | medium |
| **W2** | **Reference WP, stage A** — deep *statements*, opaque expression leaves (leaves carried as already-rendered `GoalAst` subtrees, same on both sides). Authored as tactus spec fns in `tactus-core`, lean-only-clean, emitted via crate-defs. Mirrors the `Wp` walk: Done/DoneEmpty/Let/LetRaw/ClosureBody/Scope, CtxFrame assembly, loop init/maintain/use with havoc sets, overflow/bounds obligation placement, decreases obligations. | the WP *logic* — where the structured bugs live (loop rules, context frames, prophecy plumbing) | large |
| **W3** | **Differential gate over the corpus.** Compare production goals vs. reference goals for every serializable fn in the suite + tgt (3116 fns) + tutorial. Run as a Lean batch (`decide` per fn, no Rust execution of spec fns needed). Divergence = bug on one side; drive to zero; keep as CI mode. | finds real bugs *now* (the F-taxonomy shows the class is populated); calibrates reference completeness before any proof | medium |
| **W4** | **Kernel bridge on by default** in package mode: per-fn Bridge modules, gate output gains one line — "N obligations bridge-checked against tactus-core". Failure = verification error at the fn. | rows 2 (and structurally 4) of the §2 table leave the TCB | medium |
| **W5** | **Soundness of the reference.** `Tactus.SstSem`: fuel-indexed big-step evaluator over `Sst` (total spec fn — the tactus-friendly form), `safe s` = no failing assert/overflow/bounds from any requires-satisfying state, ensures on normal exit. Theorem `refWp_sound : (refWp s).all toProp → safe s`, partial correctness first (termination/decreases obligations modeled as their own family, as Verus itself splits them). Authored as tactus proof fns; **this is a tactus-group-theory-scale formalization** — staged: **W5a** straight-line + if/else + assert/assume; **W5b** calls (the exec call rule — the thing `DESIGN-emit-module` §4.4 explicitly leaves open); **W5c** loops + havoc; **W5d** &mut / prophecy (`final`/resolve — model prophecy by ∀-quantifying the final value, the standard trick; hardest modeling, do last); **W5e** closures. | the loop closes: tactus verifies the proof that tactus's obligations are sound; artifact = one more kernel-checked package | very large, incremental |
| **W6** | **Stage B expressions**: deepen `Sst` leaves to full expression/type syntax + denotation; bridge now covers rendering (§2 row 3), incl. the cast/coercion semantics from `DECISION-cast-rendering.md` — the highest-value silent-unsoundness class in rendering. | row 3 leaves the TCB | large |
| **W7** | **Defs-layer certificate**: same pattern for spec-fn *bodies* and datatype/height emission (serialize VIR spec bodies, reference definitional translation, bridge) — a wrong-but-consistent def translation is a model-drift bug users can't see. | row 4's remaining half | medium |
| **W8** | **Authority flip (optional end state)**: emitted statements become the reference's output; production renderer demoted to dev-UX pretty-printer. Deletes the pp trust question. | strategy (2) of §4.1, reached incrementally | small, once W4–W6 have soaked |

Dependency shape: W0 → W1 → W2 → W3 → W4; W5 needs only W1/W2's shapes (can start once
stage-A `Sst` stabilizes, long-running in parallel); W6/W7 after W4's pattern is
proven; W8 last. R1-merge gates W4's package home; R0a gates nothing before W5's
*loop-closure claim*.

---

## 6. The bootstrap loop, precisely

What checks what, in the end state:

```
.rs of tactus-core (reference WP spec fns + SstSem + refWp_sound proof fns)
        │  authored in tactus, verified by the tactus binary (lean-only routing)
        ▼
Lean package: TactusCore/{Defs,Stmts,Proofs,Link} + #tactus_check_axioms
        │  checked by the Lean KERNEL — closure ⊆ core ∪ prelude
        ▼
per-crate, per-run:  user crate packages
   + f_sst literals            (trusted serializer, <1k lines)
   + Bridge modules            (kernel: refWp f_sst = f_goals)
   + Link + closure check      (kernel: composition + trust inventory)
```

Why this is not circular: the tactus *binary* appears only as an author/producer. If
it is buggy, it produces a package that **fails kernel check** — a bad `refWp_sound`
proof fails elaboration; a bad bridge fails `decide`; a smuggled axiom fails the
closure check. The one thing a buggy binary can still do is mis-serialize `f_sst` so
the kernel checks faithfulness against the wrong program — which is why the serializer
is the piece that stays in the TCB, kept small and boring, and why §8 lists it. The
fixed point is anchored outside the system being bootstrapped: any Lean kernel
implementation, including independent ones, re-checks the whole tower from the
artifacts alone.

A pleasant corollary: `tactus-core` is *itself* covered by the bridge once W4 is on —
the reference WP's own verification goals are bridge-checked against the reference WP.
That is the honest, achievable form of self-application.

---

## 7. Beyond R2 (named, not designed)

- **R4 — peel `ast_to_sst`.** Same certificate pattern one pass earlier: serialize
  VIR-AST, reference-implement the lowering (or its key invariants) in tactus, bridge.
  Only worth it after W6/W7; until then row 11 stands as trusted, mitigated by
  Verus-differential testing (same VIR pipeline, two independent backends — divergence
  on shared corpora is evidence either way).
- **vstd as a package** (R1's last row): Boundary shrinks to imports; the vstd axioms
  that remain become the explicit cross-crate trust surface, closure-checked.
- **Prelude hygiene** (closure doc §4): definitionalize `Tactus.index`,
  `Tactus.hasResolved`, audit `Tactus.heightLt` companions — target end state:
  the `arch_word_bits` pair is the *only* tactus axiom.
- **R3 — frontend:** still not a priority. rustc + `builtin_macros` + HIR→VIR remain
  trusted, as they do for Verus, CompCert-style front-gap honesty.

---

## 8. What stays trusted at the end (honesty section)

1. **The Lean kernel** (and the platform it runs on).
2. **The `arch_word_bits` axiom pair** — a genuine platform assumption.
3. **The SST serializer** (<1k lines, reviewed, fails loudly outside its subset).
4. **The frontend**: rustc, macro expansion, HIR→VIR, `ast_to_sst`,
   `inline_spec`, `mut_ref_normalize` — until/unless R4.
5. **Spec adequacy**: `Tactus.SstSem` is a *definition we wrote*; "the SST means what
   the `.rs` means" and "safe means what users think unsound means" are judgment
   calls, mitigated by the semantics being small, readable Lean and by differential
   testing against Verus/compiled behavior — never eliminable.
6. **`lean_pp`** under Bridge-D until W8 (931 mechanical lines, printing a
   kernel-checked AST).
7. **Statement *reading*ment**: the user must still read the theorem statement (or the
   `.rs` spec) to know the right thing was proven. No bootstrap fixes specs that say
   the wrong thing.
8. **Gödel's residue**: consistency of Lean + our axioms is assumed, not proven from
   inside.

Nothing else. In particular the emitter (rows 2–5), the ladder, Mathlib's tactic
ecosystem, dep ordering, caching, and tactus's entire Rust binary are *checked* at
every run, not trusted.

---

## 9. Open questions

- **O1 (W0):** Bridge-R defeq feasibility + kernel cost; Bridge-D `decide` cost at
  tgt scale (3116 fns × avg obligations — batch per fn? per module?).
- **O2 (W1):** mirror-type single-source-of-truth: generate the Lean inductives from
  the Rust types (build.rs) or hand-write + golden-test? Lean-side generation is less
  trusted code; hand-written is more auditable. Lean-side wins if the subset is stable.
- **O3 (W2):** spec-fn `refWp` computability in the kernel — `Classical.epsilon`
  anywhere in the emitted defs (via `choose`-like constructs) breaks `decide`; keep
  tactus-core's source in the choice-free fragment (enforced by a lint or by the
  emitted-defs closure check listing no `Classical.choice`… note: `Decidable` instances
  themselves are fine).
- **O4 (W2):** obligation *identity* — bridge per goal needs stable pairing between
  production goals and reference goals; `obligation_naming.rs` ids on one side, `refWp`
  output order on the other; make `refWp` emit ids too and pair by id, not position.
- **O5 (W5):** prophecy/&mut semantics — ∀-final-value model vs. two-state; pick
  whichever makes W5d provable, document as part of spec adequacy.
- **O6 (W5):** decreases/termination — model `CheckDecreaseHeight` obligations in
  `SstSem` (well-founded fuel argument) or scope W5 to partial correctness permanently
  and state that plainly in §8.
- **O7 (W4):** bridge failure UX — sourcemap the Bridge module's error to the fn like
  everything else; "goal drift against reference" as a first-class diagnostic kind.
- **O8:** does the W3 corpus run write divergences into the F-taxonomy doc
  (`DESIGN-lean-all-proofs-followons.md`) or a fresh `DESIGN-bridge-divergences.md`?
  (Bookkeeping, decide when the first one lands.)

---

## 10. Bricks summary

Near-term, in order: **W0** (spike, days) → **W1** (serializer) → **W2** (reference WP
stage A) → **W3** (differential gate — first real payoff: bug-finding) → [R1 merge] →
**W4** (kernel bridge on). Long-running in parallel from W2 onward: **W5a–e**
(soundness, the formalization). Then W6 → W7 → (soak) → W8.

Independent of all of it, still-open bricks from the sibling docs that this plan
*leans on*: T/B1 histogram (now nearly free via ladder sidecars), closure-doc §4
prelude hygiene, R1/M6.0b Ref-ABI, R0a tactic-strength (Danielle's).
