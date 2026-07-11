# Bootstrap: verifying tactus in tactus — master plan

**Date:** 2026-07-11 (rev 2, same day: W0 pre-probes RUN — §11; bridge roles sharpened — §4.3)
**Status:** proposed; five load-bearing mechanics empirically validated (`probe-w0/`), one
real constraint found (WF-compiled spec fns don't kernel-reduce) with a confirmed mitigation
**Branch:** all bootstrap work lives on `bootstrap` (worktree `tactus-bootstrap/`), keeping
main clear for the in-flight F6/B5 arcs
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

**Division of labor (sharpened after the §11 pre-probes; the two bridges are
COMPLEMENTARY, not alternatives):**

- **Bridge-D is the drift gate.** It is cheap, robust, and catches emitter bugs — but
  it cannot carry the soundness chain alone, because connecting a *data* GoalAst to
  the *Prop* the user actually proved requires a denotation, and a denotation of full
  untyped `LExpr` syntax would be an elaborator-in-Lean (infeasible).
- **The denotation is therefore load-bearing on the soundness path**, and it must be
  over `refWp`'s own *typed* goal language, not over LExpr: `refWp : Sst → List TGoal`,
  `TGoal.toProp : SymEnv → TGoal → Prop` where `SymEnv` carries the crate's actual
  types and spec fns (a generated per-crate environment literal grounding fn symbols
  in the emitted Defs). §11 P4/P5 validate that this denotation `rfl`-bridges to the
  production-rendered Prop — through binders, environment lookups, opaque user-type
  quantifiers, and named user spec fns.
- **Authorship split, honestly:** `refWp` and `SstSem` (data → data) are tactus spec
  fns. `toProp`/`SymEnv`/`interpTyp` return `Prop`/`Type` — outside tactus's spec
  language — so the denotation layer is **hand-written Lean in tactus-core**: small,
  audited-once, and *not trusted* (it is the statement of soundness; spec-adequacy
  covers it, §8.5). The W5 soundness proof relates `refWp` to `SstSem` at the data/Val
  level in tactus; a thin hand-Lean **adequacy spine** (structural induction over
  `TGoal` relating the typed denotation to the Val-level one, with generated per-datatype
  embedding lemmas) connects it to the user-facing Props. Staging: W5 v1 may state
  soundness at the Val level only — already the full drift-detector — with the adequacy
  spine as W5f.
- Both bridges consume the same reference output: Bridge-D compares
  `TGoal.render : TGoal → GoalAst` against the serialized production LExpr; Bridge-R
  checks `rendered-stmt = toProp env g` by `rfl`. Run Bridge-D everywhere first (it IS
  the W3 differential gate, in-kernel); adopt Bridge-R per goal family as W4 matures;
  the W8 flip retires the residual pp trust.

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
| **W0** | **COMPLETE (§11, `probe-w0/` P1–P7 + `bootstrap-fixture/`).** Both bridge mechanics validated (toy + two real goals: P6 assert w/ decorations+instances+let-in-Prop, P7 loop-maintain w/ telescope+shadowing+casts); WF constraint found + mitigation confirmed (→ W1.5); costs measured; goal-language sort story pinned (Int-with-bound-hyps exec / Nat spec); fixture corpus built (18 fns, emits 20/0). | the whole concept — validated with zero tactus changes | done |
| **W1.5** | **Emitter brick (prerequisite for W2, benefits everyone):** emit `termination_by structural x` when a recursive spec fn's decreases measure is a bare structurally-decreasing param (datatype or Nat) — §11 P3 shows plain `termination_by` (WF) makes emitted spec fns kernel-INERT (`decide`/`rfl` stuck, `unseal` no rescue), while `structural` restores full reduction with an EMPTY axiom closure (no `Tactus.heightLt`). Fallback ladder rung: keep WF emission when structural elaboration fails. Independent win outside R2: user goals over such spec fns become `decide`-closable. | refWp's Lean form actually computes; also a T1-automation win | small |
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
.rs of tactus-core (refWp + SstSem spec fns, refWp_sound proof fns)
        │  authored in tactus, verified by the tactus binary (lean-only routing)
        │  + a small hand-Lean layer (toProp/SymEnv/adequacy spine — §4.3):
        │    part of the SPEC, audited once, kernel-checked like everything else
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

- **O1 (W0):** ~~Bridge-R defeq feasibility + kernel cost~~ **answered at toy scale
  (§11)**: denotation `rfl` works incl. binders/SymEnv; Bridge-D `decide` on a
  600-statement fn ≈ 2.8s wall incl. ~1s process floor. Remaining: real-goal-shape
  cost, and batching (per-Verus-module bridge files to amortize the floor; generated
  bridge modules must `set_option maxRecDepth` — kernel recursion depth scales with
  WP chain depth, §11 P2).
- **O2 (W1):** mirror-type single-source-of-truth: generate the Lean inductives from
  the Rust types (build.rs) or hand-write + golden-test? Lean-side generation is less
  trusted code; hand-written is more auditable. Lean-side wins if the subset is stable.
- **O3 (W2):** spec-fn `refWp` computability in the kernel — TWO constraints, one per
  probe: (a) choice-freedom: `Classical.epsilon` anywhere in the emitted defs (via
  `choose`-like constructs) breaks `decide`; keep tactus-core's source in the
  choice-free fragment (lintable via the defs' axiom closure). (b) **recursion
  compilation (§11 P3, the sharper one):** tactus emits every recursive spec fn with
  `termination_by` ⇒ WF-compiled ⇒ kernel-inert. W1.5 (structural emission) is the
  fix; simp-with-equation-lemmas is the proven fallback bridge tactic if any
  tactus-core fn genuinely needs a non-structural measure.
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
- **O9 (W1/W2, from P6):** tactus datatypes are non-indexed, so the tactus-authored
  goal language is *extrinsically* typed — `refWp` outputs plain data; the hand-Lean
  denotation layer sort-checks (partial `toProp : TGoal → Option Prop`, bridge
  asserts `= some rendered`, or a total default-False form). Decide the partiality
  convention with the first real telescope.

---

## 10. Bricks summary

Near-term, in order: **W0** (spike, days) → **W1** (serializer) → **W2** (reference WP
stage A) → **W3** (differential gate — first real payoff: bug-finding) → [R1 merge] →
**W4** (kernel bridge on). Long-running in parallel from W2 onward: **W5a–e**
(soundness, the formalization). Then W6 → W7 → (soak) → W8.

Independent of all of it, still-open bricks from the sibling docs that this plan
*leans on*: T/B1 histogram (now nearly free via ladder sidecars), closure-doc §4
prelude hygiene, R1/M6.0b Ref-ABI, R0a tactic-strength (Danielle's).

---

## 11. W0 pre-probe findings (2026-07-11, `probe-w0/`, lean 4.25.0, pure core)

Run the same day as rev 1, before any implementation. Five files, each answering one
load-bearing unknown; every claim below is pinned by a probe file that elaborates (or
deliberately fails) standalone with no Mathlib.

- **P1 (`probe1_structural.lean`) — Bridge-D mechanics work.** A structurally-compiled
  `refWp` over a 5-constructor mini-SST kernel-evaluates on concrete data under both
  `decide` (derived `DecidableEq`) and `rfl`; `#print axioms refWp` = none. 0.9s incl.
  process start.
- **P2 (`probe2_cost.lean`) — Bridge-D cost is fine, with one emission detail.** A
  generated 600-statement program (150 assign/assert/ite units) bridge-checks by
  `decide` in **2.8s wall** (≈1s of that is process floor). First attempt hit
  `maximum recursion depth` — kernel/elaborator recursion scales with WP chain depth,
  so generated bridge modules must emit `set_option maxRecDepth`. Consequence for
  W4: batch bridges per Verus module to amortize the floor; typical fns are far
  smaller than this probe.
- **P3 (`probe3_wf.lean` + `probe3b_unseal.lean`) — THE CONSTRAINT: WF-compiled defs
  are kernel-inert.** The same `refWp` with explicit `termination_by <Nat measure>`
  (exactly what `to_lean_fn.rs:324` emits for every recursive spec fn with a
  `decreases` clause): `decide` gets stuck at the derived `DecidableEq` instance
  application (`did not reduce to isTrue/isFalse`), and `unseal … in` does **not**
  rescue `rfl`. `simp [refWpWF, …]` (equation lemmas) DOES close it — the deterministic
  fallback. Direct consequence: **a tactus-authored refWp is kernel-inert under
  today's emission** — hence brick W1.5.
- **P3c (`probe3c_structural_tb.lean`) — the mitigation works.** The same def with
  `termination_by structural s` restores full `decide`/`rfl` evaluation with an
  **empty axiom closure** (the current datatype-measure emission would additionally
  drag `Tactus.heightLt` into every recursive spec fn's closure — structural emission
  is a trust-hygiene win independent of R2).
- **P4 (`probe4_denote.lean`) — the denotation rfl-bridge works.** A typed goal
  language (`TGoal` with de Bruijn `tforall`/`timpLe`/`tconj`/`teq` over Int
  expressions) with a structural denotation `gdenote : List Int → TGoal → Prop`
  satisfies `gdenote [] g = (∀ x : Int, 0 ≤ x → (x + 0 = x ∧ ∀ y, …)) := by rfl` —
  nested binders, env lookups under bound variables (`(x :: env).getD 0` iota-reduces
  with x still abstract), and Int-literal elaboration all agree definitionally. This
  is the W5 soundness path's load-bearing mechanic, validated.
- **P5 (`probe5_symenv.lean`) — the dependent symbol environment survives the
  bridge.** Goals referencing *user spec fns* and quantifying over *user datatypes*
  denote through a `SymEnv` structure (`U : Type`, `ifns : Nat → (Int → Int)`, …)
  instantiated by a generated per-crate match-literal — and still `rfl`-bridge to the
  production-rendered Prop naming the real fns (`∀ c : Color, colorRank c = myAbs
  (-3)`). This validates the §4.3 authorship split: the denotation layer (returns
  `Prop`/`Type`) is hand-Lean; everything data-level stays tactus-authored.

- **P6 (`probe6_real_goal.lean`) — a REAL emitted goal bridges.** The assert obligation
  of tgt's `find_cancellation_exec` (island output preserved in `/tmp/fcx_scratch.lean`,
  M6.1-era), goal copied **verbatim** — `Tactus.Ref` decoration with type ascription,
  `view.View.view` instance dispatch (instance resolved by the elaborator on the
  rendered side, carried as a plain function in `SymEnv` on the reference side —
  defeq agrees), **`let tmp__1 := …` bindings inside the Prop** (zeta closes both
  sides), `usize_hi`, the `0 ≤ len ∧ len < usize_hi` overflow guard, opaque axiom
  types (`vec.Vec`, `seq.Seq`), and a WF-compiled recursive user spec fn
  (`find_cancellation_from`) appearing as an opaque symbol — `rfl` closes the bridge
  in 0.9s. Two corollaries: (a) **the P3 constraint scopes to tactus-core's own
  defs only** — user spec fns in goals are named, never evaluated, so their WF
  compilation is irrelevant to the bridge; (b) the probe's sort-indexed `TExpr`
  worked well in hand-Lean, but **tactus datatypes are non-indexed** — the
  tactus-authored `refWp` must output *extrinsically*-typed data with Lean-side
  sort-checking in the denotation layer (new O9).

Net: **no blockers; one real constraint (P3) with a confirmed small mitigation (P3c →
W1.5); both bridge forms mechanically validated on toy AND real goals; cost in
budget.** Remaining W0 residue, now small: a loop init/maintain/use triple goal
(same connective vocabulary + nested ∀, both probed separately — P4 has nested
binders; compose them on a real loop fn), an `Int.ofNat` coercion site, and the
general binder-telescope scheme (engineering, not risk).

- **P7 (`probe7_loop_triple.lean`) — the real LOOP-MAINTAIN goal bridges. W0 COMPLETE.**
  The fixture's `sum_to` invariant-3 maintain obligation
  (`_tactus_loop_invariant_sum_to_at_lib_113_13_9`), verbatim: the loop-state ∀ is a
  telescope of **signature binders with hypothesis binders interleaved** (the
  CtxFrame architecture — no nested quantifiers; the M1 stmt ∀-closure IS the goal),
  Int-typed lets including **let-shadowing of binders** (`let i := i + 1`, the
  SSA-via-shadowing idiom — defeq is insensitive to shadowing, both sides zeta-reduce),
  the `_tactus_d_old_0_0` decrease snapshot, duplicated overflow guards (faithful),
  `Int.toNat` materialization sites, and the WF-emitted `lib.tri` as an opaque symbol.
  Two-sorted goal language (Int exec side with bound-hyps + Nat spec side, per the
  §11.1 census) — `rfl` closes in 0.6s. One idiom note for W2: build deep goal terms
  as named layers, not one paren tower.

### 11.1 The fixture crate (`bootstrap-fixture/`)

The canonical minimal module covering the goal-shape matrix — one tiny fn per
shape, F1–F19 labels in-source. Emits clean today (**20 verified / 0 errors, 18
fns**, via `--lean-backend --emit-lean --lean-all-proofs`; command in the file
header; `out/` regenerable, gitignored). Roles: the W0 hand-bridge target set
(its `sum_to.lean` has the loop triple with casts in invariants — 13
`toNat`/`Int.ofNat` sites; `find_square.lean` the nested-loop/early-return worst
case, 19 obligations; `fill_zeros.lean` quantified invariants), the W1 serializer's
first corpus, and the W3 differential gate's smoke set before tgt. Coverage:
spec fns (plain / Nat-recursive / datatype-recursive with match+Box), proof fns
(plain route, tactic block, assert, cast shapes), exec fns (overflow,
value-position if, loop triple, nested loops + early return, call contracts,
exec recursion/decreases, Vec view + `&mut` + `old()`, generic `T`, enum match,
quantified ensures/invariants, struct/tuple). Recorded residue: closures and
break/continue (add when W2 reaches their `Wp` arms).

Two shape facts the census surfaced, for the goal-language design: **exec
integer params render as `Int` plus a bound hypothesis** (`h_x_bound : 0 ≤ x ∧
x < 2^64`), not `Nat` — the TGoal sort story is Int-with-hyps on the exec side,
Nat on the spec side; and exec island files still over-include unrelated proof
fns (the documented safe over-approximation) — bridge pairing must key on the
fn's own obligations (O4's ids), never on file contents.

## 11.2 W1.5/W1 pre-probes (P8, same day)

- **P8 FOUND A REAL EMITTER BUG**: a recursive spec fn over an own Box-carrying
  datatype (`bootstrap-fixture/w15_probe.rs`) emits `esize a` at type
  `Tactus.Box PExpr` — the `.deref` is dropped on match-bound Box fields; the
  island (`probe-w0/probe8_authoring_loop.lean` context) fails elaboration.
  Never seen live because `--emit-lean` skips the Lean run. Exactly the W3
  bug class, caught by a probe. Fix belongs with W1.5 (same rendering area).
- **P8b (`probe8b_box_structural.lean`)**: the post-fix shape — recursion via
  `Box.deref` projections — IS accepted by `termination_by structural` and
  kernel-reduces (decide + rfl, zero axioms). W1.5 works for the real
  mirror-type authoring idiom.
- Scope pin for W1.5: `tri`-style `Int.toNat (n - 1)` recursion is NOT
  structural — the feature applies to datatype-subterm recursion (+ the fix);
  Nat-arith recursion keeps WF + simp-eq-lemma bridging.
- W1 constraint: mirror types must use own cons-lists, never `Seq` fields
  (opaque axiom type — no match, no reduction).

**FIX LANDED on this branch (same day):** match-arm pattern binders now enter
`ctx.binder_typs` (`to_lean_expr.rs`, Quant-arm idiom + recursive
`collect_pattern_binding_typs`), so spec-mode uses of Box/Rc-decorated
pattern vars re-materialize `.deref` via the existing use-site coercion.
w15_probe island elaborates green vs the real prelude; **full e2e suite
533/0**; P8 regenerated on the fixed emission: `termination_by structural`
flip on real emitted esize/lsize = kernel decide/rfl, zero axioms — the
W1.5 authoring loop validated end to end. (Explains the old asymmetry:
generated height fns always emitted `.deref`; only user match bodies
lacked it.) Residue noted: `block_to_node` Decl-bound pattern vars share
the hazard class in principle — same map-extension fix if a repro appears.

**W1.5 LANDED (this branch): `#[verifier::structural_decreases]`.** Opt-in
per-fn attribute (heartbeats-pattern plumbing: attributes.rs → VerifierAttrs →
vir FunctionAttrs → to_lean_fn); when the decreases measure is a bare
datatype-typed param, spec fns emit `termination_by structural <param>` with
no decreasing_by (kernel-computable, no heightLt in closure); any other
measure shape falls back silently to WF emission — visible in the artifact
termination_by line, never a hard failure. Def gains `termination_structural`;
pp renders the `structural` keyword. Proof-fn structural emission deferred to
W5 (Theorem struct, recursive proof fns). Pinned by two e2e tests, incl. the
discriminating `decide` closer (passes ONLY under structural emission).
Suite 543/0.

**NEW BUG PINNED while testing (ctor-arg sibling of RC4):** `Box::new`
erasure at CONSTRUCTOR argument slots misses the `.mk` wrap —
`Expr.Add (Expr.Lit 3)` renders unwrapped where `Tactus.Box Expr` is
expected ("Application type mismatch" at elaboration). Fix needs declared
field typs at ctor render sites (RenderCtx has no datatype map — real
plumbing, own brick). Repro = the commented construction in
test_structural_decreases_kernel_computes.

**REVIEW PASS (same day):** (a) crate-defs/package spec-world emission goes
through the SAME `spec_fn_to_ast` — structural_decreases renders identically
in islands and defs modules, no render divergence (DefCurried has no
production constructor — vestigial). (b) The documented Decl-let residue was
A LIVE BUG (review probe: `let b = l; tsize(*b)` rendered bare, island RED)
— `block_to_node` rewritten to forward recursion threading pattern bindings
through `ctx.binder_typs`; pinned by `test_spec_let_box_use_derefs`.
(c) structural helper tightened: decorated (`&Tree`) params now keep WF
(structural on a `Tactus.Ref`-wrapped binder is unvalidated). Suite 544/0.
Still-open review items: attribute silently ignored on mutual spec fns and
proof/exec fns (document-or-warn, W5); SST-path (exec obligation) match
binders unaudited for the same class — accessor-based, likely fine, worth a
probe when M6.2 lands; fixture not yet exercising --tactus-package-check.

**CTOR-ARG BUG FIXED (same day):** `Box::new` erasure at constructor slots
now re-wraps via declared-slot coercion — new ambient table `CTOR_FIELD_TYPS`
(all datatypes, all variants, raw field names + typ params) installed by
`install_datatype_field_bounds` alongside `DATATYPE_FIELDS` (the blessed
ambient-table idiom pending the typed-renderer migration); `ctor_to_node` +
StructUpdate values coerce each rendered field to the instantiated declared
typ via `coerce_lexpr` (wrapper-only, identity on agreement, skip on unknown
datatypes). Typ args from `expr.typ` (decoration-stripped). The kernel_computes
e2e is now the COMPOUND pin: Box ctor coercion + structural emission + kernel
`decide` in one goal. Battery 544/0. SST-path ctor sites remain unaudited for
the same class (M6.2-era probe).

---

## 12. Next steps — post-roll execution order (planned 2026-07-11, evening)

Session-sized bricks, in order. Everything below assumes the `bootstrap`
worktree, `vargo test --release` for e2e, and Danielle's guidance that
emit-module/package-check flags are the future default.

- **N1 (small, warm-up): close today's residue.**
  (a) Fixture emission commands gain `--tactus-package-check` (island fallback
  stays); record any package-path surprises. (b) Annotate `w15_probe.rs`'s
  `esize`/`lsize` with `#[verifier::structural_decreases]`; regenerate probe8
  from the emission with NO manual flip — the W1.5 loop becomes emitter-native.
  (c) SST-path probes for today's two bug classes on exec obligations: an exec
  fn constructing `Expr::Add(Box::new(..), ..)` + one matching on Box-field
  datatypes; fix-or-pin (the SST renderer stamps differently — unaudited).

- **N2 (medium): tactus-core skeleton = the mirror types, AS TACTUS CODE.**
  New crate `tactus-core`: `SstData`/`ExprLeaf`/`GoalData` datatypes covering
  the Wp-input subset, with OWN CONS-LISTS (never Seq — P8's kernel-inertness
  constraint), extrinsically typed (O9: tactus datatypes are non-indexed),
  `structural_decreases` on every recursive spec fn from day one, verified
  lean-only-clean. **The crate-defs emission of these datatypes IS the Lean
  mirror vocabulary** — the serializer targets those emitted names; hand-Lean
  is reserved for the denotation glue (§4.3). Include a golden unit test
  pinning the covered `vir::sst` variant list (fails loudly when vir::sst
  grows — the manual-sync tripwire).

- **N3 (medium-large): the serializer — SPEC'D in `DESIGN-N3-serializer.md`
  (2026-07-12): snapshot at `exec_fn_theorems_to_ast` inputs; faithfulness
  contract table; leaf interning via production renderer (structure-only
  stage-A claim, leaves cancel); goal-side via Wp provenance marks (N3b, the
  one production touch); `--tactus-emit-cert`; acceptance incl. N5 smoke +
  golden file + determinism. Sub-bricks N3a/b/c.**
  Rust, boring, 1:1, target <1k lines: from `build_wp`'s inputs (fn_sst body
  Stm tree + the WpCtx spec context: params/typs, requires, ensures,
  invariants, decrease) to Lean literals in the N2 vocabulary. Enumerate the
  captured WpCtx fields explicitly in a doc comment — that list is the
  faithfulness contract. FAIL LOUDLY outside the subset. Acceptance: the
  fixture serializes 100%, literals written next to islands.

- **N4 (small): corpus census.** Run the serializer over tgt (3116 fns):
  % serializable + a ranked table of unsupported constructs — this sets W2's
  coverage roadmap and is the first honest measure of subset size.

- **N5 (small): literal smoke.** Every fixture literal elaborates against the
  tactus-core defs olean (`lean` with LEAN_PATH, or package-check if N1a made
  that natural). Cold + warm timing noted.

- **Then W2 (multi-session): refWp stage A** per §5 — after N2 stabilizes the
  `SstData` shape. Obligation ids emitted by refWp, pairing by id (O4).

Standing coordination notes: the branch contains emit-module wholesale — when
emit-module merges to main, sync this branch promptly (the three bug fixes +
W1.5 may be wanted on main earlier; cherry-pick is clean, Danielle's call).
The F6 fable's work overlaps `to_lean_expr.rs` — mention the Match-arm merge
resolution (`e61d4d8`) to whoever merges next.

**N1 COMPLETE (post-roll session):**
(a) `--tactus-package-check` VALIDATED live on w15_probe (7/0, package gate:
composition + axiom closures kernel-verified; canonical command now in the
file header). lib.rs runs the gate too but carries 12 pre-existing unclosed
proofs (identical set in island mode — closure debt, not package surprises;
fixture-debt item for the W3 era). Package artifacts ride the lean-project
workspace, not TACTUS_LEAN_OUT.
(b) probe8 regenerated EMITTER-NATIVE: attribute on esize/lsize, verbatim
emitted text, decide/rfl, zero axioms, zero manual edits.
(c) SST-path probes: **ctor class = REAL BUG, FIXED** — exec-obligation
ensures rendered erased Box::new ctors bare; the SST ExpX::Ctor arm now
bridges NON-VAR-LIKE fields into declared slots via the typed spine
(into_slot; var-like fields — locals under poly/mode wrappers — stay at
storage depth, where claims can lie bare for Box::new temporaries). Pinned
by test_sst_ctor_box_slot_coercion. **Match-binder class = NO BUG** (SST
accessor rendering derefs correctly); left_val closed with an explicit
split/cases closer. Residual pinned: spec-side let-bound/field-read vars in
Box slots with env-invisible binders would still render bare — the honest
wide fix is truthful claims (upstream U2 work).
Battery: e2e 545/0, lean_verify 299+7/0.

**GATE REMOVAL + N2 (post-roll session 2):** Danielle: defs size gate (<2
checked fns → islands) removed for predictability. Removal EXPOSED 5 real
gaps the gate hid, ALL FIXED: (1) stmt modules lacked theorems'
requires_preamble (BitVec Int instances) — threaded; (2) pkg exec failure
header said "tactic" where islands say "tactus_auto" — mode-keyed parity;
(3) **soundness**: exec-only crates get no Link gate, so pkg-path sorry was
warning-only → sorry now FATAL on every per-fn path (Link stays the
cached-verdict backstop); (4) assume(P) warnings dropped by the pkg exec
route — threaded; (5) WP-routed proof fns (Verus body, no tactic block)
were neither defs-walk roots nor accessor triggers — both widened. Suite
549/0; cost of uniformity: suite 131.7s vs 71.6s (every crate builds defs).

**N2 SKELETON LANDED: `tactus-core/lib.rs`** — LeafList/StmData/GoalData/
GoalList mirror types (stage-A StmX subset, opaque u64 leaves), sequencing
via Seq/Skip (NO mutual recursion — structural_decreases is single-fn),
structural on all 4 recursive spec fns, in-crate `decide` sanity proofs =
kernel-computation validated live; 6/0 under the package gate (defs module
= the Lean vocabulary exists). Golden tripwire
`lean_verify/src/tests/bootstrap_coverage.rs`: exhaustive StmX match, 9
covered / 9 deliberately-uncovered — compile-fails when vir::sst grows.
N2 residue: probe9 (extract emitted vocabulary, decide against it) — fold
into N3 acceptance.
