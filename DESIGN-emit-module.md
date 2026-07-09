# Emit-module: whole-crate package emission — design

**Date:** 2026-07-09
**Status:** spec, on branch `emit-module` (worktree, isolated from main-line dev)
**Builds on:** CRATEDEFS.md steps 0/1a/1b/1c (prelude olean, `--tactus-crate-defs`,
batch verification), DESIGN-axiom-closure-check.md, DESIGN-transparent-automation.md
**Scope:** emit each crate as one Lean *package* whose composition is
kernel-checked — zero same-crate axioms, circularity structurally impossible,
statement drift impossible — while keeping (likely improving) per-fn iteration
speed. The architecture is hypothesis-passing proof modules + a generated linker.

---

## TL;DR

- **Four layers per crate**: `Defs` (spec fns, datatypes, instances — *exists
  today* as the crate-defs module), `Stmts` (NEW: each proof fn's ∀-closed
  requires→ensures as a named `def : Prop`), `Proofs` (one module per fn:
  `theorem f_thm (h_g : g_stmt) … : f_stmt`, importing only *statement* modules),
  and `Link` (NEW, generated: `theorem f_closed : f_stmt := f_thm g_closed …` —
  pure applications, fast, plus the crate-level axiom-closure check).
- **Why hypotheses instead of importing callee theorems directly**: Lake
  invalidates by olean hash and proofs live in oleans — direct theorem imports
  mean every proof-body edit re-elaborates all transitive dependents (Mathlib's
  daily pain). With hypothesis-passing, dependents import only `Stmts` oleans,
  which are byte-stable under body edits. The resulting invalidation semantics
  **exactly match the verus-dev cache**: body edit → that fn + relink; signature
  edit → that fn + callers; defs edit → wide. Kernel-checked composition with
  cache-shaped incrementality.
- **This kills two documented problems with one mechanism**: the trust problem
  (broadcast/helper lemmas as axioms; cross-file circularity and statement drift
  Rust-trusted) and the cost problem CRATEDEFS measured (same-crate helper
  theorems re-elaborated in every citing file — quadratic on deep chains).
- **Iteration speed should improve, not regress**: today an island file
  re-elaborates its dependency closure's *proof bodies*; a package-mode per-fn
  check elaborates one theorem against prebuilt oleans. Batch mode's −76% on
  deep chains is the cold-gate bound; single-fn warm checks beat islands.
- **Honest scope**: exec-call contract inlining stays a WP-calculus argument
  (that's the verified-WP arc's job) — but `Stmts` gives req/ens *named defs
  used by both sides*, so contract drift becomes impossible by construction
  even before the WP calculus is verified.
- Entry brick **M0 is a hand-written spike**: author the target Lean shape for a
  toy crate by hand, validate elaboration + invalidation behavior, measure. No
  tactus code changes.

---

## 1. Problem restatement (what today's emission trusts and re-pays)

Island emission (per-fn `.lean`), even with crate-defs + batch landed:

| Issue | Kind | Where documented |
|---|---|---|
| Same-crate helper proof fns re-elaborated as full theorems in every citing file — quadratic along helper chains | cost | CRATEDEFS "problem, measured" |
| Broadcast lemmas + cross-crate ensures emitted as `axiom`s; "separately discharged" is a Rust-side claim | trust | generate.rs #122 comments; DESIGN-axiom-closure-check §1 |
| Cross-file circular axiomatization undetectable by any per-file check | trust | DESIGN-axiom-closure-check "what it does NOT catch" |
| Axiom statement vs. discharged theorem drift (impl_subst specialization) | trust | same |
| Batch mode: any edit re-elaborates the whole batch file; error attribution needs region machinery + poison fallback | cost/complexity | CRATEDEFS 1b |

Package emission addresses all five with one structure.

---

## 2. Architecture

### 2.1 The four layers

```
Tgt/Defs/<M>.lean      -- per Verus module M: datatypes (+height), spec fn defs,
                       --   instances; imports Defs of dep modules + TactusDefs
Tgt/Stmts/<M>.lean     -- per Verus module M: for each proof fn f,
                       --   def f_stmt : Prop := ∀ …, requires → ensures
                       --   for each exec fn g: def g_req …, def g_ens …
                       --   imports Defs only
Tgt/Proofs/<fn>.lean   -- per fn: theorem f_thm (h₁ : g_stmt) … : f_stmt := by …
                       --   imports Stmts of own + direct callees; NEVER Proofs
Tgt/Link.lean          -- theorem f_closed : f_stmt := f_thm g_closed h_closed …
                       --   in dep_order topological order; SCCs linked as units;
                       --   crate axiom-closure check at the end
Tgt/Boundary.lean      -- cross-crate axioms (vstd ensures, broadcast), explicit
                       --   and whitelisted; shrinks to imports when vstd itself
                       --   is emitted as a package (M6)
```

- `Defs` is the existing crate-defs module, split per Verus module for finer
  invalidation — which also resolves CRATEDEFS 1c's bucket-alignment finding
  (per-module defs "matches Verus's own unit of work").
- `Stmts` is small and cheap: `Prop`-valued defs, no proofs, no tactics. Its
  olean is byte-stable under any proof-body edit anywhere.
- `Proofs` modules contain exactly one theorem (or one mutual block, §4.3).
- `Link` is machine-generated applications — each line's type check is a defeq
  between syntactically identical terms. Thousands of lines elaborate in seconds.

### 2.2 Worked example (target shape, hand-writable today)

Verus source:

```rust
proof fn lemma_a(x: nat) ensures x + 0 == x { }
proof fn lemma_b(x: nat) ensures x + 0 + 0 == x { proof { lemma_a(x); } … }
```

Emitted package:

```lean
-- Tgt/Stmts/M.lean            (abbrev, not def — see M0 finding F2)
import Tgt.Defs.M
abbrev lemma_a_stmt : Prop := ∀ (x : Int), 0 ≤ x → x + 0 = x
abbrev lemma_b_stmt : Prop := ∀ (x : Int), 0 ≤ x → x + 0 + 0 = x

-- Tgt/Proofs/M_lemma_a.lean   (reducibility ⇒ no unfold gymnastics)
import Tgt.Stmts.M
theorem lemma_a_thm : lemma_a_stmt := by
  intro x hx; omega

-- Tgt/Proofs/M_lemma_b.lean
import Tgt.Stmts.M
theorem lemma_b_thm (h_a : lemma_a_stmt) : lemma_b_stmt := by
  intro x hx; have := h_a x hx; omega

-- Tgt/Link.lean
import Tgt.Proofs.M_lemma_a
import Tgt.Proofs.M_lemma_b
theorem lemma_a_closed : lemma_a_stmt := lemma_a_thm
theorem lemma_b_closed : lemma_b_stmt := lemma_b_thm lemma_a_closed
#tactus_check_axioms lemma_b_closed []   -- closure ⊆ core ∪ prelude
```

Editing `lemma_a`'s *body* re-elaborates `M_lemma_a` + `Link` only.
Editing `lemma_a`'s *ensures* changes `Stmts/M` → `M_lemma_a`, `M_lemma_b`
(imports the stmt), and `Link` re-elaborate. Exactly the verus-dev cache table.

### 2.3 Invalidation semantics (the answer to "does iteration stay fast")

| Edit | verus-dev cache re-verifies | package mode re-elaborates |
|---|---|---|
| fn body only | just that fn | that fn's Proofs module + Link |
| fn requires/ensures | fn + transitive callers | Stmts module → fn + *direct* importers (callers) + Link |
| datatype / spec fn / new fn in module | whole module's functions | Defs/⟨M⟩ → its import cone |
| nothing | nothing (all cache hits) | nothing (all olean traces valid) |

Two notes. First, "direct importers" is *finer* than the cache's transitive
invalidation — a caller whose proof re-elaborates green against the new
statement doesn't propagate further unless its own Stmts changed. Second, the
per-fn dev check gets *faster* than islands: an island re-elaborates its dep
closure's definitions and helper-theorem bodies every run (CRATEDEFS: this is
the quadratic term); a package check elaborates one theorem against oleans.

---

## 3. Why not the two simpler variants

**(A) Import callee Proofs directly, cite `g_thm`.** No Stmts layer, no
hypotheses, no linker. But proofs live in oleans, Lake invalidates by olean
hash → every body edit cascades through all transitive dependents. On
group-theory-shaped helper chains that's most of the crate per edit. Rejected
for the same reason Mathlib suffers: Lean has no proof-irrelevant interface
hashing, so we build the interface layer ourselves — that's what Stmts is.

**(B) One batch file (status quo maximalist).** Already landed for the cold
gate and it's good there (−76% deep-chain). But any edit re-elaborates the
file, error attribution needs region machinery, and axioms remain for
broadcast. Package mode subsumes batch: the gate is `lake build` (parallel
over Proofs modules — same parallelism, no attribution machinery: errors land
in the right file natively).

---

## 4. Emission details

### 4.1 Statements

The `f_stmt` renderer is not new machinery: it is exactly the ∀-closure of
requires→ensures that `broadcast_lemma_axiom_cmd` renders today — the target
changes from `axiom f_ax : ⟨stmt⟩` to `def f_stmt : Prop := ⟨stmt⟩` plus
`theorem f_thm (…) : f_stmt`. Prop impredicativity covers generic fns
(`∀ (A : Type u), …` is a `Prop`); `[Nonempty A]`-bracketing (nonempty.rs)
carries over unchanged as binders inside the stmt.

### 4.2 Proofs with hypotheses

- Hypothesis list = direct proof-fn callees + broadcast lemmas the fn uses
  (`broadcast_collect.rs` already computes this per fn). Same-crate broadcast
  lemmas thereby stop being axioms.
- Where the island proof cited a global axiom, the package proof cites a local
  hypothesis — for the tactic layer this is *at worst* neutral and often
  better: `simp_all`/`omega` consume local hypotheses natively, whereas env
  axioms need explicit mention. Pins (DESIGN-transparent-automation) are
  keyed on obligation ids and are unaffected.
- **impl_subst interaction (open question O3):** where today's emission
  specializes a callee's axiom per call site, the hypothesis can either be the
  general statement (proof instantiates it) or one hypothesis per
  specialization (mirrors current terms exactly). Start with
  per-specialization — it's term-identical to what tactic bodies already
  expect — and generalize later if hypothesis lists get long.

### 4.3 Mutual recursion

Mutually recursive proof fns (dep_order `FnGroup::Mutual`) go in one Proofs
module as a `mutual` theorem block with the existing `termination_by`/
`decreasing_by` emission; the linker closes the whole SCC as a unit. Their
*statements* are ordinary separate defs — no mutuality at the Stmts layer.
Two sharpenings from M0 (F3/F4): recursive/mutual theorems must keep the
**parameterized** type (real binders for `termination_by` — a bare
`theorem f_thm : f_stmt` has nothing to recurse on); the linker bridges to
the stmt-typed closed form by direct reference (definitional eta makes
`theorem f_closed : f_stmt := f_thm` typecheck). Within-SCC references are
direct (same mutual block) — only SCC-external callees become hypotheses.

### 4.4 Exec fns

Exec fns' WP theorems stay self-contained in their Proofs module (nobody cites
an exec fn's theorem; callers consume its *contract*). What moves to Stmts is
`f_req`/`f_ens` as named defs, **used by both** the fn's own WP theorem and
every caller's WP goal (today the contract is textually inlined per call site
via inline_spec). Result: contract drift between definition site and call
sites becomes impossible by construction. The WP call rule itself — "assuming
`g_ens` for the returned value is sound because g's body was verified" — is a
semantics-level argument that only the verified-WP arc (tactus-core) can
discharge; this design deliberately does not pretend to close it, it just
removes the textual-copy failure mode and hands R2 a cleaner target.

### 4.5 Trust accounting after M5

| Surface | Island mode | Package mode |
|---|---|---|
| same-crate helper lemmas | re-elaborated per file (sound, quadratic) | theorems, elaborated once |
| same-crate broadcast lemmas | axioms (Rust-trusted discharge) | theorems + hypotheses |
| cross-file circularity | Rust-trusted (dep_order) | impossible (import DAG + Link) |
| statement drift | Rust-trusted (impl_subst) | impossible (shared defs) |
| cross-crate / vstd | axioms | Boundary module (explicit, closure-whitelisted) → imports at M6 |
| exec call rule, frontend, prelude | trusted | unchanged (R2 / documented) |

---

## 5. Build orchestration

- **Package layout**: a real lake project under
  `target/tactus-lean/<crate>-pkg/`, lakefile generated. The gate runs
  `lake build` — incremental + parallel natively, replacing batch-mode's
  bespoke chunking/attribution.
- **Single-fn dev check bypasses lake** (CRATEDEFS 1c's resolved-LEAN_PATH
  trick): plain `lean` on the one Proofs file with the package's olean dirs
  prepended — no lake lock, ~spawn + olean-load + one-theorem cost. Rebuilding
  stale Defs/Stmts oleans on demand reuses the step-0 atomic-rename pattern.
- **Verus-cache coupling**: the existing SST-hash cache decides *whether* a fn
  needs re-verification; package mode adds nothing to decide — a cache hit
  skips the Lean run exactly as today. Lake's traces are a second, coarser
  guard underneath.
- `lean_out_root()` absoluteness, prelude olean cache, `set_option`
  re-emission: all inherited as-is from CRATEDEFS step 0/1c.

---

## 6. Migration path

| Brick | Content | Validates | Size |
|---|---|---|---|
| **M0** | **Hand-written spike**: author the §2.2 shape for a toy crate (3 chained lemmas, 1 mutual pair, 1 broadcast use, 1 generic fn, 1 exec fn) directly in Lean; confirm elaboration, measure single-module re-elaboration + relink wall-time vs. an equivalent island set; touch a body vs. a statement and watch what rebuilds | the whole concept, zero tactus changes | small |
| M1 | Stmts renderer (retarget the broadcast-axiom statement machinery to `def : Prop` + theorem headers) | §4.1 | medium |
| M2 | Proofs-module emission behind `--tactus-emit-module`; hypothesis plumbing; islands untouched | §4.2–4.4 | large |
| M3 | Link + Boundary generation; `#tactus_check_axioms` integration (closure ⊆ core ∪ prelude ∪ Boundary) | §2.1, trust table | medium |
| M4 | Build orchestration: lakefile gen, single-fn fast path, on-demand olean refresh | §5 | medium |
| M5 | Real-crate cutover (gate crate runs package mode; A/B vs islands+batch; retire batch if subsumed) | everything | medium |
| M6 | vstd as a package; Boundary shrinks to imports | trust table last row | later |

M0 is genuinely load-bearing, not ceremony: it will surface the Lean-side
surprises (olean trace behavior under byte-identical rebuilds, `unfold`
ergonomics of stmt defs in tactic bodies, mutual-block linking) while the
design is still cheap to change — CRATEDEFS's probe-first methodology, kept.

## 7. M0 findings (2026-07-09, `probe-m0/` — hand-written package, lean 4.25.0)

The §6 spike ran same-day. The probe (13 modules: Defs, Stmts, 8 per-fn Proofs
covering every checklist shape, Link, root) **builds green, cold, in ~1.4s**;
pure Lean core, no Mathlib needed for any architectural question.

- **F1 — every shape elaborates**: hypothesis-passing, broadcast-as-hypothesis
  (consumed from local context exactly like env axioms — parity confirmed),
  generic stmt with `∀ (A : Type) [Nonempty A]` inside the abbrev (Prop
  impredicativity + instance binders fine), shared `incr_req`/`incr_ens`
  contract defs used by both the exec WP theorem and a caller's WP goal.
- **F2 — Stmts must be `abbrev`, not `def`**: reducibility makes `intro` peel
  the stmt name, `h_a x hx` elaborate, and linker applications unify — zero
  `unfold` gymnastics anywhere in the probe. (§2.2 example updated.)
- **F3/F4 — mutual/recursive form**: parameterized theorem type +
  `termination_by`, linker bridges to stmt-typed closed forms via definitional
  eta; within-SCC references stay direct. Consequence for M2: the *current*
  theorem rendering is reused as-is — the only delta is prepended hypothesis
  binders and the stmt-abbrev layer. (§4.3 updated.)
- **F5 — invalidation validated, sha256-verified**: body edit → exactly
  {edited Proofs module, Link, root} rebuild; consumer modules untouched
  (olean byte-identical, not re-elaborated); Stmts olean byte-stable. At a
  generated 300-fn chain: cold 8.4s (305 modules, parallel), **body-edit
  cycle 1.6s with 299 modules untouched** — flat in crate size except Link.
  No-op build 0.17s.
- **F6 — Link cost measured**: 300 closure lines = 593ms ≈ 0.4s process floor
  + ~0.6ms/line → ~2.2s monolithic at a 2800-fn crate. Two easy mitigations
  when it matters: per-module link files under a root aggregator (only the
  touched module's link rebuilds), and/or dev loop skips linking entirely
  (checking the one Proofs module is the verification; the verus cache
  already tracks per-fn green — Link is a gate artifact).
- **F7 — statement-edit fanout is per-module-coarse** (O1's concrete data):
  editing one stmt rebuilt all 8 Proofs modules importing `Stmts.M`, vs. the
  verus cache's callers-only invalidation. Per-fn (or per-SCC-cluster) stmt
  files would recover exact-caller granularity at the cost of file count.
- **F8 — axiom closure demonstrated**: `#print axioms` on every `_closed`
  theorem reports ⊆ {propext, Quot.sound, Classical.choice} — the package-mode
  gate claim, kernel-confirmed, zero domain axioms.
- **F9 — translator note**: `simp [isOdd]` does *not* unfold mutual-structural
  defs at constructor patterns (`isOdd 0`); defeq-based closers (`rfl`,
  `decide`, bare `exact` at defeq type) work. Emitted proofs touching mutual
  spec fns should prefer defeq forms / `.eq_def` lemmas.
- **F10 — island vs package at toy scale**: 0.47s vs 0.42s for a 3-lemma
  closure (island re-elaborates all helper bodies; package elaborates one
  theorem against oleans). The real-scale version of this measurement is
  CRATEDEFS's (−76% batch on deep chains); the probe confirms the structure,
  not the magnitude.

Net: **no blockers found; two design corrections (F2, F3) folded into §2.2 and
§4.3.** M1 can start on this shape directly.

**M3.5 status (same day): mutual tactic SCCs SUPPORTED in package mode —
a capability islands don't have.** Empirically established first: mutual
tactic-body proof fns FAIL island emission today (8 errors on an
even/odd pair — each island emits its helper before the root, and the
helper cites the root; the existing `Command::Mutual` machinery serves
spec fns only). Package mode fixes this: fns on a direct-reference cycle
emit as ONE canonical module (`pkg/mutual__<first-leaf>.lean`) holding a
`mutual … end` block — verbatim tactic bodies, within-SCC references
direct, `termination_by` from each member's `decreases` (the M0 probe's
`MutualEO` shape, now generator-emitted). Link eta-closes each member
(F3) with closure checks. **Supported iff the SCC has no external helper
deps**: external deps arrive as hypothesis binders, and a verbatim
mutual reference (`lemma_odd k`) cannot pass hypothesis arguments the
user never wrote — such SCCs are rejected at emission with a message
saying exactly that, and Link skips them with an artifact comment.
E2e: even/odd crate → mutual module + Link elaborate green, closure
checks pass. Drive-by fix: `is_lean_keyword` was missing `mutual` (and
`axiom`/`opaque`/`macro`/…) — a crate literally named `mutual` produced
an unescaped `namespace mutual`; pre-existing, affects islands too.

**M3 status (same day): Link + Boundary + axiom-closure check LANDED, e2e-validated.**
`TactusLink_<scope>.lean` (in `pkg/`, memoized per scope like Stmts) closes
every tactic proof fn in dependency order:
`noncomputable def <name>_closed : <name>_stmt := <name> <dep>_closed …`,
each followed by `#tactus_check_axioms <name>_closed [<Boundary>]`.
Argument order is guaranteed identical to M2's hypothesis binder order by
the shared `direct_helper_deps` chokepoint. Cycles in the direct-reference
graph (mutual tactic lemmas — unsupported by islands too) are detected via
tri-state DFS and skipped with a loud artifact comment + eprintln.
Boundary = the `Command::Axiom` names in the defs module (the crate's
entire declared trust surface beyond the prelude). **The
`#tactus_check_axioms` elab command now EXISTS in TactusPrelude**
(DESIGN-axiom-closure-check.md B2): allowed = classical core 3 + the
prelude's own 5 axioms (hardcoded in the same file, versioning together
by the olean content-hash rebuild) + ofReduceBool/trustCompiler
(allowed-but-inventoried) + the explicit list; `sorryAx` always fatal;
subset check. Hand-validated: positives (incl. namespace-relative
resolution), undeclared-axiom rejection with actionable message, sorry
rejection. Full-package e2e on the chain crate: prelude+defs+stmts+pkg
oleans built, **Link elaborates and all closure checks pass**. NOTE: the
prelude olean cache is user-level and shared across checkouts — branch
runs use `TACTUS_PRELUDE_CACHE` to avoid ping-ponging the main checkout's
cache until the branch merges. Remaining for M4: check-mode wiring +
LEAN_PATH orchestration so the package (incl. Link) is elaborated by the
harness rather than by hand.

**M2 status (same day): package emission LANDED on this branch, e2e-validated.**
`--tactus-emit-module` (implies `--tactus-crate-defs` at parse time) emits,
alongside untouched islands: the per-scope Stmts module
(`TactusStmts_<crate>_<fingerprint>.lean`, written next to the defs
artifacts, memo keyed by the scope-fingerprinted module name — the
CRATEDEFS 1c bucket bug avoided by construction) and per-fn `pkg/` Proofs
modules. **The load-bearing trick: hypothesis binders are named by the
helper's SHORT name — exactly the identifier raw tactic text references —
so binder shadowing makes every existing tactic body elaborate unchanged.**
The translator delta was near-zero: `proof_fn_to_ast` output + spliced
binders. Emission hooks before the batch early-return; failures warn and
never fail the island result. E2e on a real chain crate: emitted
`theorem lemma_b (lemma_a : lemma_a_stmt) (n : Nat) : …` with verbatim
body `have h := lemma_a n`; defs+stmts oleans built by hand; **all three
pkg modules elaborate green**. No-flag runs are byte-identical to pre-M2.
Known scope cuts (for M4+): emission-only (no check wiring); in check
mode, batch-covered fns short-circuit before the hook (only `--emit-lean`
covers all fns); exec fns not yet packaged (§4.4 named req/ens defs);
cross-crate broadcast stays axiomatic via the defs union.

**M1 status (same day): Stmts renderer LANDED on this branch.**
`to_lean_fn::proof_fn_stmt_cmd` emits `@[reducible] noncomputable def
<name>_stmt : Prop := ∀ <binders>, <ensures>` — built on the same
`proof_fn_signature` chokepoint as `proof_fn_to_ast` and
`broadcast_lemma_axiom_cmd`, so statement/theorem drift is impossible by
construction; `stmt_name` is the naming chokepoint shared with M2/M3. Zero
pp changes were needed (`Def.attrs` + `write_binders`' Instance/Implicit
kinds already cover the form). Unit tests pin the exact rendered shape
(285/0 suite). The probe's Stmts layer was rewritten from `abbrev` to the
exact emitted form and rebuilds green — `@[reducible] noncomputable def`
has the full abbrev ergonomics (F2) end-to-end. FunctionX-level exercise
against real crates lands with M2's flag wiring.

## 8. Open questions

- **O1 — Proofs granularity**: per-fn (finest invalidation, ~2800 files/oleans
  for tgt-sized crates) vs per-Verus-module (fewer files, module-wide proof
  re-elaboration on any body edit). Proposal: per-fn; Mathlib proves the file
  count is fine. Revisit at M5 with data.
- **O2 — lake vs plain-lean for the gate**: lakefile gen assumed above;
  fallback is a generated topo-order driver using plain `lean` if lake
  overhead/locking annoys (1c precedent).
- **O3 — hypothesis form**: per-specialization vs general (§4.2). Start
  specialized.
- **O4 — do islands survive** as a debugging view ("give me one self-contained
  file for this fn")? Cheap to keep behind the existing flag; decide at M5.
