# Axiom-closure checking — design

**Date:** 2026-07-09
**Status:** B2 IMPLEMENTED (branch `emit-module`, alongside M3 of
DESIGN-emit-module.md): the `#tactus_check_axioms` elab command lives in
`TactusPrelude.lean` and is emitted by the package Link module after every
closed theorem. Base allowed set = classical core + the prelude's own 5
axioms (hardcoded in the same file — they version together via the olean
content-hash rebuild) + `Lean.ofReduceBool`/`Lean.trustCompiler` (§3
option-2 per-theorem tracking is TODO — currently allowed globally);
`sorryAx` fatal; subset semantics; namespace-relative name resolution.
Hand-validated: positives, undeclared-axiom rejection, sorry rejection.
Island-mode emission (B1/B3/B4) and always-on sanity (B6) remain open.
**Scope:** make "this theorem's proof rests on exactly the axioms we think it does" a
machine-checked, per-theorem fact on every Lean run — instead of a belief about the
generator.

---

## TL;DR

- After every emitted `theorem`, the generator appends a
  `#tactus_check_axioms <thm> [<expected axioms>]` command, defined in
  `TactusPrelude.lean`, which computes the theorem's **axiom closure** (the same
  environment walk `#print axioms` uses) and **fails elaboration** if the closure
  contains anything outside the allowed set.
- Allowed set = **(a)** Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`),
  **(b)** the Tactus prelude axioms (currently 5), **(c)** the dependency axioms this
  very file declares (callee `ensures`, broadcast lemmas, cross-crate lemmas) — a list
  the generator already has in hand, since it emitted them.
- `sorryAx` in the closure is a **hard error, always**. The closers' `fail` rungs
  already prevent the known `sorry` paths; this catches every path, including future
  codegen bugs.
- Runs **in-band** during the same `lean` invocation — no output parsing, no extra
  process. `collectAxioms` is a cached environment walk; expected cost is noise-level
  against elaboration.
- This is the **semantic complement to `sanity.rs`** (which checks *references
  resolve*; this checks *proofs rest on declared trust*), and it is the enforcement
  point that a future whole-crate "package mode" soundness claim reduces to: there,
  the allowed set shrinks to (a) ∪ (b) only.

---

## 1. Motivation / threat model

Today the claim "an emitted proof uses only the prelude axioms plus the dependency
axioms we deliberately gave it" is enforced by construction of the generator — i.e.
by ~24k lines of unverified Rust. Nothing on the Lean side checks it. The check
converts this from an invariant we maintain into a fact the kernel-adjacent machinery
verifies per theorem, per run.

Bug classes it catches:

| # | Class | Example |
|---|---|---|
| 1 | **Smuggled `sorry`** | any tactic/codegen path that produces `sorryAx` without tripping a closer's `fail` rung |
| 2 | **Undeclared dependency axiom** | dep walk emits an axiom the verification set never discharges (the family of bugs behind the tuple/`pair` regression, caught there only because the *reference* was dangling; here we catch it even when the reference resolves) |
| 3 | **Prelude drift** | someone adds an `axiom` to `TactusPrelude.lean` and nothing downstream notices the TCB grew |
| 4 | **Hidden tactic-level TCB extensions** | `native_decide`-style tactics add `Lean.ofReduceBool` / `Lean.trustCompiler` to the closure, silently extending trust to the Lean *compiler*. **This is live today**: `tactus_bit_vector`'s `bv_decide` rungs are expected to pull in `Lean.ofReduceBool` (its LRAT check runs compiled). See §4 policy knob. |
| 5 | **Stale/wrong expected list** | generator believes fn F depends on {A, B} but the proof actually uses axiom C from an import — surfaces dep-walk imprecision even when sound |

### What it deliberately does NOT catch (honesty section)

- **Cross-file circular axiomatization** (island mode): F's file axiomatizes G's
  ensures while G's file axiomatizes F's. Each file's closure is locally fine; the
  unsoundness is in the composition. Until package mode, acyclicity remains
  `dep_order`'s (Rust-side, trusted) job. Package mode closes this by construction —
  a Lean package cannot have circular imports/theorem references.
- **Axiom-statement vs. discharged-theorem mismatch across files**: G's ensures-axiom
  in F's file has the right *name* in the closure but a wrong *statement* (drifted
  specialization, `impl_subst` bug). Name-closure checking can't see this. The fix is
  the package-mode gate (callee referenced as a theorem — statements are then the
  *same term*), or an interim statement-hash cross-check between the axiom emitted in
  F's file and the theorem statement in G's file.
- **Unfaithful encoding**: if the WP/goal itself doesn't mean what the Verus source
  means, a clean axiom closure proves the wrong thing perfectly. That's the
  tactus-core / verified-WP arc (separate design, forthcoming).
- **Lean elaborator/kernel bugs**: out of scope. The kernel independently rechecks
  elaborator output, so the elaborator is already not fully trusted; kernel bugs are
  where external checkers (lean4lean) would slot in — assessed as not worth the
  integration cost for now. If we ever hit an elaboration soundness bug, the right
  move is an upstream report + minimized repro, not a permanent second checker.

---

## 2. Mechanism

### 2.1 The prelude command

Sketch (exact API names to be confirmed against v4.25.0 at implementation time;
`#print axioms` is implemented via `Lean.collectAxioms` in
`Lean.Util.CollectAxioms`):

```lean
open Lean Elab Command in
elab "#tactus_check_axioms" thm:ident "[" expected:ident,* "]" : command => do
  let env ← getEnv
  let axioms ← liftCoreM <| collectAxioms thm.getId
  let core : NameSet := .ofList [``propext, ``Classical.choice, ``Quot.sound]
  let prelude : NameSet := .ofList [`arch_word_bits, `arch_word_bits_valid,
    `Tactus.heightLt, `Tactus.index, `Tactus.hasResolved]
  let allowed := expected.getElems.foldl (init := core.union prelude)
    fun s e => s.insert e.getId
  for ax in axioms do
    if ax == ``sorryAx then
      throwError "tactus: proof of {thm.getId} contains sorry"
    unless allowed.contains ax do
      throwError "tactus: proof of {thm.getId} rests on undeclared axiom {ax}"
```

Notes:

- **Subset, not equality.** The soundness check is `closure ⊆ allowed`. A proof that
  doesn't *use* a declared dependency axiom is fine (and common — the WP may discharge
  without it). Optionally emit an `info` for expected-but-unused axioms as a dep-walk
  precision signal, but never fail on it.
- **Failure is an ordinary elaboration error** at the check command's span, so it
  flows through the existing error-reporting path (sourcemap points it at the fn).
  The message names the offending axiom — directly actionable.
- The prelude elaborates with Mathlib available (`setup-mathlib.sh`), so the
  `Lean.Elab.Command` machinery is importable. If the prelude's import footprint is
  a concern, the command can live in a separate always-imported `TactusCheck.lean`.

### 2.2 The generator side

- New `lean_ast::Command::CheckAxioms { thm: LeanName, expected: Vec<LeanName> }`,
  pretty-printed by `lean_pp`.
- Emission site: `generate.rs`, immediately after each theorem command (per-fn island
  files today; per-module files in package mode later).
- `expected` = **exactly the `axiom` commands the generator placed in this file**
  (callee ensures, broadcast-lemma axioms, cross-crate lemma axioms, external-body
  `Inhabited` axioms). No new analysis needed — the generator constructs these
  commands itself; it just records their names as it goes. Transparency beats
  cleverness here: an explicit, diffable list in the `.lean` artifact over an
  implicit "whatever this file declared" rule.
- `sanity.rs` extension: check every `CheckAxioms.expected` name is actually declared
  by an earlier `Command` in the file (keeps the two checks honest with each other).

### 2.3 Where it runs

Every routed-to-Lean verification, unconditionally. No opt-out flag — the check is
cheap and an escape hatch would defeat the point. (A debug-only env var for tactus
developers bisecting the checker itself is acceptable.)

---

## 3. Policy: the allowed core set

| Axiom | Status | Rationale |
|---|---|---|
| `propext`, `Classical.choice`, `Quot.sound` | **allowed** | Lean's classical base; Mathlib rests on these; `Classical.epsilon` (our `choose`) needs `choice` |
| prelude 5 (`arch_word_bits`, `arch_word_bits_valid`, `Tactus.heightLt`, `Tactus.index`, `Tactus.hasResolved`) | **allowed, shrink over time** | see §4 hygiene |
| per-file dependency axioms | **allowed iff listed in `expected`** | island-mode modularity; disappears in package mode |
| `sorryAx` | **hard error** | never legitimate in emitted output |
| `Lean.ofReduceBool` / `Lean.trustCompiler` | **policy knob — see below** | extends TCB to the Lean compiler + native execution |

**The `ofReduceBool` decision.** `bv_decide` (used by `tactus_bit_vector`) checks a
SAT solver's LRAT certificate with a *verified* checker — but executes it *compiled*,
which is what `ofReduceBool` licenses. Options:

1. **Allow globally** — simplest; TCB includes Lean's compiler for bitvector fns.
2. **Allow per-theorem, tracked** *(recommended)* — the generator whitelists it only
   for fns whose emitted tactic block contains a `tactus_bit_vector` rung, and the
   check makes every such fn identifiable. We then *know* the exact set of theorems
   resting on compiled execution, and can revisit if it grows.
3. **Disallow** — lose `bv_decide`, fall back to `decide`/`simp` rungs only;
   probably kills bitvector-heavy fns' automation.

Recommendation: (2). It costs one boolean plumbed from tactic-selection to the
emission site, and converts an invisible trust extension into an inventoried one.

---

## 4. Companion hardening (same arc, each cheap)

1. **`sanity.rs` always-on.** Currently `debug_assertions`-gated. It's an AST walk —
   negligible against a Lean elaboration. Promote to release builds; keep the
   panic-vs-error decision consistent with other codegen invariant violations.
2. **Prelude axiom hygiene.** Investigate definitionalizing:
   - `Tactus.index` — plausibly `def` via bounds-check + `Classical.arbitrary`
     fallback (the `[Nonempty α]` binder is already there);
   - `Tactus.hasResolved` — if no emitted facts constrain it beyond existence, an
     `opaque` def of an unspecified `Prop` family is conservative over the kernel in
     a way an `axiom` is not (any interpretation works ⇒ no consistency risk);
   - `Tactus.heightLt` — audit what's assumed *about* it (well-foundedness for
     `decreasing_by`?); those companion facts, if any, are the real trust, not the
     symbol.
   Each one removed shrinks the §3 table. `arch_word_bits` (+ validity) is the one
   pair that's *honestly* an axiom — platform width is a genuine assumption.
3. **CI grep belt-and-suspenders:** no literal `sorry`/`admit` tokens in emitted
   `.lean` files. Subsumed semantically by the `sorryAx` check but costs one line.

---

## 5. Package-mode forward compatibility

This design is unchanged by the move from per-fn islands to whole-crate packages —
only the `expected` lists shrink. End state per crate:

```lean
-- generated, one per crate package
#tactus_check_axioms_crate [
  -- every theorem in the package, closure ⊆ core ∪ prelude ∪ {ofReduceBool where inventoried}
]
```

i.e. the crate gate's soundness claim becomes a single machine-checked line:
**"every theorem in this package elaborates with axiom closure inside the declared
TCB."** Dependency axioms are gone (callees are theorems), circularity is impossible
(import graph), statement mismatch is impossible (same term). The island-mode check
is the same command with a longer allowed list — nothing is thrown away.

---

## 6. Implementation plan

| Brick | Content | Size |
|---|---|---|
| B1 | `Command::CheckAxioms` in `lean_ast.rs` + `lean_pp.rs` rendering | small |
| B2 | `#tactus_check_axioms` elab command in `TactusPrelude.lean` (+ confirm `collectAxioms` API on v4.25.0) | ~30 lines Lean |
| B3 | Emission in `generate.rs` after each theorem; record axiom names as they're emitted | small |
| B4 | `ofReduceBool` plumbing: whitelist entry iff the fn's tactic block includes a `bv_decide`-bearing rung | small |
| B5 | Tests: golden output; fixture with a smuggled undeclared axiom (must fail); fixture with a `sorry` (must fail); bitvector fn (must pass with knob, fail without) | medium |
| B6 | `sanity.rs`: release-mode enable + expected-list cross-check | small |
| B7 | Measure wall-clock delta on the tactus-group-theory gate (expect noise) | trivial |

Independent bricks: B2 ∥ (B1→B3→B4). B5 last. §4.2 prelude hygiene is a separate
follow-up arc, not gating.
