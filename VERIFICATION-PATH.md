# The path to a verified tactus — orientation

**Date:** 2026-07-12. **Audience:** anyone (including future us) who wants the
whole arc in one read before descending into the detailed specs.
**Detail lives in:** `DESIGN-bootstrap.md` (master plan, trust inventory,
W-ladder), `DESIGN-N3-serializer.md`, `DESIGN-W2-refwp.md`, and the component
docs they reference. This doc states WHERE the program goes, WHAT can honestly
be claimed at each milestone, and what can never be claimed.

---

## 1. The end-state claim, stated honestly

"Verify tactus" cannot mean tactus proves itself correct (Gödel), and cannot
mean the whole toolchain is verified (nobody verifies rustc). What it CAN
mean — the de Bruijn criterion, pushed to its limit:

> Every claim tactus makes is checkable by a small independent checker (the
> Lean kernel) from self-contained artifacts, with every trust extension
> inventoried per run. The 25k-line emitter, the tactic automation, and
> tactus's own proof search all drop out of the trusted base. What remains
> trusted is: the Lean kernel, a definitions-only prelude plus one honest
> platform axiom pair, a ~1k-line SST serializer, the shared Verus frontend
> (rustc → HIR → VIR → SST), and the adequacy of one written-down operational
> semantics.

Everything in this program is a step that moves an item from "trusted" to
"checked" in that sentence, or makes the trusted remainder smaller and more
readable.

## 2. Why the battle is about statements

A verification toolchain can fail you in two ways: accept a bad *proof*, or
prove the wrong *statement*.

* **Proofs are already un-trusted.** Tactic text goes to Lean's elaborator
  and the kernel re-checks the result. A bug in tactus's automation can waste
  time; it cannot certify a falsehood — the kernel would reject it.
* **Statements are the entire remaining exposure.** If the emitted goal does
  not mean what the `.rs` source means, a clean kernel verdict is worthless.
  Today the goal text is produced by ~25k lines of unverified Rust. Silent
  mis-rendering IS the threat model — not hypothetically: this program found
  four latent statement-rendering bugs and one soundness hole in its first
  two days of probing, all in code the test suite passed.

Hence the strategy: keep proofs kernel-checked (done by construction), then
make statements *certified* rather than trusted (the R2 arc), then shrink and
harden what's left.

## 3. The arcs, and how they compose

Five arcs, largely independent, composing into the §1 claim:

| Arc | One-line job | State |
|---|---|---|
| **R0a** lean-only routing | no Z3 hybrid: every obligation goes to Lean | in progress (Danielle) |
| **R0b** axiom closure | per-theorem `#tactus_check_axioms`: closure ⊆ core ∪ prelude, sorryAx fatal | landed (Link gate) |
| **R1** package emission | one shared defs world, kernel-checked composition; same-crate axiomatization structurally impossible | landed (M6: package-check is the default) |
| **T** transparent automation | proof search out of artifacts; what's checked is what's written | brick 1 measured; squeeze-and-pin path chosen |
| **R2** statement certificates | the emitter's goals kernel-checked against an independent reference computation | THIS program's heart: W0 ✓, W1.5 ✓, N2 ✓, N3–W3 spec'd |

R2's mechanism, in one paragraph: the emitter additionally snapshots each
fn's SST as a Lean data literal (the **serializer** — the one new trusted
piece, deliberately boring and small). A **reference WP**, authored as tactus
spec fns over mirror datatypes and emitted as ordinary kernel-computable Lean
definitions, recomputes the obligations from that literal. Per fn, per run,
the kernel `decide`s that the production goals equal the reference's. The
emitter is then no longer trusted for statement structure — a disagreement
anywhere fails loudly. Staging: structure first with opaque expression leaves
(stage A), expression rendering folded in later (stage B), and finally the
reference itself *proven sound* against an operational semantics of SST, with
that proof also kernel-checked (W5) — closing the loop without circularity,
because the fixed point is checked by the kernel, not by tactus.

## 4. The claim ladder

What a skeptic can verify after each milestone — each line strictly extends
the previous:

1. **Today** (R0b + R1 + W1.5 + N2 landed): every accepted proof is
   kernel-re-checked from self-contained per-crate packages; composition and
   axiom closures are kernel-verified per run; a user-written `sorry` is
   fatal on every path. *Trusted: all statement rendering.*
2. **After N3 + W2 (stage-A certificate, fixture-scale):** obligation
   STRUCTURE — binder telescopes, hypothesis sets and order, let-chains,
   obligation multiplicity — is kernel-checked to equal an independent
   recomputation from the serialized SST. *Trusted: leaf (expression/type)
   rendering, the serializer, the frontend.*
3. **After W3 (differential gate over tgt):** the same certificate holds
   across a ~3k-fn real corpus, with every historical divergence triaged and
   pinned. This is also the program's bug-finding payoff, independent of any
   proof — the gate catches statement-assembly regressions forever after.
4. **After W6 (stage B, deep expressions):** leaves become mirrored data;
   expression and type rendering join the certificate. *Trusted: the
   serializer (now including leaf serialization), the frontend.*
5. **After W5 (soundness loop):** the reference WP is no longer just an
   independent implementation — it is PROVEN sound against a written-down
   operational semantics of SST (fuel big-step, partial correctness first),
   the proof authored in tactus and kernel-checked like everything else.
   The claim becomes: *kernel-checked obligations ⟹ the operational spec.*
6. **After W7/W8 (defs layer + authority flip):** the spec-world definitions
   join the certificate and the package verdict becomes the verdict. The §1
   end-state claim holds in full.

## 5. The permanent residue — what we will still be trusting at the end

Stated up front so nobody discovers it later:

* **The Lean kernel** (and hardware/OS beneath it). lean4lean
  cross-checking was considered and ruled out (elaborator-bug reports go
  upstream instead). This is the standard floor of the entire field.
* **The serializer** (~1k lines, one file, faithfulness-contract
  doc-comment, golden-file tested). Read it; that's the point of its size.
* **The frontend**: rustc + the Verus HIR→VIR→SST lowering, shared with
  upstream Verus. Mitigation, not elimination: the snapshot point is LATE
  (post all Verus transforms), so everything after the snapshot is
  certified; everything before is shared, heavily-exercised infrastructure.
* **Spec adequacy**: that the written SstSem is the semantics you meant, and
  that the mirror types mean what the SST means (W5f documents this
  judgment; math can't discharge it).
* **The platform axiom pair** (`arch_word_bits` etc.): honest, explicit,
  two lines.

## 6. Failure modes the design guards against (and how)

* *Certificate green but meaningless* → mutation-kill acceptance: perturbed
  certificates must flip the verdict (W2 §2.4).
* *Reference drifts toward the implementation* (monoculture) → the reference
  is structural/first-order by construction, reviewed as spec, and W5's
  soundness proof re-anchors it to an independent semantics.
* *Silent scope shrinkage* ("it passes because it skips") → fail-loud
  serializer with per-crate `certified M/N` reporting; the vir-growth
  tripwire breaks the build when SST gains variants; census tables in docs.
* *Heuristics silently switching pipelines* → none remain (the defs size
  gate removal, 2026-07-12, is the precedent and the policy).
* *Trust extensions sneaking in* → R0b's per-theorem axiom closure + T's
  automation transparency; both per-run facts, not one-time audits.

## 7. Current position (2026-07-12)

Done: W0 probes (8), W1.5 structural emission, four emitter bugs + one
soundness hole found and fixed with pinning tests, emit-module + main fully
merged (package-check default), N2 mirror types live under the package gate,
N3/N2.1/N4/W2/W3 spec'd with open-question ledgers. Battery: 549/0 e2e,
301+7 units, tactus-core 6/0, w15_probe 7/0.

Next: N2.1 (mirror amendments) → N3a (serializer core) — see
`DESIGN-W2-refwp.md` §6 for the full sequence.

The program's early empirical lesson, worth repeating: **every layer of
independent checking added so far has found real defects the previous layers
missed** — probes found renderer bugs the suite passed; gate removal found a
soundness hole the design docs called handled. The certificate isn't
paranoia; it's the same lesson, institutionalized.
