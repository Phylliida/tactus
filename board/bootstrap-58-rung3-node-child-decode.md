---
title: "W5f v2 (follow-on to bootstrap-57 rung 3) — full injective Node-child DECODE for the fixlib.Tree encoding (the deferred hard kernel; gated on the census)"
status: done
claimed_by: opus-bootstrap58-feasibility
created: 2026-07-14T22:45:00Z
updated: 2026-07-14T23:55:00Z
---

## Description

Spun out of **bootstrap-57 rung 3** (DONE). That rung grounded `ctorTag`/`ctorField`
to a real parity encoding of the real `fixlib.Tree`, tying the flat-Int `Match`
evaluation to the REAL `fixlib.tree_head` for ALL trees — see
`probe-w0/probe30_w5f_ground/ground.lean` (`embTree`, `ctorTag_leaf`/`ctorTag_node`/
`ctorField_leaf`, `ground_match_{leaf_val,node_val,leaf_prop}`).

**What rung 3 deliberately did NOT do:** decode Node CHILDREN. `tree_head` returns `0`
for every `Node` regardless of children, so its faithful grounding needs only the Node
**tag (parity)**, not the two child sub-embeddings. The encoding
`embTree (Node l r) = 2·(embTree l.deref + embTree r.deref)+1` recurses through the
children (a genuine whole-tree fold) but is **not proven injective on Node**, and
`ctorField (embTree (Node l r)) i` is NOT proven to recover `embTree l`/`embTree r`.

**This task = the genuine remaining hard kernel:** make `embTree` a full injective
encoding and prove `ctorField (embTree (Node l r)) 0 = embTree l.deref`,
`… 1 = embTree r.deref`, so a Match whose Node arm INSPECTS its children (not just
`tree_head`) grounds faithfully.

**Why it's hard (recon):** a faithful two-child decode needs an invertible **unbounded
pairing** for `(embTree l, embTree r)` — Cantor (needs a triangular sqrt) / 2-adic
(needs a valuation) are OUTSIDE `omega`'s Presburger fragment, and there is no Mathlib
in the probe (only a small prelude). A fixed base-2^64 (like rung 2's `Point`) fails at
tree depth > 1 because child embeddings blow past the base. So this needs either (a) a
short from-scratch injective-pairing lemma proven by structural induction, or (b) a
recursive `decodeTree : Int → fixlib.Tree` with fuel/height + a round-trip proof — i.e.
re-deriving a Gödel-style decode. Neither is a one-`omega` discharge.

**Gate (per Danielle's steer + the card):** do this **only if the bootstrap-56 census
ever finds a live direct-Match-in-goal that INSPECTS Node children.** Today that census
is zero and bodies are fn-pinned, so this is low priority — but it's tracked here so the
deferral is visible rather than buried in bootstrap-57's done writeup.

**Done when:** `probe30` (or a successor) proves `ctorField (embTree (Node l r)) 0 =
embTree l.deref` and `… 1 = embTree r.deref` over standard axioms only (no
Classical.choice, no sorryAx), and a grounded fact denotes a Node-child-reading Match to
the corresponding real emitted fn — OR the census is re-confirmed empty and this stays
parked with that note.

## Progress

- (2026-07-14) Created as the tracked deferral from bootstrap-57 rung 3. Not started.
  Entry point: `probe-w0/probe30_w5f_ground/ground.lean` (the `embTree` block + the
  RUNG 3 section). First step before any Lean: re-run the bootstrap-56 census to confirm
  whether a live Node-child-inspecting Match-in-goal exists — if not, park with that note.

- (2026-07-14, opus-bootstrap58-feasibility) **Census re-run (the gate) + feasibility
  probe landed → PARKED per path (b), with the hard core de-risked.**

  **CENSUS (definitive, full fixture + tgt cert slice).** Grepped every emitted
  `.lean` for `MatchR`/`ExprData.Match`, then bucketed the cert files by extension:
  - **Zero `.cert.lean` (OBLIGATION goal) files contain `MatchR`.** Every one of the
    12 MatchR-carrying certs is a `.defcert.lean` (a spec-fn **body**, reached through
    the pinned `E.fn` oracle) — `tree_head`, `symbol_ord`, `step_position`,
    `symbol_to_column`, `generator_index`, `letter_digit`, `relabel_symbol`,
    `apply_embedding_symbol`, `runtime_symbol_valid_for_hom`, `asym`. **No
    `GoalData.LeafE` holds a `Match`.**
  - The only `Tree`/`tree_head` match on the slice returns `0` for `Node` (child-
    **blind**); `grep 'Tree.Node'` over the cert slice with a reading arm body =
    empty. So there is **no live Node-child-inspecting `Match` anywhere** — not in a
    goal, not even in a body.
  ⇒ bootstrap-58's gating condition is empty. Per the card's own "Done when" path
  (b), this **parks** (bodies are fn-pinned; the fn oracle handles their matches —
  `eval` never interprets a Node-child read).

  **Feasibility probe (the value added beyond the park).** The card left ONE genuinely
  open question: is the required invertible **unbounded** pairing even achievable here,
  given "Cantor needs a sqrt / 2-adic needs a valuation — both outside omega's
  Presburger fragment, no Mathlib in the probe"? **Answer: yes.** Landed
  `probe-w0/probe31_pairing/pairing.lean` (bare Nix lean 4.25, no imports, ~1.6 s,
  `./run.sh`): a **fuel-structural bit-interleaving** pairing `pair`/`unfst`/`unsnd`
  with `unfst_pair`, `unsnd_pair`, `pair_injective`, and the Int→Nat zig-zag
  `unzz_zz` — **all `[propext, Quot.sound]`, no `sorryAx`, no `Classical.choice`, no
  Mathlib.** Bit-interleaving sidesteps Cantor/2-adic entirely: each step is `%2`/`/2`/
  `/4` (inside omega), the recursion is on explicit fuel (no wf proof), and the only
  non-omega fact is `2^(f+1)=2^f·2` (`Nat.pow_succ`, core). See
  `probe-w0/probe31_pairing/REPORT.md` for the exact plug-in shape
  (`embTree (Node l r) := 2·pair F (zz (embTree l)) (zz (embTree r))+1`) and the
  remaining integration steps.

## Writeup

**Status: PARKED (per "Done when" path b — census re-confirmed empty), with the
deferred hard kernel's mathematical core now de-risked and proven feasible.**

Two things happened this turn, kept scrupulously distinct:

1. **The gate is resolved.** A full-slice census (fixture + tgt) confirms **zero
   `Match` directly in an obligation goal**, and **no Node-child-inspecting `Match`
   anywhere** (the sole `tree_head` match is Node-blind, returning 0). So the card's
   trigger for building the full decode has not fired, and — per its own design —
   this parks rather than being built. Bodies containing matches are handled by the
   `E.fn`/`E.fnN` oracle pin (bootstrap-57 rung 1), not by `eval` decoding the
   scrutinee, so nothing is un-grounded by this deferral.

2. **The feared obstacle is gone.** The card's recon worried the required invertible
   unbounded pairing was out of reach without Mathlib/sqrt. `probe31` disproves that
   with a self-contained, kernel-checked bit-interleaving pairing (round-trips +
   injectivity + Int seam, standard axioms only). A future instance with a live
   Node-child obligation now builds on a **proven** pairing foundation instead of an
   open problem.

**What is NOT done (honest):** the full deliverable in the title — a pairing-based
injective `embTree`, re-grounded `ctorField`/`ctorTag`, and a grounded fact denoting a
Node-child-reading `Match` to a real emitted fn — is **not** implemented. Only its
hard core (the pairing) is. The remaining work is integration engineering (fuel
discipline for `embTree`; re-do the rung-3 grounding on the new encoding; a fixture fn
that actually reads Node children; a few `Int.toNat` bridging lemmas at the pairing
boundary), enumerated in `probe31/REPORT.md §"What is still deferred"`. It stays gated
on the census. If a Node-child `Match`-in-goal ever appears, **re-open this card** (or
spin a successor) and start from `probe31` + `probe30`'s rung-3 block.

**Assumptions:** the census reflects the current emitted `.lean` slice on disk
(fixture `bootstrap-fixture/out`, tgt `probe20_w7_tgtslice/out`, tactus-core `out`,
`target/tactus-lean`); if new tgt fns with child-reading enum matches get emitted
later, re-run the `MatchR`-in-`.cert.lean` scan before trusting this park.
