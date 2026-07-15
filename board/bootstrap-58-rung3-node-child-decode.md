---
title: "W5f v2 (follow-on to bootstrap-57 rung 3) — full injective Node-child DECODE for the fixlib.Tree encoding (the deferred hard kernel; gated on the census)"
status: todo
claimed_by:
created: 2026-07-14T22:45:00Z
updated: 2026-07-14T22:45:00Z
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

## Writeup

_(fill in when done or when re-confirmed as parked)_
