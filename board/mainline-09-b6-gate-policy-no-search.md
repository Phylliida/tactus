---
title: "B6 — gate policy: no-search artifacts asserted at the gate"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

The end-state one-line gate claim, next to the axiom-closure one: **"no artifact
imports the search module / contains a search tactic."** Gate crates
(tactus-group-theory, tactus-computability-theory, tutorial) run with derivation
+ inline proofs only; discover-mode ladder is dev-UX exclusively.

Under the derivation-first shape (mainline-04's primary candidate) there is no
"strict replay" mode to build — the gate property is simply that derived tactics
+ inline proofs close everything, asserted by (a) artifacts importing TactusDefs
only and (b) a text-level check that no T2 tactic name appears in emitted
artifacts. If mainline-04 chose a store instead, this task becomes the strict
replay mode of the original §3.1 (pin miss = hard error).

Spec: `DESIGN-transparent-automation.md` §5 (last bullet) + §9 B6.

**Done when:** gate crates' check.sh asserts the no-search claim and passes;
the claim's exact wording documented in the design doc.

**Blocked by:** mainline-05, mainline-08.
