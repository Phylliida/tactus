---
title: "machine_group `let lib` shadow rename — recover 2 proof fns (XS)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

`tactus-group-theory/src/machine_group.rs` (~lines 8055/8091,
`lemma_x_past_config_inv` / `lemma_y_past_config_inv`): `let lib = ...` shadows
the crate namespace under Option B naming (full dotted names at root — `lib.` is
the crate prefix in tactic texts). Pre-existing failure in the lean-all-proofs
failing set; now a CLEAR codegen diagnostic via the unconditional sanity checks
(reserved-binder rule). Trivial rename `lib` → `lib_w` recovers both fns.

Found during S1 preservation testing; surfaced to Danielle then, deferred, now
queued.

**Done when:** both fns' artifacts elaborate on the `--lean-all-proofs` path
(spot-check the two files, or re-run the per-file diff for that module); crate
still verifies clean on the normal gate.

**Blocked by:** nothing.
