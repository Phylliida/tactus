---
title: "machine_group `let lib` shadow rename — recover 2 proof fns (XS)"
status: done
claimed_by: fable
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T18:45:00Z
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

## Progress

- (2026-07-16) All 8 bare-`lib` occurrences renamed to `lib_w` (2 lets + 6 uses,
  the two lemmas only — grep-verified no other sites). Gate green: 2045
  verified + 2162 cached, 0 errors (tgt `ca1caec`).
- (2026-07-16) Fresh `--lean-all-proofs --emit-lean` full-crate run: 2953/0
  verus-side, both artifacts NOW EMIT (`machine_group__lemma_{x,y}_past_config_inv.lean`,
  `let lib_w :=` alongside `lib.*` crate refs — shadow gone). Previously they
  were codegen-rejected (reserved-binder).

## Writeup

Rename done and committed; both fns recovered from the codegen-rejection class.

**Deviation from done-when:** the ELABORATION spot-check is blocked crate-wide
on main, not by these fns: per-fn artifacts emit `import TactusDefs_lib_exec`,
and the defs module doesn't build on main (deepview Ref mismatch +
Option.Some_val0 — bootstrap-40/41, fixed on bootstrap branch, pending
bootstrap-72 sync). Elaborate after the sync, or census tooling works around.

**Bug finding (emit/live divergence):** the tgt target's `.ladder` sidecars
record FAILED, and a live run correctly falls back to standalone islands — but
`--emit-lean` (no lake) still emits optimistic defs imports. Emit-only
artifacts therefore diverge from what a live run elaborates whenever the defs
ladder fails. Small, real; affects any artifact-harvesting tooling (census!)
on a tree with failing defs. Consider: emit-only should honor a
fingerprint-valid FAILED record (or re-derive the live decision) so emitted
artifacts are self-contained standalone in that case.
