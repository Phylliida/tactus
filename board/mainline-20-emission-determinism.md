---
title: "emission determinism: observed flips were binary swaps; latent hash-order hazards fixed by construction"
status: in-review
claimed_by: claude (e2e-speed branch, c169674)
created: 2026-07-17T16:45:00Z
updated: 2026-07-17T16:45:00Z
---

## The walk-back (what the mainline-19 side-finding actually was)

All three OBSERVED emission flips from the mainline-19 investigation
trace to cross-session binary swaps, not in-binary nondeterminism: the
shared main checkout's `target-verus/release/rust_verify` was being
rebuilt by parallel dev sessions mid-probe. Evidence:

- The captured good/variant trees differ in the `.ladder` FINGERPRINT
  field — `ladder_fingerprint()` hashes the verus exe's mtime+size, so
  a differing fp is a direct signature of "different binary".
- The variant's closer text is the pre-52dc41a shape
  (`first | rfl` without `with_reducible`) — an older build's output.
- The original let-vs-hoist flip (with the `.deref` slot bug) happened
  during the very window the Return→Wp::Let work was being developed
  and rebuilt in that checkout; the bug it exhibited is the one
  52dc41a fixed.

With a PINNED binary, emission is byte-stable: 25/25 identical hashes
per probe (Box-ctor, tuple, vec-index shapes), 3/3 identical full-tree
hashes on tactus-core (141/0 each time).

Methodology lesson (now also in memory): never use the live main
checkout's binary as a fixed baseline — copy it or use a worktree build
no other session touches.

## What IS real, and fixed (commit c169674)

Hash-order iteration reaching output order is a genuine hazard class —
std HashMap/HashSet iteration order varies per process (RandomState) —
it just wasn't what we observed. Sweep of lean_verify found and fixed
the sites where iteration order could reach emitted bytes:

- **dep_order**: Tarjan neighbor lists (fn graph AND datatype graph)
  were `HashSet` — DFS follows neighbor order, so SCC output order
  (= defs item order) depended on set iteration. Now `Vec` in
  deterministic AST-walk order, deduped at insertion. Worklist seeding
  iterates the fn slice, not the map.
- **generate wf-synth cluster**: `scalar_carrying` (HashSet),
  `spec_fn_x` / `pending` / `wf_def_texts` (HashMaps) were iterated
  where order reaches synthesized-lemma and wf-def emission order.
  Now key-sorted at the iteration points (types unchanged — consumers
  share `&HashMap` refs through wf_synth/link_discharge structs).

Sites audited and left alone (order provably can't reach output):
fixpoint loops (converge to the same set), contains-only sets, keyed
lookups, Link's `visit` (outer loop over a deterministic slice, deps
values already `Vec`), reach/`bwd` set computations, the
referenced-datatypes filter (final collect preserves krate order),
indeg/dependents in the topo pass (decrements commute; selection scans
by index).

Beyond hygiene, the payoff is warm-tree stability on big crates: wf/
defs order flapping would show up as spurious content diffs → M5e
"changed" → warm rebuild churn (and possibly the mixed-generation
false-red pattern). Order is now pinned by construction.

## Validation

- Pinned-binary hammer: 25/25 per probe, 3/3 tactus-core (fbc2aff3…),
  141/0 each rep, on the branch synced to main @ eca810f.
- e2e suite via vargo: see branch record (target: match main's 550/1).
