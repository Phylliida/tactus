---
title: "Bootstrap foundation LANDED (W0 / W1.5 / N2 / gate removal) — context anchor"
status: done
claimed_by: fable
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Anchor entry: what's already done before the `bootstrap-01…13` queue starts, so
the board isn't a blank slate. Not a task — a checkpoint. Full history in
`DESIGN-bootstrap.md` §11–12 and the git log on the `bootstrap` branch.

## Writeup

Landed on the `bootstrap` branch (2026-07-11 → 12):

- **W0 probes** (`probe-w0/`, P1–P8b): both bridge mechanics validated on toy +
  two real tgt goals; the WF-spec-fn kernel-inertness constraint found with the
  `termination_by structural` mitigation confirmed.
- **W1.5**: `#[verifier::structural_decreases]` — opt-in emitter brick; bare
  datatype-param measures emit `termination_by structural` (kernel-computable,
  empty axiom closure); silent WF fallback otherwise.
- **Four latent emitter bugs + one soundness hole found & fixed**, each with a
  pinning e2e test: (1) match-arm pattern binders dropped `.deref`; (2) Decl-let
  Box binders same; (3) VIR-AST ctor-arg `Box::new` erasure missed `.mk`;
  (4) SST ctor-arg same on exec obligations; (5) `sorry` was warning-only on
  exec-only crates (no Link gate) — now fatal on every per-fn path.
- **Defs size gate removed** (predictability) — exposed and fixed 5 gaps the
  gate had hidden.
- **N2**: `tactus-core/lib.rs` mirror types live under the package gate (6/0),
  with the vir-growth tripwire test.
- **Merges**: emit-module (M6: package-check is the default) + main fully
  merged into `bootstrap`.
- **Specs written**: `DESIGN-N3-serializer.md`, `DESIGN-W2-refwp.md`,
  `VERIFICATION-PATH.md`; plan reviewed (2 defects fixed: CtxFrame must be a
  single ordered list; generics added to the contract).

Battery at this checkpoint: e2e 549/0, lean_verify units 301+7/0, tactus-core
6/0, w15_probe 7/0.

Next actionable: `bootstrap-01` (N2.1 mirror amendments).
