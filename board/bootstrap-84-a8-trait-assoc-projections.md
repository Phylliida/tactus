# bootstrap-84 — A8: trait associated-type / instance-projection coverage arm

Status: **CARDED 2026-08-06 (b83 D6) — step-0 evidence frozen; DESIGN
NOT PROPOSED (needs its own card-time subject matrix + design review).
NOT STARTED.** This is the blocker standing between today and
vstd-as-package proper (DESIGN-emit-module.md M6: theorem-ize vstd's
lemma layer so consumer Boundaries genuinely shrink to imports).
Sequencing per Danielle 2026-08-06: after b83 (the explicit Boundary
artifact) lands; this arm is milestone-A-shaped, not F-shaped.

## Why this arm exists (from b83's step-0 probe)

The b83 probe ran vstd itself through the lean-backend emit (vstd_build
flag set — recorded below, was non-obvious), scoped to `seq_lib`:

```
verus --internal-test-mode \
  --extern verus_builtin=<tp>/libverus_builtin.rlib \
  --extern verus_builtin_macros=<tp>/libverus_builtin_macros.so \
  --extern verus_state_machines_macros=<tp>/libverus_state_machines_macros.so \
  --crate-type=lib --multiple-errors 2 --is-vstd \
  --cfg feature="std" --cfg feature="alloc" \
  --lean-backend --emit-lean --verify-module seq_lib source/vstd/vstd.rs
```

Result: **140 errors, ALL ONE CLASS** — "Tactus codegen produced
unresolved references":

```
in `vstd.contrib.exec_spec.seq.ExecSpecSeqSubrange`: unresolved `V`
in `vstd.contrib.exec_spec.ToOwned`: unresolved `V`
in `vstd.contrib.exec_spec.ExecSpecIndex`: unresolved `V`
in `vstd.std_specs.convert.TryFromSpec`: unresolved `Error`
in `instance`: unresolved `(Self := (A))`
in `instance`: unresolved `(Self := (T))`
in `instance`: unresolved `USize`
```

i.e. trait associated-type projections and instance Self-projections
in defs/instance emission are unrendered today. The census itself runs
fine over vstd (151/820 certified in the scoped emit; tags:
branch-forced-state-join ×5, rawvir-arrayliteral ×5,
rawvir-call-arity ×3, rawvir-withtriggers ×2,
branch-forced-state-leak ×1, emit-counter-drift ×1, rawvir-binaryopr,
rawvir-readplace-nonlocal) — the blocker is codegen-level (the defs
layer), not the cert/bridge layer.

## The payoff this unlocks

b83's inventory (E2 of its card): tgt's consumer surface carries ~16
vstd-PROVED lemmas re-stipulated as axioms (8 `div_mod`, 5 `seq_lib`,
`set_lib`, `array`, `vec_clone_deep_view_proof`); `seq_lib.rs` alone
has 175 proof fns. With this arm landed, a vstd package proves them
once and every consumer's Boundary loses them — the
`proved-upstream` count in b83's gate note is exactly the diff metric
(this arm's acceptance: the note's P count drops to 0 on the
subject corpus; the inventory entries LEAVE the artifact).

## Notes for the card-time work (when picked up)

- Subject matrix over production-behavior dimensions (b81
  retrospective change 1): dimensions suggested by the probe —
  {assoc-type in trait def, assoc-type in impl, Self-projection in
  instance, concrete assoc binding (`(Self := (A))`)} × {same-crate,
  cross-crate(vstd)}.
- The `emit-counter-drift: production theorem ids [1..6] != replayed
  predictions [1..5]` line in the probe output is a SECOND, independent
  finding worth its own look at card time (may or may not be
  trait-projection fallout).
- vstd does not compile standalone with plain `verus vstd.rs` — the
  vstd_build flag set above is required (feature cfgs + `--is-vstd` +
  the three `--extern`s).
- No full tgt/vstd gates (Danielle's standing constraint) — scoped
  `--verify-module` emits are the accepted lane.
