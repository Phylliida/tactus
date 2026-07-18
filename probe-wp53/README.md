# probe-wp53: tactus-core's 48-second obligation

`wp53_repro.lean` is ONE theorem extracted verbatim from the emitted
`pkg/lib__wp_stm_sound.lean` (tactus-core, `--lean-all-proofs`): the
postcondition obligation at lib.rs:3687 case 53. It elaborates in ~48s
standalone — the other 17 obligations in the module are 0.8-2.3s each,
so this single theorem IS the module's cost, and (with the driver
running everything else in milliseconds) it IS tactus-core's lean-phase
wall time.

## Anatomy
- 38KB statement (WP goal with the whole induction context inlined as
  nested lets), one-line proof:
  `intros <;> cases s <;> simp_all (config := {zetaDelta := true}) [and_assoc] <;> omega`
- `cases s` fans into ~10 Stm-constructor arms; each arm re-runs
  zetaDelta simp_all over the 38KB context at ~4-5s → ~48s total
  (profiler: ~10 × "simp took 4-5s").

## Failed cheap fixes (measured)
- Drop `zetaDelta`: FAILS after 79s — the lets must expand for arms to
  close, and failing simp is slower than succeeding simp.
- `omega`-first per arm: 48s — omega can't close arms pre-simp, so the
  simp cost stays.
- Zeta-expand once BEFORE `cases s` (then zeta-less arms): FAILS after
  80s — the arms don't close without their own zeta pass.

## Real fix direction
Shrink the STATEMENT, not the tactic: the 38KB goal is let-duplication
the leaf-normal-emission arc (DESIGN-leaf-normal-emission, N3/N4) is
designed to remove. This probe is that arc's benchmark: success =
wp53_repro elaborating in single-digit seconds with an equivalent
statement shape.
