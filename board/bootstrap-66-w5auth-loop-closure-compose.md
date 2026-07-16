---
title: "W5-auth-6 — compose the loop closure: adequacy spine over the authored theorem + permanent runner; close bootstrap-10"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T22:40:00Z
---

## Description

The closing rung of the W5 umbrella (bootstrap-10). With `wp_stm_sound`
authored, emitted, and kernel-checked as part of the tactus-core package
(bootstrap-64/65), compose the end-to-end claim:

- **Re-point the adequacy spine** (probe27/28/29 + the probe30 groundings) at
  the **authored** emitted theorem instead of the probe-side hand-Lean
  `ref_wp_sound`. The spine itself stays hand-Lean **deliberately** — the
  denotation (`edenote`/SymEnv, oracle pins, binder embeddings) is part of the
  trusted *spec*, per VERIFICATION-PATH.md §5's permanent residue (kernel /
  serializer / frontend / **adequacy** / platform pair). Only the soundness
  proof under it moves into the kernel-checked package.
- **Permanent runner** (`probe-w0/` style, committed, exit-0 discipline like
  probe11's): regenerate tactus-core `out/lib`, elaborate the spine against
  the fresh emission, `#print axioms` the composed top-level fact, classify
  regressions. This is the standing loop-closure check.
- **Docs + claim update:** `DESIGN-W5-soundness.md` §5 final status;
  VERIFICATION-PATH.md rung 5 marked reached, with the honest statement of
  what is now claimed (*kernel-checked obligations ⟹ the operational spec*)
  and the residue restated; close the bootstrap-10 umbrella with the full
  writeup.

**Done when:** the runner passes green from a clean regen; the composed axiom
closure is recorded; bootstrap-10 status = done with writeup; VERIFICATION-PATH
updated.

**Blocked by:** bootstrap-64, bootstrap-65.

## Progress

- (2026-07-16, fable-b65 recon) Prerequisites all landed (bootstrap-60..65:
  the full model + wp_stm_sound + ref_wp_sound + corollaries, 138/0, gate
  green). Recon for the composition step, from the actual emission
  (`tactus-core/out/lib`):
  - The authored theorems ARE importable: pkg oleans
    (`lib__wp_stm_sound.olean` etc.), Stmts oleans (`TactusStmts_…__lib__
    ref_wp_sound` carries the `_stmt` Prop), and the Link module
    `out/lib/pkg/TactusLink_lib_exec.lean` derives `…_closed : …_stmt`
    defs with `#tactus_check_axioms … []` per theorem.
  - **The design question for this rung:** the `_stmt` Props are
    HYPOTHESIS-PASSING (premises = callee facts, e.g. ref_wp_sound's stmt
    binds `_h_ctx_0 : ref_wp c s = wp_stm (seed_frame c) s` and the
    wp_stm_sound equation as `→`-premises); recursive fns (wp_stm_sound)
    use the eta-bridge form (emit-module F3). So the spine cannot just
    `exact lib.ref_wp_sound …` — it must either (i) chain-discharge the
    premise-laden closed defs bottom-up in hand-Lean (mechanical, mirrors
    what Link's topo pass does), or (ii) keep the spine's own hand-Lean
    ref_wp_sound and add a DRIFT GATE equating its statement with the
    authored `_stmt` (weaker composition), or (iii) find/expose a
    premise-free closed alias from the Link layer (possibly a small
    emit-module feature: "export closed clean form for fns whose callees
    are all closed"). Option (iii) is likely the durable one — surface to
    Danielle at pickup.
