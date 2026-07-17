---
title: "W5-auth-4 — soundness proof, Loop arm; drop all scaffolding → total wp_stm_sound (probe24 authored)"
status: done
claimed_by: fable-b64
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T21:30:00Z
---

## Description

Author the probe24 (W5c) layer: the `Loop` arm — init / body / maintain-reclose
/ decrease goal groups over the havoc'd maintain/use telescopes — completing
the induction over the whole 10-constructor StmData vocabulary.

Key structure to mirror (the W5c havoc resolution, Opt-2): the operational
predicate **carries the frame** (`execSafeF`), the Loop arm havocs internally
via the emitted `loop_maintain_frame`, and each of the four goal groups closes
through the frame-agnostic `holdsAll_close_each_e` — the havoc'd frame is never
decomposed, so no `closeSem f ↔ closeSem (havoc f)` bridge is needed.

With Loop in, **remove every fragment guard/scaffold** — the theorem becomes
total:

```
wp_stm_sound : holdsAll (wp_stm f s) st ⟹ closeSem f st (execSafeF … s ·)
```

for **all** s. This is the headline theorem of the loop closure.

**Done when:** tactus-core `--lean-all-proofs` 0 errors with total
`wp_stm_sound`; no fragment predicate remains in the crate; axiom closure
clean; decide guards + existing probe runners green on the regenerated
emission.

**Blocked by:** bootstrap-63.

## Progress

- (2026-07-16, fable-b64) Landed `wp_stm_sound` (total, all 10 arms, iff),
  `u_ref_wp` + `ref_wp_sound`, and two non-vacuity pins
  (`wp_sound_bites_assert`, `wp_sound_bites_loop_init` = probe24 witness 1).
  No fragment scaffolding was ever needed (support-first landing order).
  Three iterations on the Loop arm, all TERMINATION-VC ergonomics (the
  postcondition math closed first try):
  1. IH after the big facts → termination VC carries every prior fact →
     whnf heartbeat timeout. Fix: IH call FIRST in the arm.
  2. Rust `let mframe/endf` ride into the VC goal; zetaDelta then forces
     simp to normalize loop_maintain_frame/frame_after on symbolic args →
     still times out. Fix: NO lets in the arm, inline the frame exprs.
  3. `tactus_auto` as first closer branch itself burns the whole 800k
     heartbeat budget on the Loop height reduction (11-field ctor), and
     generic tactus_case_split cases `f` before `s`. Fix: fn-level closer
     gains a FIRST branch `intros <;> cases s <;> simp_all (zetaDelta)
     [and_assoc] <;> omega` (the omega finishes the If/Seq height
     arithmetic simp can't). All five recursive-call termination VCs close
     in ~3s (hand-isolated before baking in).
  Final: **126 verified, 0 errors**, package gate green (48/50 reused).
  Axiom closure over every VC of wp_stm_sound/ref_wp_sound/bites +
  bridge lemmas: subsets of [propext, Classical.choice, Quot.sound] —
  Lean core only, no sorryAx.

## Writeup

**THE LOOP-CLOSURE THEOREM IS AUTHORED AND KERNEL-CHECKED.** tactus-core
now contains, as ordinary tactus spec/proof fns verified by the tactus
binary and kernel-re-checked through the standard package gate:

    wp_stm_sound : holds_all(hp, he, lv, wp_stm(f, s), st)
                     == exec_safe_f(hp, he, lv, f, s, st)
    ref_wp_sound : holds_all(hp, he, lv, ref_wp(c, s), st)
                     == exec_safe_f(hp, he, lv, seed_frame(c), s, st)

for every oracle triple (valuation-parametric), every frame telescope,
every statement in the full 10-constructor StmData vocabulary, and both
directions (soundness AND faithfulness). The Loop arm never decomposes
its havoc'd frames (frame-agnostic bridge lemmas). Non-vacuity is pinned
(the leaf arms demand the actual obligations; the loop-init pin recovers
`he(render_exp(ob), st)` from the emitted init goal alone).

New idiom for the memory file: TERMINATION VCs inherit the arm's prior
facts and Rust lets — keep recursive calls first-in-arm and let-free in
big arms; and a fn-level closer can carry an explicit `cases <param>`
branch when tactus_auto/case_split pick the wrong local or blow the
heartbeat budget.

Remaining tail of the W5 umbrella: bootstrap-65 (prophecy/closure
corollaries), bootstrap-66 (adequacy-spine composition + runner + docs).
