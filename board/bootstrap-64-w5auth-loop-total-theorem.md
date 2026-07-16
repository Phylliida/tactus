---
title: "W5-auth-4 — soundness proof, Loop arm; drop all scaffolding → total wp_stm_sound (probe24 authored)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
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
