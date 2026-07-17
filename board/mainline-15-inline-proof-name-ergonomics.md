---
title: "Ergonomics decision — inline proofs cite full dotted names (`open <crate> in`?)"
status: todo
claimed_by:
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

Open question for Danielle from the Option B migration: inline user tactic
texts now cite full dotted names (`lib.runtime.foo`) — correct but verbose, and
rename-brittle for single-file crates (they cite file-stem crate names). The
candidate visible-uniform alternative: a scoped `open <crate> in` emitted
around user tactic blocks (one line, at the site, no ambient context — passes
the guiding rule, unlike the rejected shadow-gated printer).

Gains weight as the S-arc pushes more proof text INTO the source (mainline-04's
inline-proof surface): the more inline proofs, the more the verbosity costs.
Known hazards to weigh (from the migration): `try unfold X` swallows
unknown-name misses silently; shadow flips can WRONG-RESOLVE (pow_pos → core's
pow_pos) — an `open` widens that exposure; the decision should name it.

**Done when:** decision recorded (design doc or a note here); if `open ... in`
adopted, emitter change + gt/tutorial migration of existing tactic texts (or an
explicit "keep full names" close).

**Blocked by:** nothing; naturally paired with mainline-04's conversation.
