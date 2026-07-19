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

## Status update (2026-07-17, after S2c/B4/B6/B10)

The verbosity cost is now MEASURED, not hypothetical: the 8 residue
inline proofs in gt each embed the full 51-lemma CORE list inline
(~700 chars per override, repeated 4-8 times per file). They work
(name-is-spec, rename-loud), but they're the worst-case data for this
decision. The options as they look from here:

1. **`open <crate> in`** — helps the dotted-name part (lib.seq.…) but
   NOT the CORE-list bulk (the lemmas are core Lean names, not
   crate-namespaced). Doesn't solve the real pain.
2. **A prelude-defined named lemma set** — Lean 4 core has NO named
   simp-set bundle mechanism; would need `macro "tactus_core_simp"` —
   a new user-visible macro, against the two-surface spirit (a named
   tactic that isn't a decision procedure). Danielle's call, but it
   reads like a fourth surface in disguise.
3. **Accept the verbosity** (status quo): correct and explicit; the
   residue is small (8 sites) and stable. The mainline-04 rule budget
   argument favors this: the inline proofs are SUPPOSED to be
   self-specifying.
4. **Emitter-generated residue suggestions**: when the derived closer
   fails at a named obligation, the failure message could print the
   exact inline-proof text to paste (the census harness already
   produces these lists). Turns verbosity from a writing cost into a
   pasting cost — probably the best UX-per-rule-budget ratio.

Leaning (3)+(4): keep the rule budget at one, and make failures
self-suggesting. Danielle's call.
