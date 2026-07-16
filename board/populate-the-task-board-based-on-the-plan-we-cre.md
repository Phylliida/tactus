---
title: Populate the task board based on the plan we created
status: done
claimed_by: fable
created: 2026-07-13T19:36:39Z
updated: 2026-07-13T19:38:00Z
---

## Description

Populate the task board from the bootstrap plan (`VERIFICATION-PATH.md` →
`DESIGN-bootstrap.md` → `DESIGN-N3-serializer.md` + `DESIGN-W2-refwp.md`),
one `.md` per checkable brick, in dependency order.

## Progress

- (2026-07-13) Board moved from the main `tactus` checkout to the
  `tactus-bootstrap` worktree (bootstrap branch) so it lives beside the plan.
- (2026-07-13) Created `bootstrap-00` (landed-foundation anchor, done) +
  `bootstrap-01…13` (todo queue) mapping the plan's sequence.

## Writeup

The board now carries one anchor + 13 forward tasks, prefixed `bootstrap-NN-`
for dependency-order sorting:

- `00` foundation (done anchor)
- `01` N2.1 mirror amendments  ← next actionable
- `02–04` N3a/b/c serializer (core → goal provenance → acceptance)
- `05` N4 census
- `06–07` W2a/b refWp worker → bridge + mutation kills
- `08` W3 differential gate (bug-finding payoff)
- `09` W4 bridge default-on
- `10` W5 soundness loop (umbrella, staged W5a–e, very large)
- `11` W6 stage-B expressions
- `12` W7 defs layer
- `13` W8 authority flip (optional end state)

Each carries acceptance criteria + a spec pointer + a **Blocked by** line
(the format has only todo/in_progress/done, so ordering is encoded there).
Assumption: the board lives on the `bootstrap` branch with the plan; if the
web UI reads a different checkout, the dir may need to move again.
