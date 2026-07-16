---
title: "W8 — authority flip (optional end state): reference output becomes the statement"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

The optional end state. Emitted statements become the REFERENCE's output; the
production renderer is demoted to a dev-UX pretty-printer. This deletes the
pretty-printer trust question entirely (strategy 2 of `DESIGN-bootstrap.md`
§4.1), reached incrementally after W4–W6 have soaked.

Spec: `DESIGN-bootstrap.md` §5 (W8 row); `VERIFICATION-PATH.md` ladder rung 6.

- Once the reference (refWp + stage-B expressions + defs layer) is trusted and
  soaked, the package verdict is computed FROM the reference, not compared
  against a separately-rendered production goal.
- Production renderer stays as a human-facing pretty-printer only; a mismatch
  between it and the reference is a UX bug, not a soundness bug.
- Completes the §1 end-state claim of `VERIFICATION-PATH.md` in full.

**Done when:** the package verdict is the reference's verdict; the pp is
demoted; the end-state trust inventory holds (kernel + serializer + frontend +
adequacy + platform pair, nothing else).

**Blocked by:** bootstrap-11 (W6) + bootstrap-12 (W7) soaked; W4 default-on.
Explicitly optional — the program is valuable stopping at any earlier rung.

## Progress

## Writeup

_when done: findings, how the code works, assumptions made_
