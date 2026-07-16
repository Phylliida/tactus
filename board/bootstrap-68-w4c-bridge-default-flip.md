---
title: "W4c — flip the kernel bridge on by default in package mode; close bootstrap-09"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

The W4 default flip itself (umbrella bootstrap-09), once bootstrap-67's cache +
cost story justifies it:

- Bridge on by default under the package gate (`--lean-backend` package mode);
  an opt-out flag for dev loops if the numbers say one is needed.
- **Bridge failure = verification error at the fn** (today it is note-only /
  opt-in). Honest-fails (census-rejected shapes) remain non-errors — they emit
  no cert and are not bridge subjects; only a cert that exists and fails to
  close errors.
- Gate note gains the standing line: "N obligations bridge-checked against
  tactus-core (…)".
- Suite: pin at least one e2e test where a deliberately perturbed cert turns
  the run red (the mutation-kill discipline, in-harness).

**Done when:** a plain `--lean-backend` package run bridge-checks every
serializable fn by default; failure is a verification error; suite green
(including the red-path pin); bootstrap-09 closed with writeup.

**Blocked by:** bootstrap-67.
