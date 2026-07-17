---
title: "Lock ensure_prelude_olean against cross-process races"
status: todo
claimed_by:
created: 2026-07-17T11:40:00Z
updated: 2026-07-17T11:40:00Z
---

## Description

`lean_verify/src/prelude.rs::ensure_prelude_olean` has no cross-process
synchronization. Two tactus binaries running concurrently on one machine
(e.g., a gt gate + a tutorial battery) race the shared content-hashed
cache dir: oleans rename into place before the marker lands, and a
concurrent reader seeing marker-mismatch rebuilds in place, potentially
deleting the other builder's work mid-rename.

Observed 2026-07-17 during mainline-08 validation: tutorial chapters
flaked (4/10, then 8/10) ONLY while a gt gate ran concurrently; every
solo battery passed 10/10. The failure mode is intermittent and
load-dependent.

Fix shape: a lockfile in the cache root held across the
freshness-check + build + rename + marker sequence (e.g., `flock` on
`prelude.lock`, or a `.lock` dir with create-dir-as-mutex semantics).
Stale-lock cleanup (owner-pid check) if flock is unavailable portably.

**Done when:** two concurrent tactus runs sharing $HOME (a gt gate +
tutorial battery) both pass repeatedly; suite green.
