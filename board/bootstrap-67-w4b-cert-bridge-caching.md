---
title: "W4b — cert + bridge caching (content-keyed, warm-run skip) + cost numbers on fixture and tgt"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

The remaining engineering before the W4 default flip (umbrella bootstrap-09):
make the in-gate bridge cheap on warm runs, then measure.

- **Cache story:** cert files + bridge oleans content-keyed like islands — a fn
  whose SST + goals are unchanged skips re-serialization and re-bridging.
  Interacts with two known facts: (a) `-V cache` Z3-cache hits skip the emit
  path entirely (probe11 census prereq B) — decide + document the intended
  composition (a cache-hit fn has an unchanged cert by construction; the bridge
  cache should key on the cert content so this is safe, but make it explicit);
  (b) `render_and_build` already content-compares (`up_to_date`) — reuse that
  machinery rather than inventing a second scheme.
- **Cost numbers** (the W3-mandated justification for defaulting on): cold and
  warm wall-clock with `--tactus-bridge` on the fixture and on tgt
  (`--verify-module runtime` + a full-crate run), vs. the same runs without.
  Run long jobs in the **foreground** single Bash call (die-with-parent lesson,
  bootstrap-39).

**Done when:** warm re-runs skip unchanged certs/bridges (verified by mtime or
log inspection over consecutive runs); cold/warm numbers for fixture + tgt are
recorded in the card; suite green.

**Blocked by:** nothing (W3 done, in-gate bridge validated by bootstrap-39).
