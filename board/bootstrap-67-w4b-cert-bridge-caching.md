---
title: "W4b — cert + bridge caching (content-keyed, warm-run skip) + cost numbers on fixture and tgt"
status: done
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-08-02T00:00:00Z
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
  (`--verify-module runtime`), vs. the same runs without.
  Run long jobs in the **foreground** single Bash call (die-with-parent lesson,
  bootstrap-39). (Danielle 2026-08-01: the full-crate tgt run is REMOVED from
  this card — no full tgt gates; the scoped `--verify-module runtime` run is
  the tgt column, and B2's condition 4 loses its "one full acceptance run"
  wording likewise.)

**Done when:** warm re-runs skip unchanged certs/bridges (verified by mtime or
log inspection over consecutive runs); cold/warm numbers for fixture + tgt are
recorded in the card; suite green.

**Blocked by:** nothing (W3 done, in-gate bridge validated by bootstrap-39).

---

## Design review (2026-08-01, pre-implementation — the b80-stage-2 model)

Survey + empirical findings the design is frozen against:

1. **Cert writers rewrite unconditionally.** `write_cert_file` /
   `write_def_cert_file` / `write_dt_cert_file` (sst_serialize.rs) do
   `File::create` every run — byte-identical content, fresh mtime. Any
   downstream mtime reasoning is defeated, and the rewrite itself is
   avoidable churn.
2. **The bridge re-elaborates every obligation cert every gate run.**
   `run_bridge_step` (generate.rs) spawns one `lean` process per cert
   (~2s each: process start + olean import dominate) with no skip path.
   This is THE warm-run bridge cost B1 exists to kill.
   `core_olean_hash` already exists and its own doc comment names it
   "the seed of W4b's bridge cache key".
3. **`-V cache` does NOT gate tactus emission today (empirical).** Warm
   fixture run with `43 cached` (Z3-verdict-cache hits) still rewrote
   every cert and reported the full `certified 43/48` census — the
   tactus route `continue`s before the Z3 cache lookup (verifier.rs),
   so the probe11 run.sh note "a cache-hit fn skips the emit path
   (census prereq B)" is STALE (written 2026-07-13, pre-routing-
   restructure). Composition decision (the card's "decide + document"):
   the two caches are INDEPENDENT layers. The `-V cache` caches
   Z3-path query verdicts (non-routed fns, plus routed fns'
   SpecTermination/CheckApiSafety queries); it never stands in for
   cert emission or bridging. The bridge cache keys on cert CONTENT
   (§D4), so any future change that does skip emission on a cache hit
   is still safe by construction: no new cert text ⟹ no new bridge
   obligation, and the on-disk cert + marker pair remains the
   authoritative record of what was bridged. probe11's comment gets
   corrected (cold regen stays the recipe; the mechanism note was
   wrong).
4. **P3(b) is specifically the `-V cache` base key** (b74 card:
   "the emitter/closer BINARY version isn't keyed — a rebuilt binary
   with changed closer logic reuses old verdicts until the krate hash
   moves"). Base today: solver + lean-backend flag + krate debug hash.
   The WP translation / SST→AIR lowering / routing are all Rust-side
   and invisible to that key.
5. **Existing precedent + a deliberate prior decision to respect.**
   `ladder_fingerprint()` (project.rs) = toolchain + exe mtime+size,
   used for defs-ladder records ("one ladder retry per rebuilt binary
   is the honest price"). Its doc comment records that island
   `.verified` markers DELIBERATELY do not key on the binary: they key
   on emitted text (always regenerated), and "this text elaborates" is
   a binary-independent fact. The pkg-olean cache has the same property
   PLUS the Link gate re-elaborating the closure every run (sorry
   can't hide in a cached pkg verdict). So: islands and pkg stay as
   they are; the fingerprint lands where the hole actually is — the
   `-V cache` verdict cache — plus the new bridge markers (D4).

Frozen design:

- **D1 — `emitter_fingerprint()`** (lean_verify::project, beside
  `toolchain_fingerprint`): `VARGO_BUILD_VERSION` via `option_env!`
  (vargo sets it for the whole build, so lean_verify sees the same
  value rust_verify's `verus_build_info` reports; "unknown" fallback)
  + FNV-1a of `current_exe` BYTES. Content, not mtime: deterministic,
  and it catches dirty-tree rebuilds where the version string is
  unchanged (`<sha>.dirty` for two different trees). OnceLock-memoized
  (4 MB exe, one hash per process). FNV-1a matches the existing
  `vocab_hash`/`core_olean_hash` style (SHA-256 vendoring is a
  separate §6 item).
- **D2 — `-V cache` base gains the tag** (verifier.rs cache
  construction): `emitter:{fingerprint}` alongside the existing
  solver/lean tags. One-time global invalidation of
  `target/verus-cache/` everywhere — that is the intended effect.
- **D3 — cert write content-compare** (M5e pattern, the card's "reuse
  not reinvent"): all three cert writers write only when the rendered
  text differs (tiny `write_if_changed` helper + tempdir unit pin).
  Byte-identical certs keep their mtime. Census untouched.
- **D4 — bridge pass cache** (`run_bridge_step`): per-cert marker
  `Bridge_<leaf>.verified` in the bridge dir, content = FNV-1a key over
  {bridge module text (cert body + suffix), `core_olean_hash`,
  `toolchain_fingerprint()`, `emitter_fingerprint()`}. Island-marker
  discipline exactly: check before run; remove marker before the live
  run; write only on success (a failed/crashed run leaves no stale
  trust). A hit skips the `lean` spawn and counts into a new cached
  column in the gate note: "N obligations bridge-checked against
  tactus-core (P passed, F failed, C cached) [core-olean H]". Stale
  markers for vanished certs are never consulted (the loop iterates
  current certs) — same as today's stale `Bridge_*.lean` behavior.
  Pure helpers (`bridge_cache_key` + marker hit/miss) factored for
  unit pins.
- **D5 — docs**: probe11 run.sh mechanism-note correction (finding 3).
- **D6 — cost numbers**: fixture + tgt `--verify-module runtime`
  (scoped per the no-full-tgt-gates constraint), cold/warm ×
  ±`--tactus-bridge`, recorded in a table below. Target: warm-run
  bridge overhead ≈ 0 on unchanged fns.

Explicit non-goals (scope discipline): no routing changes (tactus fns
still don't consult `-V cache`; serialization is not the cost, the
lean spawns are); island markers untouched (finding 5's deliberate
decision); pkg-olean path untouched (text-keyed + Link backstop);
bridge stays note-only (the flip is b68, with its own four gate
conditions).

Unit pins: `write_if_changed` (write / skip / rewrite-on-change);
`bridge_cache_key` (deterministic; sensitive to each component);
`emitter_fingerprint` (non-empty, intra-process stable); marker
hit/miss helper. Empirical acceptance per the card's Done-when: two
consecutive warm gate runs with `--tactus-bridge`, second run's log
shows all certs cache-skipped (mtime-stable certs via D3, "C cached"
via D4).

Risks: (a) e2e has `-V cache`-behavior tests — the base-tag change
invalidates once, then hits behave as before (same binary); (b)
`current_exe` under `cargo test` is the test binary — consistent per
binary, fine for the pins; (c) the fingerprint over-invalidates on ANY
relink (unrelated code changes included) — safe direction, and "one
re-verify per rebuilt binary" is the ladder precedent's honest price.

---

## Completion record (2026-08-02, one session)

Landed as designed (D1–D5), no deviations:

- **D1** `emitter_fingerprint()` — `VARGO_BUILD_VERSION` + FNV-1a of
  `current_exe` bytes (`lean_verify::project`).
- **D2** `-V cache` base gains `emitter:{fingerprint}` (verifier.rs) —
  P3(b) closed. (Side effect, intended: first run after the rebuild
  re-verified the Z3-path queries once; pkg/lean layers unaffected.)
- **D3** cert writers content-compare — verified live: a byte-identical
  re-emission preserves cert mtime (fixture, new binary vs old certs).
- **D4** per-cert bridge pass markers (`Bridge_<leaf>.verified`) —
  verified live on tactus-core (below).
- **D5** probe11 run.sh mechanism note corrected.
- Unit pins: 4 new (key determinism/sensitivity, marker discipline,
  fingerprint shape, write-if-changed mtime preservation).

### Cost numbers (all serialized runs; worktree binary)

tactus-core gate (`-V cache`, 291 fns, 166 obligation certs):

| run | wall | bridge note |
|---|---|---|
| warm, no bridge (baseline) | 34.7s | — |
| warm + bridge, markers cold | 2m16.7s | 166 passed, 0 failed, 0 cached |
| warm + bridge, markers warm | **35.2s / 34.5s** | 0 passed, 0 failed, **166 cached** |
| warm + bridge, 1 marker deleted | 35.4s | 1 passed, 165 cached |
| warm + bridge, mass content invalidation (vocab-hash header flip) | 2m21.1s | 166 passed, 0 cached |
| cold + bridge (rm -rf out) | 10m35.1s | 166 passed, 0 failed, 0 cached |

Cold baseline (no bridge) is ~10 min per the standing HANDOFF recipe —
cold bridge marginal ≈ +35s. Post-cold warm runs re-engage every layer
(224 pkg cached, 166 bridge cached, gate 54, discharge 198/0) and run
~1m30s under post-cold system load with an identical cache profile;
the same-regime ±bridge comparison (the flip-critical number) is the
pair above.

**Flip target met: warm bridge overhead ≈ 0.5s (~1.4% of the 34.7s
baseline; target was within ~10%).** Live-bridging marginal cost ≈ 102s
per full 166-cert corpus (~0.6s/cert) — paid only on real content
change.

Fixture: warm emit+cert ≈ 2.5s, certs byte-stable (golden diff clean),
mtimes preserved. The fixture's in-gate bridge does not run — its 11
pre-existing per-fn errors skip the package gate (documented class,
verdict-neutral); fixture bridging remains probe9's external runner
(green).

tgt (`--verify-module runtime`, scoped per the no-full-gates
constraint): cold module gate 1m48.7s with bridge / 1m51.3s without —
but the module gate is currently RED (11 errors) under the worktree
binary, so the in-gate bridge never executes on tgt today.

### Findings for Danielle

1. **tgt runtime-module gate drift (RESOLVED 2026-08-02 — see
   `FINDINGS-tgt-runtime-module-gate.md`).** Diagnosed on request: NOT
   b67, NOT bootstrap-lane (identical on tgt's blessed binary) — latent
   decreasing_by/mono-template bugs since mainline-10/N3 (ctor
   mis-classification; dite-encoded Prop-connective guards the named
   TERM set can't decompose). Fixed in `00827513`: the whole tgt defs
   layer elaborates again. Residual: 11 errors in 3 recursive proof fns
   (N3 script-form closer class — paths (a) script-author
   `have`-instantiation move / leg coverage, (b) S2c fn-level
   overrides; Danielle's call). Port to `tactus/source` needed.
2. **Cert perturbation composition (by construction, verified).** A
   hand-edit to an on-disk cert does not produce a bridge red: the gate
   re-emits certs from SST before bridging, and D3's content-compare
   rewrites only on a real diff. The honest red channel is
   emission-side drift (serializer/vocab change), which flips the
   marker key by construction — exercised via the vocab-hash header
   flip (166 live) and single-marker deletion (1 live). The deliberate-
   perturbed-cert e2e red pin is B2 scope (needs an emission-side hook).
3. The bridge note's third column is now `cached`; B2's standing
   trust-inventory line can read straight from it.

### Battery

units 432+7/0; tactus-core gate 291/0 + pkg gate 54 + Link discharge
198/0 (re-run 7× across the measurements); probes 9 (ALL CLASSIFIED),
11 (ALL CLASSIFIED), 13 (22 classes PASS), 14 ✓, 17 ✓, 37 ✓, 38 ✓;
golden byte-stable; e2e 829/2 (the 2 = documented pre-existing
flat_combine/tutorial_fifo standing baseline).
