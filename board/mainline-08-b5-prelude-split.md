---
title: "B5 — prelude split: TactusDefs (artifacts) / TactusSearch (dev-only)"
status: in_progress
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

Split the prelude into:
- **`TactusDefs.lean`** — vocabulary only: defs, instances, decoration types,
  `arch_word_bits` + validity, Decidable promotion, conditional HXor instances.
  No tactics. This is the file in the trust/audit story.
- **`TactusSearch.lean`** — imports TactusDefs; the ladder (`tactus_first` /
  `tactus_auto` / `tactus_case_split` / `tactus_bit_vector` / `tactus_peel`
  until mainline-07 deletes it). Imported only in discover mode.

Replay/gate artifacts import TactusDefs alone; their tactics reference only
core/Mathlib T1 procedures. `prelude.rs`'s content-hashed olean cache extends to
two oleans. CAUTION (learned the hard way): the prelude is `include_str!` and
the shared cache olean rebuilds IN PLACE on any tactus-binary/test run with a
changed prelude — never run tests mid-measurement.

Spec: `DESIGN-transparent-automation.md` §5.

**Done when:** two-olean build works warm+cold; a package-check artifact
elaborates against TactusDefs only (once S2c/mainline-05 has removed its search
dependence — until then this brick just makes the split EXIST, with artifacts
still importing Search); suite green.

**Blocked by:** nothing (independent per §9); full payoff gated on mainline-05.

## Progress

- (2026-07-17 ~10:00Z, kimi) Claimed. Full map: the single
  `TactusPrelude.lean` (514 lines) has a clean vocabulary/tactics
  boundary at line 246 (`axiom Tactus.hasResolved`); the name surface
  outside prelude.rs is tiny (TACTUS_PRELUDE const, TACTUS_PRELUDE_IMPORT
  at 2 emit sites, sanity extraction, one integration test, doc refs).
- (2026-07-17 ~10:40Z, kimi) **Split landed.** `TactusDefs.lean` =
  vocabulary + `#tactus_check_axioms` (audits the axioms defined
  there); `TactusSearch.lean` = `import TactusDefs` + 4 ladder tactics.
  prelude.rs: two consts, content-hash over both sources, two-olean
  build in dependency order (defs standalone, search with defs dir on
  LEAN_PATH), marker = both sources + toolchain fingerprint.
  **Design deviation from the task text, recorded:** no "discover-mode"
  emission exists post-S2c, so instead of mode-gated Search imports,
  every artifact is scanned at the `pp_commands` chokepoint and gets
  `import TactusSearch` exactly when one of its theorems cites a search
  tactic in its closer (comments stripped, whole-word, 5 names). The
  injection runs before landmark computation — sourcemaps stay aligned.
- (2026-07-17 ~11:20Z, kimi) **Validation green:** gt gate 3116/0
  (package gate live); tutorial 10/10 (solo — see race note below);
  lean_verify 374/374 + 7 integration (integration test now
  inline-concatenates both halves); suite running. **The B6 gate claim
  is now textually real:** exactly 4 gt files import TactusSearch
  (apply_hom_gen/inv, todd_coxeter ×2 — the known user-override sites);
  all other pkg files are TactusDefs-only.
- **Race note (follow-up filed):** tutorial chapters flaked twice
  during CONCURRENT gt gate runs — `ensure_prelude_olean` has no
  cross-process lock, so two tactus binaries on one machine can race
  the shared content-hashed cache dir (oleans rename into place before
  the marker lands; a concurrent reader can rebuild-in-place). Solo
  battery: 10/10. Fix shape: lockfile around ensure_prelude_olean.
