---
title: "B5 — prelude split: TactusDefs (artifacts) / TactusSearch (dev-only)"
status: todo
claimed_by:
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
