---
title: "B6 — gate policy: no-search artifacts asserted at the gate"
status: done
claimed_by: kimi
created: 2026-07-16T17:28:00Z
updated: 2026-07-16T17:28:00Z
---

## Description

The end-state one-line gate claim, next to the axiom-closure one: **"no artifact
imports the search module / contains a search tactic."** Gate crates
(tactus-group-theory, tactus-computability-theory, tutorial) run with derivation
+ inline proofs only; discover-mode ladder is dev-UX exclusively.

Under the derivation-first shape (mainline-04's primary candidate) there is no
"strict replay" mode to build — the gate property is simply that derived tactics
+ inline proofs close everything, asserted by (a) artifacts importing TactusDefs
only and (b) a text-level check that no T2 tactic name appears in emitted
artifacts. If mainline-04 chose a store instead, this task becomes the strict
replay mode of the original §3.1 (pin miss = hard error).

Spec: `DESIGN-transparent-automation.md` §5 (last bullet) + §9 B6.

**Done when:** gate crates' check.sh asserts the no-search claim and passes;
the claim's exact wording documented in the design doc.

**Blocked by:** mainline-05, mainline-08.

## Progress

- (2026-07-17 ~12:20Z, kimi) Claimed. First move: migrate the 3
  remaining gt user-override sites (apply_hom_gen/inv ×2, todd_coxeter
  ×2) so the claim can be ABSOLUTE rather than counted-residue.
  `first | tactus_auto | …` → kernel+CORE text; `tactus_usize_bound`
  inlined. Finding: the prelude macro's `subst h` form is
  broken-but-masked — `arch_word_bits` is a CONSTANT (subst can't
  fire), and these sites' obligations always closed via the
  `tactus_auto` branch before usize_bound could run. Composed
  overrides were never in the census pool (fast_attrib skips them), so
  this gap was invisible until the claim forced it. Working inline
  form (scratch-validated): `rcases arch_word_bits_valid with h | h
  <;> (simp_all only [usize_hi, isize_hi, h]; first | decide | omega)`.
- (2026-07-17 ~12:55Z, kimi) Gate check tool landed:
  `tools/check-no-search.py` — asserts (a) no `import TactusSearch`,
  (b) no search tactic in tactic position (5 names, comments stripped,
  whole-word). Perf lessons: artifact files reach 257MB — substring
  pre-filter + per-line analysis (5.5s → 0.09s); skip `build-*`
  workdirs and vanishing files. **The big gotcha:** the artifact tree
  carries STALE files from pre-S2c binaries (the gate never cleans
  `target/tactus-lean`) — thousands of tactus_auto hits, all
  historical. check.sh now deletes `*.lean` pre-run (`.olean` /
  `.verified` caches survive — content-keyed) so the claim covers
  exactly the current emission.
- (2026-07-17 ~13:10Z, kimi) **DONE — the claim holds with ZERO
  residue:** gt gate 3116 verified / 0 errors, then `check-no-search`
  over the fresh tree: **136 artifacts, no search module imported, no
  search tactic named** (0.09s). Tutorial check.sh (new) runs all
  chapters + the same assertion (141 artifacts hold). Claim wording
  recorded in DESIGN-transparent-automation.md §5 (B6 section).

## Writeup

**Done-when review:** gate crates' check.sh asserts the no-search
claim and passes ✓ — gt (`3116/0` + 136-artifact claim) and tutorial
(chapters green + 141-artifact claim); claim's exact wording
documented in the design doc §5 ✓. The claim holds with ZERO allowed
residue on both crates; the checker's `--allow` mechanism remains for
crates that can't yet reach zero (ct, per mainline-17).

**What this means:** default emission never names a search tactic
(S2c/B4), user override sites no longer name one either (this task),
and the gate now FAILS LOUD if either regresses. The ladder still
exists in TactusSearch for discover-mode UX — it simply never reaches
a checked artifact.

**Note for the main sync:** gt/tutorial check.sh derive the checker
path from the verus binary location (`$TOOLS/tools/check-no-search.py`)
— the main-line sync needs `tools/check-no-search.py` present in the
main tactus checkout (it lands with this commit series).
