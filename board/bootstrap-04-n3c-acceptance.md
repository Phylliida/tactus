---
title: "N3c — serializer acceptance: elaborate + decide smoke + golden + determinism"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
---

## Description

Close out the serializer per its acceptance criteria. Small; may share a
session with N3b.

Spec: `DESIGN-N3-serializer.md` §7.

- Every exec/WP-proof fn in `bootstrap-fixture/lib.rs`, `w15_probe.rs`, and
  `tactus-core/lib.rs` either serializes or is a documented stage-A exclusion
  (expect: the two bv fixture fns excluded, everything else in).
- Every cert file ELABORATES against the vendored TactusCore olean, and one
  `decide`/`#eval` probe per file (`stm_size <literal> = <n>`) confirms the
  literal kernel-computes. (Folds N5's smoke into acceptance.)
- Two consecutive runs ⇒ byte-identical cert files.
- Suite stays green with the flag off AND on (cert emission must not perturb
  verdicts).
- Golden-file unit test pinning one fixture fn's full cert text (drift =
  reviewed diff, like the trusted code it is).
- `sst_serialize.rs` under 1k lines incl. the contract doc-comment; verify.

**Done when:** all six criteria pass; doc §9 open-questions answered from the
real structs; battery green flag-on and flag-off.

**Blocked by:** bootstrap-03 (N3b).

## Progress

- (2026-07-13, opus) **Golden-file unit test LANDED early** (§7.5, the one
  N3c criterion not blocked by N3b). N3a's writeup listed it as the immediate
  remaining item. Added `sst_serialize::tests::golden_add_capped_cert`:
  - Golden = the verbatim cert file the rebuilt binary emitted for the real
    fixture fn `add_capped`, vendored at
    `source/lean_verify/src/testdata/add_capped.cert.lean` (tracked;
    `bootstrap-fixture/out/` is gitignored, so the golden needed its own home).
  - Test recovers the `CertBody` inputs FROM the golden (leaf texts from the
    `-- leaf N: ⟦…⟧` rows, ctx/sst terms from the two `def` bodies) and
    re-renders via `render_cert`, asserting byte-equality. Valid regression
    pin: golden bytes are fixed, recovered content is format-independent, so
    any header / leaf-table / def-naming / spacing / `stm_size … := by decide`
    change diverges. Avoids hand-transcribing the Unicode leaves + the long
    fully-parenthesized terms (a transcription-error surface in itself).
  - Caught a real parse bug while writing it (the header prose line
    `-- leaf rendering (stage B/W6)…` also begins `-- leaf `); fixed with a
    digit-index + `⟦` guard. Confirms the test exercises live logic.
  - `RUSTC_BOOTSTRAP=1 cargo test -p lean_verify sst_serialize` → 4/4 pass
    (34s incremental; no verus-binary rebuild). Hermetic: skips under a
    vendored `$TACTUS_CORE_VOCAB` (golden was emitted "unvendored").

  **Still blocked by N3b for the rest of N3c** (the GoalData literal must join
  the cert before the full elaborate-both-halves acceptance and the two-run
  determinism sweep over all three crates). N3a already validated §7.1–7.4 +
  §7.6 on the rebuilt binary (see bootstrap-02 writeup); this closes §7.5.

## Writeup

_when done: findings, how the code works, assumptions made_
