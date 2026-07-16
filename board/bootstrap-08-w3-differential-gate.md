---
title: "W3 — differential gate over tgt (the bug-finding payoff)"
status: done
claimed_by: opus-w3
created: 2026-07-13T19:38:00Z
updated: 2026-07-14T18:40:00Z
---

## Description

Run serializer + bridge across tgt. Every fn where `decide` says NO is a bug in
production, refWp, or the serializer — all three are interesting. This is a
bug-FINDING deliverable independent of the W5 soundness proof, and the first
milestone where the certificate holds at real-corpus scale.

Spec: `DESIGN-W2-refwp.md` §3; claim-ladder rung 3 in `VERIFICATION-PATH.md`.

- Certs emitted during a normal gated run; bridge files batch-elaborated like
  stmt modules (reuse `ensure_stmt_olean`-style plumbing).
- Failures reported per-fn with both GoalData terms pretty-printed + a small
  Rust differ computing the first-divergence path (goal index → spine
  position) so triage never reads raw terms.
- Triage discipline: classify every divergence (production bug / refWp bug /
  serializer bug / stage-A scope gap) in a running table in `DESIGN-W2-refwp.md`.
  Scope gaps feed stage B; production bugs get pinned e2e tests (like this
  week's five).
- Bridge wall-clock budget ≤ the package gate's own cost (else flag for W4).

**Done when:** tgt divergences = 0 UNEXPLAINED; certified fraction reported;
triage table complete; any production bugs found are pinned with e2e tests.

**Blocked by:** bootstrap-07 (W2b bridge) + bootstrap-05 (N4 census informs
which constructs are in scope).

## Progress

- (2026-07-14, opus-w3) **DONE at current serializer scope.** Ran the
  differential gate over tgt end-to-end: emitted the cert, bridged it, found +
  triaged a divergence, built a reusable runner + pinpoint evidence.
  `probe-w0/probe11_w3_tgt/` (run.sh + Pinpoint.lean + REPORT.md + .gitignore).

  **Emit.** Targeted cold `--verify-module` runs of the bootstrap release binary
  (the flag isn't in the tgt-facing binary — census prereq A) with
  `--emit-lean --tactus-emit-cert`, no `-V cache` (census prereq B: cache-hits
  skip the emit path). `runtime` (~83s): `certified 1/7`, `24 verified, 0
  errors` (verdict-neutral). `todd_coxeter_rt`: 0 certs, both exec fns
  `assert-query`. Reproduces the N4 census buckets exactly.

  **Corpus is census-limited (the key finding for scaling W3).** Stage-A
  emission is exec-fn-only; tgt has 9 exec fns, of which exactly **1** emits a
  cert (`runtime::impl__4::clone`) and 8 are loud scope-rejections (5
  `StmData::Call` = bootstrap-02b; 3 `assert-query`) that emit NO cert and are
  NOT bridge subjects. So the gate has ONE bridgeable subject today. This is the
  architectural fork Danielle flagged: W3's breadth is gated on the Call +
  assert-query serializer arms, not on the runner. The runner is permanent and
  re-runs trivially once those land.

  **The one cert DIVERGES — triaged to a single leaf.** `clone(self:
  &RuntimeSymbol)` bridge `goals_eq refWp production = 1` is FALSE. Pinpoint-
  proved (`Pinpoint.lean`, 4 decides) the SOLE divergence is the RetBind-value
  leaf: SST `RetLet(4,0)` binds `_return := leaf 0 ⟦self⟧`; production binds
  `_return := leaf 5 ⟦self.deref⟧`; patching only that leaf (`Let 4 5 → Let 4
  0`) closes it. refWp is faithful (`ret_frame` folds the SST val verbatim);
  production is correct; the SERIALIZER misses the `*p→p.deref` `&`-param subst
  at the RetBind-value render site. NEW site, SAME class as head_exec
  (bootstrap-18, the obligation-leaf site) — the deref-subst gap is systemic
  across leaf-render sites. Batched onto bootstrap-18 (§ "Second site"); logged
  to DESIGN-W2-refwp.md §5 W3 triage. Sound honest-fail (DESIGN §2.5), not a
  refWp/production bug. run.sh classifies it HONEST-FAIL (a later CLOSE =
  regression). Runner green (exit 0, "ALL TGT BRIDGES BEHAVE AS CLASSIFIED").

## Writeup

**W3 — differential gate over tgt — DONE (census-limited scope) + GREEN.**

### What landed

`probe-w0/probe11_w3_tgt/`: `run.sh` (emits-recipe header + bridges on-disk certs
with the probe9 HONEST-FAIL/regression discipline), `Pinpoint.lean` (4 kernel-
checked decides isolating the divergence; a snapshot of the emitted cert so the
finding is committed even though the cert is gitignored/regenerable),
`REPORT.md`, `.gitignore` (out islands regenerable). Triage recorded in
DESIGN-W2-refwp.md §5; the second deref site recorded on bootstrap-18.

### Result vs the task's "done when"

- **tgt divergences = 0 UNEXPLAINED** ✓ — exactly 1 bridgeable cert; it diverges;
  fully triaged (serializer RetBind-value deref gap). The 8 non-certs are all
  known census scope-rejections (not divergences).
- **certified fraction reported** ✓ — 1/9 exec fns crate-wide (census-limited).
- **triage table complete** ✓ — DESIGN §5 W3 entry + REPORT.md.
- **production bugs pinned** — none found; the sole divergence is a serializer
  faithfulness gap (batched onto bootstrap-18), not a production bug, so no e2e
  pin is warranted (an e2e pin is for production behavior, not a TCB-side leaf
  render). If a future re-run finds a production/refWp bug, THAT gets pinned.
- **bridge wall-clock ≤ package-gate cost** ✓ — ~1.2 s/fn (olean-import bound).

### How it works

Same bridge mechanism as W2b/probe9: append
`example : goals_eq (ref_wp cert_ctx cert_sst) cert_goals = 1 := by decide` to
the cert and elaborate against tactus-core's `out/lib` oleans (which carry
`ref_wp`/`goals_eq` + the mirror constructors the serializer emits). The only new
plumbing is the targeted cold emit (`--verify-module` + `--tactus-emit-cert`,
no cache) to produce the tgt cert, and the honest-fail classification for clone.

### Assumptions / honest scope

- **"0 unexplained divergences" is over the bridgeable subset (1 cert).** The
  bug-finding breadth of W3 is bounded by how few tgt exec fns clear stage-A
  scope today (1/9). This is not a weakness of the gate — it is the census
  reality (tgt is proof/spec-heavy). The real broad payoff arrives when
  bootstrap-02b (Call) + an assert-query arm unlock the other 8; re-run then.
  I did NOT expand the corpus beyond tgt (the task scopes W3 to tgt); the
  bootstrap-fixture family is the separate serializer stress corpus (probe9).
- **The clone divergence is a serializer leaf-render gap, provably the sole one.**
  I did not fix it here (that's bootstrap-18, now covering both deref sites);
  W3's job is to FIND + triage, which it did. Fixing it is validated by moving
  clone out of the runner's honest-fail set + a negative-control mutation.
- Runs against on-disk certs (gitignored/regenerable; recipe in run.sh header).
  Same lean v4.25.0 / prelude-e81fbf9a86375c12 pin as probe9.
