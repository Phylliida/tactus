# NEXT — bootstrap work queue (2026-07-21; superseded 2026-07-24)

**2026-07-24 evening: endgame rows 5+6 (A3+A5+R1 batch) LANDED —
`board/bootstrap-77-a3a5r1-batch-churn.md`.** tactus-core 254/0 +
discharge 172/0; probe9 all-green (head_exec CLOSES via IfCtor);
probe11 all-classified (find_cancellation = the vec_read/A7 stage-B
class); `assert-query-tactus` census tag retired; probes 13/14/37/38 +
units green. ⚠ FIRST STANDALONE TASK (nothing else heavy in parallel — it OOM'd
under session load): the full tgt gate with the BOOTSTRAP binary
(recipe + the word_numbering observation on the b77 card §Follow-ups).
Remaining endgame order: **b77 follow-up mutation kills FIRST
(next-session warm-up: probe13 `ifctor_eq_drop`/`ifctor_arm_swap`/
`aqt_hyp_drop` classes — concrete recipe on the b77 card §Follow-ups,
incl. the bracket-aware splitter) → A4 (call-mut, card first) →
A7 (stage-B callee-signature vocab — closes vec_read AND
find_cancellation) → B (b67 caching + b68 flip)**. D's in-model
tripwire column landed with b77. NOTE the serializer header now names
a SECOND trusted predicate (the shared N2 IsVariant detector) —
reference-side derivation rides with A7, cross-check pin rides with
the mutation kills.

**The ordered map of everything remaining is now
`DESIGN-bootstrap-endgame.md`** (milestones A–F + policy points P1–P4,
agreed with Danielle 2026-07-24). The single source of per-brick detail
is still the board (`board/*.md`); this file's sections below remain as
the pre-endgame snapshot. **Milestone C DONE 2026-07-24: Link discharge
150/0** (HoistEq + Req composer arms, b73 closed) **+ P1 poison
contract/mutation** (probe13 `poison_flip`, probes de-staled). **A1
DONE same day: b70/71 closed via probe38** (∀-path close + 2 frame
kills; vec_read goal-0 close + kill; A7 tripwire). **A2 DONE same day
(b75): apply_hom_gen/inv bridge-close — probe11 3/3 CLOSE.** The real
mechanism was the CLOSER GATE (production never hoists user-tactic
fns), not arg-temp LetRaw: shared `closer_is_default` + serializer
wrap-mode + `build_req_binders` leaf reuse + call-leaves ledger. New
tags: `user-closer-hoistless`/`user-closer-loop`. **A6-short DONE same
day (b76): assert-forall census-rejects via production's own skolem
detection — probe11 fully green, 3/3 CLOSE, zero honest-fails, no
non-bridging certs anywhere.** Next: A3+A5 batched tactus-core churn
(AssertQueryTactus variant + Match arm + fn-level force-wrap bit),
then A4 (call-mut), A7 (stage-B vocab), B (b67/b68 flip). Suite
state: e2e 551/0; tactus-core gate 231/0 + Link discharge 150/0.

## 1. bootstrap-74 — bridge ↔ N1-hoist reconciliation (DONE 2026-07-21)

All four slices landed (1a `d08b6c1`, 1b `17b6e72`, slice 2 rounds A–D
`734711b`/`a2c40ad`/`651b532`/`4fdd7df`/`ca8dd93`). The blocker for ALL
bridge decide-closes is cleared: **probe9 18/20 close + 2 documented
(vec_read stage-B, head_exec N2-match); probe11 clone closes + 4
documented (apply_hom call-arg temps, assert-forall)** — ALL CLASSIFIED ✓
on both runners. Slice 2 covered: 3-mode goal rendering (wrap / hoist /
hoist+residue with poison gate), uniform loop telescope (`_h_ctx_N` and
the leading/non-leading split are gone), `_h_hoist_i` per-goal-path hyp
naming, FLetH/AssignH/AssignR/RetLetH classification, the shadow mirror
(hoist-only freshening `i_hoist1` + renames), `inv_obligs_exit` (renamed
re-close obligations), the AssertQueryNl degenerate-True goal.

## 2. bootstrap-70/71 residue — full closes (UNBLOCKED)

b74 landed. Both arms landed and validated to the pre-b74 limit (vec_read
precondition goal decide-closes with mutation-kill; use_clamped frame
ids match production exactly). Now: re-run probe9 + mutation-kill the
∀-path frame, close both cards. tgt census is clean: call-generic 0,
call-forall-path 0; remaining tags = 1 call-mut (runtime.copy_word,
+ vec_push7/fill_zeros fixtures) and 4 assert-query-tactus.

## 3. bootstrap-69 residue — Tactus-mode assert-query design

AssertQueryNl (NonLinear) is done end-to-end (F20 mul_bound cert
emits). The 4 remaining tgt assert-query fns are TACTUS-mode:
production renders them inline (`have h : P := by <tactic>` — no
separate goal, P enters as hyp), so the stage-A mirror looks
Assume-like. Small design decision for Danielle, then a small arm.

## 4. Later / parked

- call-mut arm (prophecy/rebind machinery) — unblocks vec_push7,
  fill_zeros, runtime.copy_word. Genuinely new machinery; card it
  before starting.
- **Call-arg temp lets + auto-ref arg coercion** (apply_hom class,
  from the probe11 sweep): arg temps are typ-less `Wp::LetRaw` frames
  (production wraps); the serializer must classify them plain-Assign
  and keep the `Tactus.Ref.mk <arg>` coercion in instantiated requires.
- **assert-forall loud census rejection** (from the probe11 sweep):
  skolem binders are unmodeled — today these emit non-bridging certs;
  they should reject loud with an `assert-forall` tag instead.
- **stmts-olean staleness** (found during Round D): a fresh
  `TactusStmts_*.lean` was written without its olean being rebuilt,
  and the next gate's Link layer reported a misleading
  Type-mismatch/sorry cascade. Investigate the stmts-module rebuild
  logic.
- Cache emitter-fingerprint: the closer/emitter BINARY version is
  still not in the cache key (documented hole, b74 card) — add a
  build-fingerprint tag if it ever bites.
- Stage-B deep-leaf coverage growth (ongoing): vec_read's
  view-call/CallN coercion derivations (§7.7 of the slice-2 doc).
