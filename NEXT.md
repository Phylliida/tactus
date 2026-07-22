# NEXT — bootstrap work queue (2026-07-21)

The single source of detail is the board (`board/*.md`); this is the
ordered summary of what remains. Suite state: 551/0 upstream; tactus-core
gate 231/0 + Link discharge 144/6 (the 6 = pre-existing other-hyp/HoistEq
residual; mode flags are part of the verification-cache key, `16d301c`).

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
