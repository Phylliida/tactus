# NEXT — bootstrap work queue (2026-07-19)

The single source of detail is the board (`board/*.md`); this is the
ordered summary of what remains. Suite state: 551/0 upstream; tactus-core
gate 141/0 + Link discharge 69/69 (ALWAYS gate with `--lean-all-proofs` —
mode flags are now part of the verification-cache key, `16d301c`).

## 1. bootstrap-74 — bridge ↔ N1-hoist reconciliation (IN PROGRESS)

The blocker for ALL bridge decide-closes (13 fixture certs + 3 tgt
exec certs wait on it). Design is FINAL on the card (three passes,
converged). State:

- **Slice 1a DONE** (`d08b6c1`): FHyp name-field arity migration.
- **Slice 1b WIP** (`bd2d92f`): spec layer DONE (FLetH variant,
  `has_plain_flet` gate, close_e / close_sem_e / close_sem_obligs
  wrap-hoist split + gated dispatchers, six matcher arms).
  **Remaining: the proof layer** — precise numbered map in the card's
  "Slice 1b WIP state" section: 3 proof matches to mode-split
  (holds_close_e, cso_nil_true, cso_cons_split), u_cse_hyp/u_cso_hyp
  wrap-only restatements, prophecy_sound×2 ∀-form restatements.
  ⚠ 0-sentinel hyp names collide in hoist mode — use distinct ids in
  model fixtures; serializer must never emit 0 names.
- **Slice 2 (serializer)**: `_h_hoist_i` ordinal naming, FLetH
  classification (type_map typ + non-Bool), Call-post + RetBind
  conversion, goals-side deepener follow-up for hoisted shapes.
- **Then**: probe9 13/13 close + mutation-kill, probe11 re-run with
  the 3 tgt certs, retire the honest-fail entries.

## 2. bootstrap-70/71 residue — full closes (BLOCKED BY b74 only)

Both arms landed and validated to the pre-b74 limit (vec_read
precondition goal decide-closes with mutation-kill; use_clamped frame
ids match production exactly). When b74 lands, re-run probe9 +
mutation-kill the ∀-path frame. tgt census is clean: call-generic 0,
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
- Cache emitter-fingerprint: the closer/emitter BINARY version is
  still not in the cache key (documented hole, b74 card) — add a
  build-fingerprint tag if it ever bites.
- b74 residual: shadow-freshening honest-fail documentation once the
  serializer slice lands (no-shadow common case first).
