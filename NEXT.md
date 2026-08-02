# NEXT — bootstrap work queue (2026-07-21; superseded 2026-07-24)

**2026-08-02: milestone B1 (b67 caching) DONE —
`board/bootstrap-67-w4b-cert-bridge-caching.md` (completion record).**
Cert + bridge content-keyed caching landed (D1–D5): cert writers
content-compare (byte-identical re-emissions keep mtime); per-cert
bridge pass markers (`Bridge_<leaf>.verified`, keyed on module text +
core-olean hash + toolchain + emitter fingerprints, island-marker
discipline); `emitter_fingerprint()` closes P3(b) — the `-V cache`
base now keys the emitter/closer binary. **Flip target MET: warm
tactus-core gate + bridge = 35s vs 34.7s baseline (~1.4%), all 166
obligations cache-served; cold+bridge 10m35s.** probe11's stale `-V
cache` mechanism note corrected (empirical: the tactus route never
consults the Z3 verdict cache). Battery: units 432+7/0, gate 291/0 +
54 + discharge 198/0, probes 9/11/13/14/17/37/38 ✓, e2e 829/2,
golden byte-stable. Findings on the card: tgt runtime-module gate is
currently RED under the worktree binary (pre-existing drift, NOT
b67 — in-gate bridge has no tgt subject today; probe11's external
path stays the tgt lane), and on-disk cert hand-edits don't red the
bridge (re-emission overwrites; the red channel is emission-side
drift, which flips marker keys by construction). b68's full-crate tgt
acceptance run REMOVED (Danielle 2026-08-01: scoped probe11 census
is the A-coverage path).
**NEXT: B2 = b68 (the bridge default flip —
`board/bootstrap-68-w4c-bridge-default-flip.md`). Gate conditions
status: P3(b) DONE + cost story DONE (b67); remaining = the flip
itself + red-path e2e pin + trust-inventory gate line + P2
(hoist-mixed-shadow MIX detector confirm-loud) + P3(a) stmts-olean
staleness fix + regen pin.** Then milestone E (W8 authority flip +
trust shrink — the N2 `branch_isvariant_of` detector is the last
named trusted predicate on the cert path).

**2026-07-31 late pm: stage 2 (F4 poison derivation) LANDED, both
eras, one session — completion record on the b80 card.** The poison
mark is DERIVED reference-side now (`poisoned_props(c)` over
`FnCtxData.residue_names` + the new `prop_deeps` side table) and the
carried bit slots are DELETED from the vocabulary (FHyp 4→3; Assert
4→3 / Assume 3→2 / AQT 4→3 / If 7→6 / IfCtor −2 / Loop 21→20).
`hyp_poison`/`lexpr_mentions_var` retired from the cert path (they
stay only as the forced-state mirror + emission-time guards); the N2
IsVariant detector is now the LAST named trusted predicate on the
cert path (next trust-shrink target after B). The A4 cross-check era
validated derivation ≡ bit corpus-wide (probe9 33/33 + probe11 11/11
ALL CLASSIFIED with derivation-driven assembly) BEFORE deletion.
probe13's poison kills re-pointed at the derivation INPUTS
(`poison_residue_drop` / `poison_deep_drop`, both flip 1→0; the old
zero-the-bits `poison_flip` was dead-on-arrival under derivation-driven
assembly — the review's "(not before)" note was wrong about that).
Design review landed FIRST (card addendum): the freeze validated +
the `poisoned_props`-precompute refinement (one threaded param, one
derivation site). Surprises along the way: the discharge's
feed_requires needed the pp-first arg layout (+ unit pins);
`poisoned_props` takes the WHOLE FnCtxData (wf-transport can't do
`<param>.<field>` projections); find_cancellation_exec's
`hastype-range`-uncoverable prop needed the bit-gated dummy-deep
fallback. Battery: gate 291/0 + pkg gate 54 + discharge 198/0,
probes 9/11/13(22 classes)/14/17/37/38 ✓, units 428+7/0, golden
re-vendored (era 2). probe20 stays deferred (no tgt gates).
**NEXT: milestone B (b67 caching + b68 flip — the endgame's 4 gate
conditions: P2 census-honest, P3 stmts-olean staleness fix +
emitter-binary cache fingerprint).**

**2026-07-31 pm: A7 scope items 1+3 DONE —
`board/bootstrap-80-a7-callee-signature-vocab.md` (completion record).**
probe9 ALL 33 CLOSE (zero honest-fails corpus-wide), probe11 ALL 11 tgt
CLOSE (scoped regen only — no tgt gate). THREE landings: (1) the
callee-signature vocab (RawList per-arg expected typs + reconcile_arg
two-phase slot reconciliation + RefMk/BoxMk id-free nodes); (2) F5
PULLED FORWARD — vec_read's residual was production's bound predicates
running on the UNINSTANTIATED declared typ (generic callees silently
lost bound hyps; instantiate_callee_typ, 4 production sites + Phase-1
serializer mirror); (3) Assign-rhs `into_slot(dest_typ)` (walk_let's
coercion — find_cancellation's `tmp__6 = w.deref`, masked inside the
A7-class attribution). probe13 → 21 classes (expected-typ kill; Loop
classes full-strength), probe38 tripwire fired→close+kill, probe17
de-staled (pre-existing, pinned-prelude), probe37 RefMk/BoxMk arms,
units 428+7/0, golden byte-stable, gate 286/0 + discharge 198/0.
probe20 deferred (vendored old-shape tgt defcerts; needs the tgt-slice
re-emit, deferred under the no-tgt-gates constraint).
**NEXT: stage 2 = scope item 2 (F4 poison derivation — residue_names +
prop_deeps side table, derive wrap-forcing + FLetH collapse
reference-side, delete the bit after the cross-check era, re-point
probe13 poison_flip; impl-time checklist on the card) → B (b67 caching
+ b68 flip).**

**2026-07-28: b79 (break-form loop arm) DONE — see
`board/bootstrap-79-break-form-loop-arm.md` (full record).** The
loop_normalize coverage regression is closed: `StmData::Loop` gains
`setup`/`inv_obligs_break`/`neg_neg_cond_ann`/`break_guard_ann`/
`break_use_ann` (arity 16→21), refWp derives the THREE invariant goal
families from ONE setup transcription, `wp_stm_sound` covers both loop
forms (285/0 + package gate green), and the Link discharge gained the
assert-VC composer arm (**198/0-pending**). copy_word +
find_cancellation_exec certs RETURN (call-mut + break-or-continue
census populations 0 on tgt — b78 S5 acceptance); all three
break-form subjects are A7-class honest-fails (frame assembly
byte-perfect; they close when A7 lands). probe9/11/13/14/37/38 all
green (probe13 → 20 classes). **NEXT per the endgame map: b78 S5
proper is DISCHARGED (its acceptance was the loop arm) → A7 (stage-B
callee-signature vocab — closes vec_read, vec_push7, fill_zeros,
count_to_len, copy_word, find_cancellation_exec) → B (b67 caching +
b68 flip).**

**2026-07-24 evening: endgame rows 5+6 (A3+A5+R1 batch) LANDED —
`board/bootstrap-77-a3a5r1-batch-churn.md`.** tactus-core 254/0 +
discharge 172/0; probe9 all-green (head_exec CLOSES via IfCtor);
probe11 all-classified (find_cancellation = the vec_read/A7 stage-B
class); `assert-query-tactus` census tag retired; probes 13/14/37/38 +
units green. **b77 mutation kills DONE 2026-07-24 (follow-up session,
+ review round): probe13 now 10 classes (`take_sexpr` splitter; four
IfCtor kills = one per N2 frame-assembly output channel
eq/binders/neg/arm-swap, + `aqt_hyp_drop`), all baselines =1 + kills
=0; N2-detector cross-check pin wired into the serializer header
contract per-channel, honest residue named (peel decision + IfCtor
poison bits). Deviations on the b77 card: eq_drop uses the 999999
sentinel (no True leaf interned); binder/neg kills added in review
after catching my own contract overstatement.** Remaining endgame order: **A4
(call-mut, IN PROGRESS — card `board/bootstrap-78-a4-call-mut.md`,
design frozen from step-0 evidence; S1 counter mirror DONE 2026-07-25
`5ddbebb`, byte-neutral + battery green; S1 review round `a5e0917` =
emission-time cross-check, found 3 real table bugs; **S1b DONE
2026-07-25: both card hypotheses were WRONG — count_down+clamped_inc =
the block() join-desugar reuses the continuation term while production
clones `after` into both branch Wps (fix: record + replay the
continuation's theorem consumption after the else branch, gensym-
carrying continuations reject `call-in-branch-join`); mul_bound = the
NL query's Done(True) `_tactus_ensures_` theorem row. Certified 32/37
(3 restored, 0 drift), 29 certs byte-identical, probe9 all-green incl.
the 3 restored, probes 13/14/37/38 + units 406+7/0 green**; **S2 DONE
same day: FnCtxData `mut_params` churn landed** (MutParamList Dt +
mut_preamble_frame two-plain-FLet derivation — mut-param fns are
WRAP-MODE via hoist_all's typ-less-let bail, base binders survive;
slot 3 = deref VALUE leaf not inner-typ, at-impl D2 amendment; .mk
arity 7; 17 vendored pins bumped + probe37 wf-projection +1 + golden
re-vendored + probe20 de-staled). Battery: core gate 256/0 +
discharge 172/0, emission 32/37 ctx-only diffs, probes
9/11/13/14/20/37/38 + units all green. **S3 DONE 2026-07-26
(`8896532`+`79ddaae`, card §3 has the full story): SOUNDNESS FIX
first — collect_modifications missed loop-body call writes (mut-call
targets AND call dests; false ensures verified, confirmed live,
2 e2e pins) — then the mut-call frame arm: call_inc + inc
BRIDGE-CLOSE, call-mut tag retired from the fixture census (36/39),
fill_zeros `_5/_6` spine byte-match, ensures-phase mut-rewrite gap
found+fixed via the inc pinpoint. vec_push7 + fill_zeros =
documented A7-class honest-fails (frame spines match production
node-for-node; deep-leaf `view (Tactus.Ref.mk v)` divergence);
fill_zeros also exercises the b77 leading-hyp wrap divergence —
S3-pre brick spec'd on the card (retire `_h_ctx` → `_h_hoist_k` +
close_e_wrap leading latch, zero user references in corpus).
Battery: units 425+7/0, e2e 558/0 (+2 soundness pins), probes
9/11/13/14/20/37/38 green.** **S4 kills DONE 2026-07-26 (probe13 →
15 classes). S3-pre DONE 2026-07-26 (full record on the b78 card):
`_h_ctx` retired — production split_leading_binders = pure prefix
latch naming `_h_hoist_k`, refWp close_e_wrap_lead/close_sem twins
with one-way let-latch, serializer needed ZERO changes (per-goal
positions == walk ordinals); gate 283/0 + discharge 196/0, probe9
23/26 CLOSE (add_capped/proof_block_fn close with reshaped certs;
fill_zeros hfail narrowed to A7-only), probes 13/14/37/38 green,
golden re-vendored.** **S5 RUN 2026-07-28 —
BLOCKED (full record on the b78 card §5): the 4th-sync loop_normalize
pre-pass rewrites call-in-cond whiles to break-form; copy_word AND
find_cancellation_exec now census-reject `break-or-continue` before
the Call arm (find_cancellation LOST its b77-era cert = tgt coverage
regression the stale-on-disk certs had masked). probe11 regen: 9/9
remaining certs CLOSE + new subject-population pin keeps the 2
absences loud. NEXT = break-form loop arm — card
`board/bootstrap-79-break-form-loop-arm.md` (step-0 frozen: the
break-form has THREE invariant phases vs classical TWO; exit side
hoists setup+¬cond, maintain wraps inline; design = NO Break arm,
mirror at original_cond level, Loop-node vocab growth; Danielle
sequenced it before A7) → S5 proper → A7
(stage-B callee-signature vocab — closes vec_read, vec_push7,
fill_zeros AND find_cancellation, derives poison + N2 detector
reference-side) → B (b67 caching + b68 flip)**. D's in-model
tripwire column landed with b77.

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
