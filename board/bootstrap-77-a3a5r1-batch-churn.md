---
title: "A3+A5+R1 batched tactus-core churn — AssertQueryTactus + IfCtor fork + FUserCloser frame"
status: done
claimed_by:
created: 2026-07-24T00:00:00Z
updated: 2026-07-24T00:00:00Z
---

## Description

The endgame §8 rows 5+6 batch: one cache-churning tactus-core vocabulary
edit covering A3 (Tactus-mode assert-query, card bootstrap-69's residue),
A5 (the head_exec match-split), and R1 (per-goal closer wrap modeling),
plus the R4 serializer tidy. Q1 resolved the A3 variant question
(first-class, not Assume-with-mark); this card records the step-0
emission evidence and the design corrections it forced.

## Step-0 evidence (frozen 2026-07-24, cold emissions, binary @ 8e7696d)

Probe file: scratchpad `fork_probe.rs` (probe_if_ret / probe_if_assign /
probe_match_assign); tgt emissions for the 5 `assert-query-tactus` fns
(todd_coxeter_rt.symbol_to_column_exec, todd_coxeter_rt.inverse_column_exec,
runtime.is_inverse_pair_exec, runtime.find_cancellation_exec,
runtime.apply_hom_symbol_exec — census is FIVE, the endgame doc's "4" was
stale); fresh fixture certs (probe9 18/20 baseline re-confirmed).

**E1 — the fork gate.** `walk_let` forks a value-if ONLY when the if is
at the SPINE of the walked value: probe_if_ret (return-position plain
if, default fn) → 4 goals (2 ens × 2 branches, per-branch
`_h_hoist_1 : x < y` + `r = y` FLetH pairs); probe_if_assign
(`let m = if …; m`) → 2 goals, if OPAQUE inside `_h_m_hoist1 : m = (if …)`.
Reason: the raw SST for the assign form has NO Assign statement — the
body folds into `Return(Bind(Let(m := If …), Var m))`, and walk_let's
Bind arm pushes binder RHSs as opaque rendered lets (no recursion into
them for ifs); only the If arm (spine position) forks. head_exec's SST
is `[Assign(tmp__, t), Return(If(isLeaf, Bind(Let v, v), Bind(..., 0)))]`
→ spine fork + per-branch Bind-peel = the observed per-arm goals.

**E2 — N2 upgrade scope.** `branch_ctor_frames` upgrades the POSITIVE
branch hyp to field binders + `scrut = Dt.Variant fs` (CtorEq) iff:
default-closer obligation scope, positive IsVariant on a plain-Var
scrutinee, dt in krate map, multi-variant, typ args exposed. Negative
branches always keep plain `¬cond`. Wrapper decorations add `.deref` on
the equation LHS.

**E3 — assert-by EMITS A GOAL (endgame §A3 text corrected).** The A3
description said "no separate goal, P enters as hyp" — WRONG for the
assert-by kind. `walk_assert_by_tactus(Some(P))` emits one
`_tactus_assert_*` theorem for span-marked P (closer = generated intro
spine + the user's verbatim tactic; `emit_with_closer` NEVER hoists —
leading-binder split + wrap always), THEN pushes bare P as an
`AssertFact` hyp for the continuation. So the mirror arm is
ASSERT-shaped (goal + forward hyp), with the goal force-wrapped. The
proof-block kind (`cond = None`) emits nothing structural: the tactic
goes onto `e.tactic_prefix`, composed into closers AFTER the hoist
decision — per-obligation shape unaffected.

**E4 — but the proof block flips the FN-LEVEL gate.** *(AMENDED by the
Progress triage: the fn-level DFS gates the RETURN ROUTE only — per-goal
hoisting follows the ATTR alone; "all 5 fns are wrap-mode" below is the
pre-correction framing. See Progress item 1 and the two-bit split.)* A2's
`closer_is_default(fn)` DFS counts proof-block prefixes: a fn containing
`proof { tac }` routes Return via the LEGACY `Done(let ret := e; …)`
path (no fork, goal wraps — is_inverse_pair_exec's observed single
wrapped goal with the whole tuple-match value-if inside). All 5 tgt
assert-query-tactus fns are wrap-mode by attr and/or proof block. The
force-wrap bit matters for the DEFAULT-fn assert-by case (fixture to
be added — no tgt instance today).

**E5 — G4 stale-fold latent divergence.** The serializer's G4
impl-fold (`Ret([impl…], RetNone)`) mirrors `lift_if_value_coerced`,
which since the Return→Wp::Let route only runs for NON-default fns.
For probe_if_ret (default) G4 fired and produced a cert whose goals
diverge from production's forked goals (honest-fail, but an
unclassified one — P2 debt). Fix in this arc: G4 only on the legacy
route; default route gets the fork mirror.

## Design (agreed shape)

**R1 — `FrameList::FUserCloser` sentinel** (not a wp_stm mode param):
a frame entry that (a) trips `gate_wrap` (new `has_user_closer`
conjunct), (b) is skipped by every renderer/semantic walker (close_e_wrap,
close_e_tel, residue_fold_e, close_sem_*, holds family — FNil-like
pass-through), (c) is STRIPPED by `strip_hyps` (production's
`OblCtx::new_scope` drops hyps AND resets the closer at the same point
— the NL-scope-inside-user-fn mix hoists again, the R1 finding).
Serializer: seed it from `fn_closer_is_default` via a new
`FnCtxData.closer_default: u64` + `seed_frame` conditional; RETIRE the
wrap_mode all-lets-plain collapse (honest AssignH/AssignR classification
everywhere; wrap rendering of FLetH/FLetR == FLet, so goals are
byte-identical — probe11 must stay 3/3 CLOSE).

**A3 — `StmData::AssertQueryTactus(RawExp, u64, u64, u64)`**
(annotated P obligation, hyp name leaf, bare P leaf, poison):
wp = ONE goal `close_e(frame_append(f, FUserCloser), ob)` (the
always-wrap emit_with_closer mirror); frame_after = `f + FHyp(bare P)`
(AssertFact). The PROOF-BLOCK kind emits NO node (structurally absent
— nothing is assumed, nothing proven inline; the prefix only reshapes
closers, which stage A does not certify) — the fn-level gate (E4)
already routes such fns to wrap mode. Census: the fns then serialize;
`assert-query-tactus` tag retires. Soundness: Assert-arm analogue.

**A5 — `StmData::IfCtor`** (NOT a Match node — production has no Match
either; the construct is "If whose positive branch hyp is
ctor-upgraded", and it applies to hand-written `if t.is_leaf()` too):
fields = pos field binders (`BinderList`), eq name/prop/poison, neg
name/prop/poison, then/else bodies. wp: then under
`f ++ binders_to_frame(pos) ++ FHyp(eq)`, else under `f ++ FHyp(neg)`;
frame_after mirrors If's diverge/skip logic. Plain-cond forks NEED NO
NEW VOCABULARY — StmData::If with per-branch `Seq(assigns…, Ret(ens,
RetLetH(r, branch-val)))` already renders production's fork shape.
Serializer: mirror walk_let on the default Return route — peel
Bind-chains to assign terms (exists: peel_terms), then a spine If forks
into per-branch trees (recursive: branch exps peel their own Bind-chains,
nested ifs nest); N2 gate mirror picks IfCtor vs If per branch cond.
Multi-variant matches = nested else-if chains, compositional.

**R4** — stop interning unused `_h_hoist_i` name leaves in wrap-mode
certs (touching the serializer anyway).

**D discipline**: both new StmData arms enter `wp_stm_sound` (IfCtor =
If-arm analogue — ctor-eq is an opaque hyp leaf under the oracle
model; AssertQueryTactus = Assert-arm analogue) + the
bootstrap_coverage in-model column.

## Follow-ups (small, tracked — not blockers)

* **FULL tgt gate with the bootstrap binary — DROPPED (Danielle's
  call, 2026-07-24: not needed, ever — tgt's real gate runs with the
  MAIN binary via its check.sh, and the wf-sig change gets its tgt
  exposure at the next bootstrap→main sync anyway; the attempted run
  also OOM'd the machine under session load).** For the record from
  the killed partial run: `TactusDefs_lib_exec__word_numbering` failed
  ("simp_all made no progress" ×4 in a decreasing_by) before the OOM —
  unattributed, defs emission untouched by b77; only relevant if a
  future sync surfaces the same signature.
* **Review-round fixes LANDED (2026-07-24 late-late):** N2 shared
  detector named as the SECOND trusted predicate in the serializer
  header contract (reference-side derivation rides A7; cross-check
  pin rides the mutation kills); `closer_default` doc in tactus-core
  AMENDED to attr-only (+ E4 amendment marker above); step-0 fork
  probe VENDORED as `probe-w0/probe39_b77_fork_gate/`; the
  `default_route` gate simplified to production's exact two
  conditions after PROVING the lname coupling (both map off the same
  `post_condition.dest` Option) — probe9 re-pinned all-green on the
  rebuilt binary.

* **Mutation-kill classes for the NEW arms — DONE 2026-07-24 (follow-up
  session).** All three classes landed in probe13 `gen.py` per the plan
  below + `take_sexpr` splitter; suite = 8 classes, all baselines =1 +
  kills =0, lean rc=0. ONE deviation: `ifctor_eq_drop` rewrites eq_prop
  to the 999999 SENTINEL (wrong_field precedent), not "the interned True
  leaf id" — head_exec's cert interns NO True leaf (the recipe
  misremembered); `goals_eq` kills on id-divergence either way. N2
  cross-check pin wired: serializer header contract now cites
  `ifctor_eq_drop`/`ifctor_arm_swap` as the live assembled-frames pin
  (also fixed `mut_poison`→`poison_flip` name drift there); README +
  CLASSES comments carry the shared-decision-vs-independent-assembly
  scoping. Original plan (for the record):
  1. Add a bracket-aware term splitter (`take_sexpr(s, i)` — scan from
     an offset, balance parens, return the span) so a ctor's
     positional args are addressable without regex fragility.
  2. `ifctor_eq_drop` (head_exec, sst-side): locate
     `lib.StmData.IfCtor`, take_sexpr the pos_binders group, then
     rewrite the following `eq_prop` scalar to the interned `True`
     leaf id — the ctor-equation hyp text diverges → bridge must flip
     1→0.
  3. `ifctor_arm_swap` (head_exec, sst-side): take_sexpr the two
     trailing `(Tactus.Box.mk …)` groups (thn/els) and swap them —
     per-arm goals emit in the wrong order → flip.
  4. `aqt_hyp_drop` (assert_by_default, sst-side): locate
     `lib.StmData.AssertQueryTactus`, rewrite its bare-hyp scalar
     (2nd-from-last arg) to 0 — the continuation goals lose the
     AssertFact hyp → flip.
  Each keeps the standard baseline `= 1` + kill `= 0` pair. ALSO wire
  the N2-detector cross-check here (the header-contract's second
  trusted predicate): the arm-structure kills pin the assembled
  frames while the detector remains shared.
* **R4 resolved by construction**: with honest classification the
  FLetH eq/name leaves in wrap-mode certs are load-bearing SST data
  (not unused interned noise) — no tidy needed; noted for the record.
* **Statement-If IsVariant N2 upgrade** (pre-existing, unexercised):
  production's `Wp::Branch` walker ALSO ctor-upgrades statement-level
  `if x.is_v()` tests in default scopes; the serializer's StmX::If arm
  emits plain cond hyps. No corpus fn hits it (matches lower to
  return-position value-ifs). Would honest-fail loudly if one appears;
  wire the shared `ctor_fork_frames` into the If/block-desugar arms
  then.

## Known residue (documented, not solved here)

* Leading-position Hyp in a WRAP-mode goal: production's
  `split_leading_binders` extracts post-binder Hyps as NAMED `_h_ctx_N`
  binders; mirror wrap renders FHyp → anonymous Imp. Unexercised by the
  corpus (first post-seed frame is always a let so far) — same latent
  gap as A2's landed wrap mode, now written down.
* is_inverse_pair's TUPLE let (`tmp__ := (s1, s2)`) is a typ-less/
  LetRaw-class frame → wrap-forces its goal via the EXISTING plain-FLet
  gate; no new machinery.
* find_cancellation_exec may hit further tags after the arm lands
  (loops + in-loop assert-by); classify loudly, don't chase in this arc.

## Acceptance

* tactus-core package gate green + Link discharge 0-pending (R-c
  machinery expected to absorb; verify).
* probe9: head_exec CLOSES; 19/20 (vec_read stays the one stage-B
  honest-fail); max_u64/probe shapes keep closing.
* probe11: 3/3 CLOSE unchanged (wrap_mode retirement is render-neutral).
* New fixture fns: return-position plain fork (probe_if_ret shape),
  assert-by-in-default-fn (force-wrap bit exercised), proof-block fn,
  match-in-assign (opaque — must NOT fork). Mutation kills on IfCtor
  (drop ctor-eq / swap arms) and AssertQueryTactus (drop hyp).
* tgt: `assert-query-tactus` census 5 → 0; the 5 fns emit certs that
  bridge-close or carry sharp new tags with written reasons.
* e2e suite + lean_verify units green; no assume-warnings from the new
  arm.

## Progress

- (2026-07-24) Step-0 evidence complete (E1–E5 above); design agreed
  per endgame Q1/R1 under Danielle's standing no-half-measures
  guidance. The two endgame-doc corrections (assert-by HAS a goal;
  Match-node reframed as IfCtor) recorded here.
- (2026-07-24) **tactus-core churn LANDED (`a0c9423`): gate 254/0.**
  FUserCloser (all 23 frame-walker arms + 12 u_* pin families + weave
  lemmas), AssertQueryTactus + IfCtor (wp/esf/frame_after/size/diverges
  + wp_stm_sound arms — model total, D column holds), FnCtxData.closer_default
  + seed_frame conditional. GOTCHA that cost a round: IfCtor field
  `then` is a Lean KEYWORD → defs module failed to elaborate → whole
  crate island-fallback whose surface error ("invalid 'import'
  command", 172 reds) pointed nowhere near the cause. Renamed `thn`.
  One straight-line proof (closure_forwards_contract) needed the new
  u_gateu_* pins (its closer delta-unfolds gate_wrap).
  RESIDUE: Link discharge 171/1 — seed_frame_wf stopped synthesizing
  ("no wf source for `c.typ_params`" — c classified non-Dt), under
  investigation with a WFDEBUG probe.
- (2026-07-24 late) **E2E: main suite green; the examples binary has 2
  PRE-EXISTING reds** (`examples_state_machines_flat_combine`,
  `examples_state_machines_tutorial_fifo` — Z3-side "inherent safety
  condition" deposit/withdraw failures). ATTRIBUTED by reverting
  lean_verify to pre-b77 (`8e7696d`) and rebuilding: they fail there
  too — not this arc's. Deterministic, so not load flake either;
  worth an independent look (vstd/toolchain drift from earlier main
  merges is the suspect class). All other suites 0-fail.
- (2026-07-24 evening) **TRIAGE COMPLETE — probe9 all-green (23/24
  close, vec_read the lone stage-B hfail), probe11 ALL-CLASSIFIED
  (9/10 close), probes 13/14/37/38 PASS, units 406/0+7/0.** The tgt
  user-closer class forced FIVE post-landing corrections, each
  evidence-driven:
  1. **Two-bit split** (proof_block_fn goal-0 evidence): the fn-level
     `closer_is_default` DFS gates the RETURN ROUTE only; per-goal
     hoisting follows `obl.closer` = the ATTR alone. FUserCloser
     seeding/freshening/loop-reject now key on `attr_user_closer`;
     G4/fork/RetLetH on route-level `wrap_mode`.
  2. **Nested-Block flatten** in `block()` (inverse_column 4-vs-5
     goals): a `proof { }` scope nests a Block whose tail If must see
     the OUTER continuation for the two-way-join desugar — production
     threads continuations through block boundaries transparently.
  3. **Legacy-route peel gate** (is_inverse_pair extra Let):
     `lift_if_value`'s Bind arm keeps the whole `let tmp__ := …; if …`
     chain inside the RetLet leaf — the Bind-peel is a default-route
     mirror only.
  4. **Binder-aware hyp renders** (apply_hom_symbol `s` vs `s.deref`):
     Assert / Assume / AssertQueryTactus forward hyps all render
     through `render_ctx().with_let_binder_typs` (the bootstrap-18
     class, latent in the plain arms until a `&`-param assert showed).
  5. **find_cancellation_exec = the vec_read stage-B class**, newly
     visible now that it serializes: stage-A assembly matches (21
     goals, spines align); the divergence is deep-leaf only
     (`FieldProj .deref` on a View-call arg). Classified honest-fail
     in probe11 pointing at A7.
  probe13's parked A5 tripwire FIRED AS DESIGNED → deref class
  restored to close+kill. probe14/probe37 vendored pins updated for
  the 6-arg FnCtxData.mk / the closed theorem's new `h_c_bound`
  binder (fed from FnCtxDataWf's final conjunct).
- (2026-07-24) Serializer side WRITTEN + compiled: honest let
  classification in wrap fns (wrap_mode collapse + wrap_guard +
  user-closer-hoistless + user-closer-assert-query all RETIRED),
  FnCtxData.mk 6th field, AssertQueryTactus arm (AssertBy = Assert-
  shaped node; ProofBlock = Skip), ret_fork + ctor_fork_frames (walk_let
  fork mirror + shared N2 detector `branch_isvariant_of` now
  pub(crate)), G4 impl-fold gated to the LEGACY route only (fixes the
  probe_if_ret-class silent divergence), ret_terminal extraction,
  stm_size_of new heads (`If ` trailing-space guard vs IfCtor).
  Fixtures added: pick_max (F22 plain fork), head_via_let (F23 no-fork
  negative control), assert_by_default (F24 R1 force-wrap), 
  proof_block_fn (F25 fn-level gate flip). bootstrap_coverage gains the
  in-model column (D tripwire). Validation pending.
