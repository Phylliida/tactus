---
title: "finding-3 follow-up — nested-loop _h_ctx counter (find_square bridge)"
status: done
claimed_by: opus-b16
created: 2026-07-14T09:35:00Z
updated: 2026-07-14T12:15:00Z
---

## Description

finding-3 (bootstrap-15) landed the loop-binder serializer and closed the
single-loop `sum_to` bridge by `decide`. The NESTED-loop fixture
`find_square` (2 loops) honest-fails (`goals_eq`→0) — a documented stage-A
caveat, fail-loud not silent-pass. This task closes that gap (a stretch
goal, only if it's worth the scope).

**Root cause.** The serializer's `loop_stm`
(`source/lean_verify/src/sst_serialize.rs`) resets `hyp_counter = 0` per
loop when minting `_h_ctx_N` names. But production's
`OblCtx::split_leading_binders` (`sst_to_lean.rs:1510`) counts from 0 over
the FULL accumulated `obl.frames` at each obligation — and for an INNER
loop the OUTER loop's mod-var ∀-binders + their bound/invariant/cond hyps
are STILL in scope (pushed by the outer `push_mod_var_frames` and never
popped). So the inner loop's leading hyps get `_h_ctx_<outer_hyp_count + k>`
in production, while the serializer emits `_h_ctx_k`. The binder-NAME ids
diverge → `goal_eq` (which compares name ids) → `goals_eq` = 0.

Likely also needs: multi-level `decreases` support (currently rejected via
`loop-multilevel-decrease`) if any nested fixture uses a lex measure, and
the refWp spec side may need to model the accumulated-frame counter too
(check whether the spec `wp_stm` Loop telescope already threads outer
binders — it does via the recursive `frame_after`/`f`, but the `_h_ctx`
NAMES are baked into the SST literal by the serializer, so this is
primarily a serializer-side counter fix).

## Approach sketch

- Thread an INCOMING `hyp_counter` base into `loop_stm` (the count of
  leading hyp frames already in scope from enclosing loops), rather than
  resetting to 0. The outer loop, when recursing into `self.stm(body)` for
  a body that contains an inner loop, must know how many of its own
  binders/hyps precede — i.e. pass down `mod-vars-with-bounds + invs + cond`
  hyp count. Care: the counter is per-OBLIGATION in production
  (split_leading_binders runs at each emit), but for a well-nested loop the
  leading-frame structure is the same at every inner obligation, so a
  static "outer hyp depth" carried through the recursion should match.
- Validate: `goals_eq (ref_wp cert_find_square_ctx cert_find_square_sst)
  cert_find_square_goals = 1 := by decide` closes (LEAN_PATH =
  tactus-core/out/lib + prelude-cache); negative-control a leaf.
- Regen recipe + prelude/LEAN_PATH details: see bootstrap-15 Progress.

## Progress
- (2026-07-14) Split out of bootstrap-15 as a documented stretch caveat.
- (2026-07-14, opus-b16) **NESTED-LOOP TELESCOPE FIX LANDED + VALIDATED
  end-to-end against the real find_square cert (refWp-only, NO serializer
  change, NO regen).** Corrected the prior diagnosis, implemented the fix,
  isolated it with real data, and spun out the remaining gap (bootstrap-17).

  **Diagnosis correction (the prior "counter offset" read was imprecise).**
  Decoded the on-disk `bootstrap-fixture/out/lib/cert/find_square.cert.lean`
  goals directly. The inner loop's maintain telescope (goal 5) is
  `∀b (All 23 1), Imp 24, Imp 25, Imp 26, Imp 27, Imp 29` — the mod-var
  bound + three invs + cond render as **bare unnamed `Imp`s**, NOT as
  `_h_ctx`-named `All`s with a shifted counter. Root cause:
  `split_leading_binders` (sst_to_lean:1510) hoists a prefix of Binder/Hyp
  frames from the FRONT and STOPS at the first `Let`. An enclosing loop
  pushes a `_tactus_d_old := D` `Let` frame (walk_loop:2451), so the inner
  loop's hyps come AFTER that `Let` → not leading → rendered `Imp`. The
  inner mod-var ∀-binder (`b`) still renders `All` (keeps its source name).

  **Fix (tactus-core/lib.rs only, verified 40/0 under the package gate).**
  refWp re-derives "leading-ness" from the pre-loop frame `f`: LEADING iff
  no `Let` survives `havoc_lets(f, binders)` (the modified locals' own
  pre-loop lets are havoc'd; a surviving `Let` = an enclosing loop's
  `_tactus_d_old`). New helpers `has_let`, `binderprops_to_hyps`,
  `seed_binders_hyp_bounds`, and the branch drivers `loop_maintain_frame`
  / `loop_use_frame` (top-level fns, not nested `if`/`match` in `wp_stm`'s
  arm — decide-checker flattening caveat). `wp_stm` Loop + `frame_after`
  Loop now call these. Leading loops (sum_to, find_square OUTER) keep the
  finding-3 NAMED-∀ path unchanged; nested loops (find_square INNER) get
  bare `Imp`s. **The serializer already emits the right prop leaves** (the
  inner Loop node's `binder_bounds`/`inv_hyps`/`cond_ann` prop slots) —
  refWp simply stopped using the (interned, now-ignored) `_h_ctx` name
  slots for a nested loop. So NO serializer change and NO vargo regen: the
  fix validates against the already-emitted cert.

  **End-to-end validation (real find_square cert, per-goal bridge
  `/tmp/b16-bridge/BridgeFindSquare.lean`, LEAN_PATH = tactus-core/out/lib
  + ~/.cache/tactus/prelude-e81fbf9a86375c12):**
  - `goal_count (ref_wp ctx sst) = 17` ✓ (same multiplicity as production).
  - Goals **0–5 close** (`goal_eq … = 1 := by decide`): outer init, inner
    init, inner assert — the maintain telescope (incl. the nested `Imp`s).
  - Goals **12–16 close**: the continuation AFTER the inner loop, through
    the USE telescope (`loop_use_frame` non-leading `Imp`s + `¬cond`).
  - Goals **6–11 honest-fail** (`goal_eq = 0`): the ONLY remaining
    divergence, all downstream of the inner `if a*b==36 { return a }` —
    the if-in-fall-through case DESIGN §2.4.1 excluded. Spun out as
    **bootstrap-17** (root cause + leaf ids decoded there).
  - Mutation-kill baked in: the permanent `decide` test
    `ref_wp_nested_loop_nonleading` (lib.rs) asserts the SAME loop node
    renders bare `Imp`s under a `Let`-bearing front frame and NAMED `All`s
    under a `Let`-free one — a leading↔non-leading flip changes every inner
    `Imp`↔`All`, so `goal_eq` flips. Uses find_square's real inner-loop
    leaf ids.

  find_square does NOT fully bridge yet (goals 6–11 need bootstrap-17), but
  the titled nested-loop telescope gap is closed, validated with real data,
  and sound (structural `goal_eq` — any divergence honest-fails).

## Writeup

**Nested-loop (non-leading) telescope — DONE + VALIDATED (refWp-only).**

### What the bug actually was

A NESTED loop's mod-var bounds / invariants / condition render in the
production goal as bare (unnamed) `Imp` hypotheses, while a LEADING (top-
level) loop's render as NAMED `_h_ctx_N` ∀-hyps. The distinction is made
by `OblCtx::split_leading_binders` (sst_to_lean:1510), which hoists a
front prefix of Binder/Hyp frames to named `All`s and STOPS at the first
`Let`. An enclosing loop pushes a `_tactus_d_old := D` `Let` (walk_loop),
so the inner loop's frames are past that `Let` → not hoisted → unnamed
`Imp`. The finding-3 refWp baked ALL loop hyps as `FBind` (→ `All`),
correct only for a leading loop. (The task's premise — a `_h_ctx` COUNTER
offset — was imprecise: the inner hyps are UNNAMED, not renamed.)

### The fix (tactus-core/lib.rs)

refWp re-derives leading-ness from the pre-loop frame:
- `has_let(f)` — is there a surviving `Let`? (nat, decide idiom.)
- `loop_maintain_frame` / `loop_use_frame` — build the loop telescope,
  choosing NAMED (`seed_params` + `binders_to_frame` + `FBind` cond) when
  `has_let(havoc_lets(f, binders)) == 0`, else UNNAMED
  (`seed_binders_hyp_bounds` — binder `FBind`, bound `FHyp` — +
  `binderprops_to_hyps` + `FHyp` cond). The mod-var ∀-binders stay `FBind`
  either way; only their bounds/invs/cond flip.
- `wp_stm`/`frame_after` Loop arms call these instead of the inline
  finding-3 telescope.

No StmData shape change, no serializer change, no vargo regen — the
serializer already emits the annotated invariant/bound/cond obligation
leaves in the loop node's prop slots; the fix only stops refWp from
consuming the `_h_ctx` NAME slots when the loop is nested.

### Assumptions / caveats

- **Leading-ness = "no surviving `let` in front."** This is the exact
  `split_leading_binders` stop condition for the loop case (the only stop
  triggers in-scope are the enclosing `_tactus_d_old` lets and any pre-loop
  non-modified `let`). The OTHER `split_leading_binders` stop — a `Hyp`
  before any `Binder` — is not modeled (no fixture has a pre-loop
  assume/assert before a top-level loop). A fixture that did would
  honest-fail, never silent-pass (`goal_eq` is structural).
- **find_square is NOT fully closed** — goals 6–11 (if-in-fall-through,
  §2.4.1) remain, tracked as **bootstrap-17**. Goals 0–5 + 12–16 close.
- Validated with the real cert (already on disk) — no regen was needed, so
  the fixture certs and golden add_capped/sum_to are untouched. `out/lib`
  re-emitted (fix + new test), re-verified 40/0.
