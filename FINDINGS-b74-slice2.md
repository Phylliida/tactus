# FINDINGS — bootstrap-74 slice 2: the bridge ↔ N1-hoist reconciliation

Status: **complete** (2026-07-21). Commits: step 0 `734711b`, Round A
`a2c40ad`, Round B `651b532`, Round C `4fdd7df`, Round D `ca8dd93`,
sweep `50256de`. Card: `board/bootstrap-74-bridge-n1-hoist-reconciliation.md`.
Plan doc: `DESIGN-b74-slice2-serializer.md` (with the step-0 evidence
table in its §2b/§2c).

## 0. What this was

Main's leaf-normal emission (N1 hoist, `8accb8d` + partial hoist
`8dcac64`) reshaped every goal production emits: hyps became named
theorem binders `(_h_hoist_i : P)`, spine lets became binder pairs
`(x : T) (_h_x_hoist1 : x = v)`, and Bool lets became goal-position
"residue" lets. Every fixture bridge honest-failed (13/13 CLOSE-BROKE)
because the frozen refWp mirror in tactus-core could not express the
new shapes. Slice 2 taught the model (tactus-core) and the serializer
(sst_serialize.rs) to reproduce them exactly, per goal, byte-for-byte.

## 1. Final state

- **probe9 (fixtures): 18/20 bridge-close** — every family: asserts/seq
  (add_capped — all three goal modes in one fn), call ret-eq
  (use_clamped, use_multiarg, clamped_inc, call_g2/g3_ob, quad_exec),
  if-join (count_down), assert-query (mul_bound), loops (sum_to,
  find_square), plus double_exec, id_generic, max_u64, mk_point,
  scope_shape, swap_pair, tri_one.
- **probe11 (tgt): `runtime__impl__4__clone` bridge-closes** — the
  differential gate's first real-corpus bridge subject.
- Both runners report **ALL BRIDGES BEHAVE AS CLASSIFIED ✓**; the six
  remaining failures are documented honest-fails with precise
  machinery reasons (§5).
- Gates: tactus-core 231/0 + package gate green, Link discharge 144/6
  steady (the 6 = pre-existing other-hyp/HoistEq residual, unchanged
  through the whole arc), e2e 551/0, lean_verify unit 400/0.

## 2. The core mechanism findings

These are the durable lessons — the things that are true about
production that any future mirror must respect.

### 2.1 Production has THREE goal modes, not two

The 2026-07-20 design ("all-or-nothing hoist") was already stale when
written: `8dcac64` (partial hoist, same day) made Bool lets fold as
goal-position residue lets around an otherwise-hoisted leaf. The full
discipline (`hoist_all`, sst_to_lean.rs:2073):

- **wrap** — any typ-less let, or any hoisted binder whose TYPE
  (hyp prop or let equation) mentions a residue name
  (`lexpr_mentions_var` bail check). Everything renders old-style
  (`Imp`/`Let`).
- **hoist** — every frame becomes a theorem binder: hyps named
  `(_h_hoist_i : P)` (1-based per-goal ordinal among Hyp frames),
  typed lets as pairs `(x : T) (_h_x_hoist1 : x = v)`.
- **hoist+residue** — Bool lets stay in goal position, folded around
  the leaf in frame order (earliest outermost).

add_capped exhibits all three in one fn (goal 0 pure hoist, goal 1
hoist+residue, goals 2–3 wrap — the asserted Bool temp `tmp__1` as a
hyp prop mentions the residue name → bail).

The model mirrors this with `FLetR` (residue let), an `FHyp` poison
field, and `gate_wrap = has_plain_flet || has_poisoned_hyp`.
**"Mentions residue" is a TEXT check and the model's leaves are opaque
ids — so the serializer computes the poison mark and the model's gate
reads it.** A poisoned hoistable let needs no variant: it collapses to
plain `FLet` losslessly (poison forces wrap; wrap mode discards the
hoist payload anyway).

### 2.2 The loop telescope is uniform

The leading/non-leading distinction (`_h_ctx_N`, `has_let` switch) is
DEAD in goal shapes (it survives only in the SST `Loop.inv_hyps`
side-table). Post-N1, maintain and use telescopes are flat
concatenation under one per-goal counter: havoc'd mod-vars as
`FBind(x : T) ∘ FHyp(_h_hoist_i : bound)`, named invariant hyps,
named cond hyp (with poison bit), and `_tactus_d_old_<id>_0` HOISTED
as an `FLetH` pair — not a plain `FLet`. Nested loops are the same
shape with the counter continuing (`find_square` goal 5: outer
`_h_hoist_1..4`, inner `_h_hoist_5..9`).

### 2.3 Hyp numbering is PER-GOAL-PATH, not a walk counter

`_h_hoist_i` is the 1-based ordinal of the Hyp frame within THAT
goal's frame prefix — production runs `hoist_all` per goal with a
fresh counter. Consequences:

- The If cond is `_h_hoist_{save+1}` in BOTH branches (each branch is
  a separate path); branch state (bound names, renames, wrap-forcing
  flags) snapshots per branch — count_down's `tmp__3` is a FIRST
  binding in each branch, not a shadow.
- The fall-through case (diverging then, Skip else) forwards the
  `¬cond` hyp on the continuation path — the counter resumes past it.
- **A Loop is a scope boundary**: its telescope names consume
  (bounds/invs/cond), the body numbers independently from the
  telescope end, and the post-loop path resumes from the same point.
  `find_square`: the inner body's hyps and the outer body's later
  hyps BOTH number from the telescope end (`0 ≤ a + 1` is
  `_h_hoist_10` in both the inner-body goals and the outer re-close).
- An assert-query scope (`new_scope`) drops outer hyps: the sub-walk
  numbers from 0, `poison_forced` resets (hyps stripped) but
  `flet_forced` carries in (lets kept).

### 2.4 The shadow mirror: freshening happens ONLY in hoisted goals

Production's `hoist_all` freshens a later binding of a taken name
(`i` → `i_hoist1`, then `i_hoist2`, …) and rewrites downstream
references (`rename_frame_vars`). The sharp rule, learned the hard way
when fn-wide freshening broke add_capped:

- **Wrap-mode goals do NOT freshen** — goal-position lets shadow
  textually. So the serializer freshens iff the current prefix is
  wrap-free (`flet_forced`/`poison_forced` split — see §2.3). The MIX
  case (shadow before a later wrap-forcer) is documented honest-fail
  (`hoist-mixed-shadow`, unhit so far).
- The eq name is `_h_{chosen}_hoist1` — `fresh()` ALWAYS appends
  `_hoist1`. So `_h_i_hoist1_hoist1` is NOT a collision: it is simply
  `_h_` + `i_hoist1` + `_hoist1`.
- Renames apply to hyp props, assign RHSs, conds, ret values, the
  annotated OBLIGATION texts too (`oblig_leaf`/`neg_oblig_leaf`), the
  decrease measure (rendered at body END — the d_old VALUE stays
  loop-entry-plain), the re-close invariant obligations, and the deep
  RawExp `Var` ids.
- The re-close invariant obligations are DIFFERENT leaves from init
  (`i_hoist1 ≤ n` vs `i ≤ n`) — hence `Loop.inv_obligs_exit`
  (model addition). Slot discipline: deep iff the renamed text's id
  is already in `deep_ids` (rename no-op — `n ≤ 1000` keeps the deep
  `RawExp.Span`), else opaque `atom_ob` (genuinely renamed texts are
  atoms, matching production exactly).
- Loop mod-var binders keep SOURCE names always (production never
  freshens them); the renames clear at loop exit (`r = acc`, not
  `r = acc_hoist1`).

### 2.5 The assert-query emits a degenerate `True` goal

The query's own ensures is empty, so production emits one final
in-scope goal `True` (`emit_done_or_split`'s `and_all([])` fallback,
the `_tactus_ensures_` theorem). The mirror: `StmData::AssertQueryNl`
gained a true-obligation slot (`atom_ob("True")`), closed under the
post-body frame (the query's own assert hyps DO accumulate inside).

## 3. Production-fidelity details that mattered

Smaller, but each was a bridge-breaker:

- **Call dest binder typ = the instantiated CALLEE ret typ**
  (`ret_typ_subst`), NOT the SST dest local's declared typ. Verus
  auto-derefs call results into locals (`vec_index`'s Ref-typed return
  becomes an `Int` local) while the binder stays `Tactus.Ref Int`.
- **The Return value renders through production's TYPED SPINE**
  (`sst_exp_to_typed` + `into_slot`) with a tracked `let_binder_typs`
  env — that is what inserts `.deref` on a Ref-typed call-result local
  (`r = tmp__1.deref`), which the checked path + claimed-typ coerce
  cannot reach.
- **The goals transcriber must peel residue lets** off production's
  leaf (`let tmp__1 := …; @loc leaf`) into `GoalData::Let` — otherwise
  the whole residue-wrapped leaf atomizes and mismatches the ref
  side's structured `residue_fold_e`.
- **The deepener erases `TypeAnnot`** (`((view v) : Seq Int)`) — the
  reference RawExp never carries ascriptions, so both sides drop them.
- **Ghost/spec lets lower to `Bnd Let` chains INSIDE the return
  expression** (use_multiarg's `let _g2: Ghost<nat> = …`) — peel them
  into AssignH-class statements before the Ret.
- **Assert/Assume forward hyps duplicate**: the overflow assert and
  the following Assume push the SAME prop text twice with sequential
  ordinals (`_h_hoist_1`, `_h_hoist_2` — both `0 ≤ x + y ∧ …`).

## 4. Process lessons

- **The stale-certs trap**: fixture certs are gitignored regenerables.
  Read fresh ones before concluding anything about production (an
  11:29 read showed the decrease unrenamed; the 16:30 regen showed it
  renamed — the difference was a stale emission, not a production
  change).
- **The `TactusStmts_*` olean staleness** (worth its own
  investigation): a gate wrote a fresh `TactusStmts_*.lean` (16:58)
  without rebuilding its `.olean` (16:48), and the next gate's Link
  layer then reported a "Type mismatch" + "contains sorry" that
  pointed everywhere except the real cause. The content was always
  correct — per-fn theorems elaborate standalone. This looks like a
  stmts-module rebuild-logic hole, distinct from the known
  emitter-binary-fingerprint cache gap.
- **Per-goal probing beats full bridges for triage**: `nth refg i` vs
  `nth prod i` with `goal_eq … = 1 := by decide` localizes a failure
  to one goal in seconds; `#reduce` of the two then shows the exact
  frame/leaf that diverges. Used ~15 times in this arc.
- Fixture expected-goals can be COMPUTED by `ref_wp` itself via
  `#reduce` against the fresh oleans and pasted (the fixture then pins
  refWp's output as a regression tripwire; the real-cert bridge is the
  independent check).

## 5. Remaining gaps (documented honest-fails)

- **vec_read** (probe9): stage-B reference-renderer coercion. The
  binder telescope matches production EXACTLY; `render_exp` of the
  reference RawExp derives `v.deref` where production writes `v`
  (View.view arg), and misses the `Int.ofNat` on a CallN arg (per-arg
  spec-call coercions need the callee signature the fixed-vocabulary
  mirror does not carry). Follow-up §7.7.
- **head_exec** (probe9): match-statement machinery — per-arm value
  temps hoist as FLetH pairs inside per-arm goals (the N2 match-split).
  `StmData` has no Match arm. Card separately.
- **apply_hom_gen / apply_hom_inv** (probe11): call-arg temp lets are
  typ-less `Wp::LetRaw` frames (production wraps the whole goal); the
  serializer typed them from `local_typs` and hoisted. Plus the
  auto-ref arg coercion (`Tactus.Ref.mk <arg>`) in instantiated
  requires, which the serializer drops. New Call-arm machinery.
- **lemma_runtime_word_view_append / _subrange** (probe11):
  assert-forall skolem binders unmodeled — production emits
  `∀ (k : Int)` in the telescope; stage A has no quantifier binder.
  These should be a LOUD census rejection (`assert-forall` tag), not
  non-bridging certs. Census-gap follow-up.

## 6. Follow-up queue (card + NEXT.md)

1. b70/71 full closes (unblocked) — re-run the vec_read/use_clamped
   bridges end-to-end, mutation-kill the ∀-path frame.
2. Call-arg temp lets + auto-ref arg coercion (the apply_hom class).
3. assert-forall loud census rejection.
4. stmts-olean staleness investigation (§4).
5. discharge Q1 composer arm (`HypProvenance::HoistEq` exists, main
   `9a88b6c`).
6. b69 Tactus-mode assert-query mirror decision (Danielle's call).
7. call-mut arm (prophecy/rebind) — vec_push7, fill_zeros,
   runtime.copy_word; card before starting.
8. Cache emitter-fingerprint (parked).
9. Stage-B deep-leaf coverage growth (vec_read class, §5).
