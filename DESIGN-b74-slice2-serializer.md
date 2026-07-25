# DESIGN — bootstrap-74 slice 2: the serializer half of the N1-hoist mirror

Status: **planned** (2026-07-20). Prereqs landed: slice 1a (`d08b6c1`,
FHyp name field), slice 1b (`17b6e72`, FLetH + gated dual-mode close
fns, proof layer 182/0 + package gate green). This doc is the work
plan for the serializer half plus the follow-on queue. The b74 card
(`board/bootstrap-74-bridge-n1-hoist-reconciliation.md`) carries the
design history; this doc is forward-looking only.

## 1. Goal and shape of the work

Production now emits N1-hoisted goals by default: every context frame
becomes a theorem-level binder (`hoist_all`, sst_to_lean ~1865) —
hyps as named binders `(_h_hoist_i : P)`, typed non-Bool lets as the
pair `(x : T) (_h_x_hoist1 : x = v)` — with an all-or-nothing per-goal
fallback to the old wrap form when any let is Bool-typed or typ-less.

The model (tactus-core) can now express both forms and picks the mode
per goal via `has_plain_flet`. What it cannot do is invent the leaf
ids production's rendering interns: hyp binder names, let typ texts,
equation texts, equation names. **Slice 2 = the serializer supplies
them**, by reproducing production's naming/classification exactly and
emitting the extended SST vocabulary.

Everything below keeps the established division of labor:
- serializer (sst_serialize.rs): naming, classification, leaf
  interning, honest-fail census tags;
- model (tactus-core/lib.rs): mechanical rendering of ids it is
  handed. Small model arity additions are part of this slice (§4);
  they follow the proven pattern (discharge absorbs statement growth;
  fixtures 0-fill / re-derive).

## 2. Step 0 — evidence first: regenerate the fixture certs

Before any code: regenerate the 13 fixture certs + the 3 tgt exec
certs with **current** production and read the actual goal shapes and
leaf tables. Slice 1's design was driven by two reduces (use_clamped,
vec_read); the fixture families each have open evidence questions:

| Family | Fixture(s) | Open question |
|---|---|---|
| asserts/seq | add_capped | plain confirmation of `_h_hoist_i` numbering + seed unchanged |
| call ret-eq | use_clamped, vec_read | confirm interned name TEXTS (is leaf 16 literally `_h_hoist_1`?); RetLet postcondition pair `All 8 1 (All 13 14 …)` — what are 13/14's texts (`_h_r_hoist1`, `r = s`?) |
| if-join | count_down | does the desugared-clone path number hyps identically in both branches (prefix counts match — expected yes) |
| loop | sum_to | **the big one**: `_tactus_d_old` is a typed let → post-N1 the maintain goals should HOIST — do inv hyps now name `_h_hoist_i` instead of `_h_ctx_N`? does `split_leading_binders` still run first (leading Binder frames keep their names) or does hoist_all own the whole telescope? |
| nested loop | find_square | non-leading branch: does the enclosing typed let hoist too, collapsing the leading/non-leading distinction? (`loop_maintain_frame`'s has_let branch may need a rethink if production no longer distinguishes) |
| assert-query | mul_bound (F20) | AQNl strip interaction with hoist mode — does the stripped sub-walk hoist independently? |

Deliverable of step 0: a table (append to this doc) of per-family
production shapes + name texts. Only then wire the serializer. If the
loop evidence shows `split_leading_binders` is gone, the model's
`loop_maintain_frame`/`loop_use_frame` leading/non-leading split
needs redesign — **stop and card that before proceeding** (it changes
slice scope).

## 2b. Step-0 evidence table (2026-07-21, certs regenerated)

Certs regenerated with current production (post-N3, `417de34`):
`--crate-type=lib --lean-backend --emit-lean --tactus-emit-cert`
(fixture: 32/39 certified — `call-generic` rejections GONE, only
2×call-mut + rawvir-poly remain; tgt runtime: the 3 exec certs +
2 lemma certs). All name texts below read straight off the fresh
leaf tables.

| Family | Evidence | Answers |
|---|---|---|
| call ret-eq (use_clamped) | leaf 16 = literally `_h_hoist_1`; RetLet pair = `All 8 1 (All 13 14 …)` with 13 = `_h_r_hoist1`, 14 = `r = t`. FHyp ordinals run in frame order (bound hyp → 1, ensures → 2). | name texts confirmed exactly as designed |
| call ret-eq (vec_read) | dest `tmp__1 : Tactus.Ref Int` (non-Bool) HOISTS: `_h_tmp__1_hoist1`, eq `tmp__1 = Tactus.Ref.mk (…)`; RetLet eq = `r = tmp__1.deref` (deref in eq RHS — comes from the RetBind-value deref path). | FLetH classification confirmed; eq-prop text = `x = v` pp'd AFTER the value-side deref |
| asserts/seq (add_capped) | **ALL THREE SHAPES IN ONE FN.** goal 0: pure hoist. goal 1: hoist + RESIDUE (`tmp__1 := s < 2000` Bool let → goal-position let around the leaf, leaf 28 = `let tmp__1 := s < 2000; ⏎…tmp__1`). goals 2–3: FULL WRAP (`Imp`/`Let` shape) — a hyp `tmp__1` (the asserted Bool as proposition) MENTIONS the residue name → production's bail check fires. Seed numbering unchanged; `_h_hoist_1/2` per goal. | residue is per-goal and monotone along the frame prefix; see §2c |
| if-join (count_down) | cond hyp = `_h_hoist_1` in BOTH branches (`n = 0` then / `¬(n = 0)` else) → per-branch counter snapshot/restore confirmed. `decrease_init0` let hoists (`_h_decrease_init0_hoist1`). Same tmp names recur across branches (`tmp__3` in both, distinct eqs) — NO cross-branch freshening. | branch numbering identical, as expected |
| loop (sum_to) | `_tactus_d_old_0_0` HOISTS (`All _tactus_d_old_0_0 (All _h__tactus_d_old_0_0_hoist1 …)`). Inv hyps in goals are `_h_hoist_3..6` — **`_h_ctx_N` is GONE from goal shapes** (survives only in the SST `Loop` `inv_hyps` side-table). Havoc'd-var bound hyps = `_h_hoist_1/2`; cond = `_h_hoist_7`. **SHADOWING IS REAL**: body assignment `i := i + 1` freshens to `i_hoist1` with eq-hyp `_h_i_hoist1_hoist1` (double suffix — `_h_i_hoist1` was already taken). | §6's "expected: none" for shadow freshening is WRONG for loops — the rename mirror is IN SCOPE (census shows hits in every loop-body rebind) |
| nested loop (find_square) | Outer and inner frames compose by FLAT CONCATENATION under ONE per-goal counter (outer bound/inv/cond = 1–4, inner bound/inv/cond = 5–9, inner `_tactus_d_old_1_0` hoists too). The leading/non-leading distinction is GONE from goal shapes. | loop-telescope redesign trigger TRIPPED — see §2c |
| assert-query (mul_bound) | AQNl-stripped goals hoist cleanly and independently (`_h_hoist_1..5` per goal; the queried fact enters as a `_h_hoist_i` hyp). | no special strip×hoist interaction |

tgt exec certs (probe11): all three regenerated
(`runtime__apply_hom_gen`, `runtime__apply_hom_inv`,
`runtime__impl__4__clone`); shapes to be read at §5 sweep time.

## 2c. Scope updates decided from the evidence (2026-07-21)

1. **Three goal modes, not two.** Production (post-`8dcac64` partial
   hoist) has: full-wrap (typ-less let, or a binder/hyp TYPE
   mentioning a residue name), hoist, and hoist+residue (Bool lets
   fold as goal-position lets around the leaf). Danielle's call
   (2026-07-21): **mirror residue in the model** rather than
   honest-failing residue goals. The mode gate is per-goal and
   monotone along the frame prefix (add_capped: goal 1 hoists,
   goals 2–3 wrap off the SAME shared prefix plus one poisoning hyp).
2. **"Mentions residue" is serializer-computed.** The model's leaves
   are opaque ids — it cannot test `lexpr_mentions_var`. The
   serializer (which holds the interned texts) marks each FHyp whose
   prop mentions an in-scope residue name (poison), and the model's
   gate reads the mark: any poisoned frame OR typ-less FLet ⇒
   whole-goal wrap; else hoist, folding residue FLets around the
   leaf. (Faithful alternative — model-level text analysis — is
   impossible without breaking leaf opacity.)
3. **Shadow-rename mirror is IN SCOPE** (was §6-deferred): every
   loop-body rebind hits it (`i_hoist1`, `_h_i_hoist1_hoist1`).
   Serializer must freshen shadowed let names AND rewrite downstream
   leaf texts, exactly as production's `rename_frame_vars` does.
4. **Loop-telescope redesign trigger tripped** (§2's stop-and-card):
   `split_leading_binders` naming (`_h_ctx_N`) is gone from goal
   shapes; leading/non-leading is gone; nested loops are flat
   concatenation under one per-goal counter. `loop_maintain_frame`/
   `loop_use_frame` simplify accordingly (carded on b74).
5. Follow-up item partially pre-landed: `HypProvenance::HoistEq`
   already exists (main `9a88b6c`) — discharge Q1 shrinks to the
   composer arm.

## 3. Serializer work items (sst_serialize.rs)

### 3a. Hyp naming — the `_h_hoist_i` mirror

Production names each Hyp frame by its 1-based ordinal among Hyp
frames in the goal's frame list (`hoist_all`'s `hyp_counter`),
freshened against taken names. Frames are append-only along a walk
path, so a given statement's hyp has a fixed ordinal per path — the
serializer computes it with a running per-branch counter during its
existing walk. Implementation:

- Add `hyp_ordinal: u64` to `Serializer` state; increment at every
  site that emits a frame-hyp-producing construct, snapshot/restore
  around `block()`'s If-branch cloning (each branch resumes from the
  pre-If count; the cond/neg-cond hyp increments inside each branch).
- Name text: `format!("_h_hoist_{}", ordinal)`, interned via
  `text_leaf`. Collision with a user binder named `_h_hoist_N` →
  honest-fail with census tag `hoist-name-collision` (production
  freshens to `_h_hoist_N_hoist1`; mirror later only if census shows
  real hits — §6).
- Sites: `stm()` Assert arm (~1914), Assume arm (~1928), `block()`'s
  If desugar (~2223, c and nc hyps), `call_stm()` post-frame FHyp
  sites (2271–2303), `loop_stm()` cond/neg-cond (evidence-dependent,
  §2).
- The seed (params/bounds/reqs) is Binder frames — NOT counted, no
  change.

### 3b. FLetH classification and assembly

A let hoists iff its typ is known and non-Bool (production's gate).
For each site the serializer already has the typ:

- **Assign** (`stm()` ~1939): local decl typs are in scope
  (`binder_typs` path). Classify: typ known + `!matches!(TypX::Bool)`
  → emit `StmData.AssignH x ty v en ep` (new variant, §4) where
  `ty` = interned `typ_to_expr` pp, `ep` = interned pp of
  `LExpr::eq(var, rhs_rendered)` (byte-for-byte production's equation
  text — reuse the same pp path production's hoist uses), `en` =
  interned `_h_{x}_hoist1` (production's `fresh()` always appends
  `_hoist1` on first use). Bool or unknown typ → plain `Assign`
  (wrap fallback, matches production).
- **Call dest let** (`call_stm()` 2271, 2295): `FrameList.FLet
  dest_id dv` → `FrameList.FLetH dest_id ty dv en ep` when the dest
  typ (callee ret typ, instantiated) is known non-Bool. The
  serializer builds these post frames verbatim — no model change
  needed here, just the richer literal.
- **RetLet** (`stm()` Return ~1982-2048): `RetBind.RetLet name val`
  → `RetBind.RetLetH name ty val en ep` (new variant, §4) under the
  same classification, using the ret typ (already resolved for the
  RetBind-value deref logic).

### 3c. Goals-side transcriber + deepener

- `GoalShape`/`goal_data()` (2519): post-N1 production theorems are
  flat binder telescopes; the existing All arm already covers named
  hyp binders (evidence: `All 16 12` in the use_clamped reduce). No
  structural change expected; verify against step-0 certs.
- The W6d deepener currently bails to `Atom` on hoisted obligation
  shapes it doesn't recognize (vec_read goal 2 evidence). Extend its
  shape-walk to descend the hoisted binder spine before matching the
  G0–G7 leaf patterns. Verdict-neutral on failure (atom fallback
  stays, as today).

### 3d. Census

- `stm_size_of` (3227): count `FrameList.FLetH`, `StmData.AssignH`,
  `RetBind.RetLetH`.
- New rejection tags: `hoist-name-collision`, `hoist-shadowed-let`
  (§6), `hoist-unclassifiable-let` (typ path missing where production
  hoisted — indicates a serializer gap, should be zero).

## 4. Model work items (tactus-core/lib.rs — small, with the slice)

Same pattern as slices 1a/1b: arity additions, arm updates, pin
additions; the discharge and fixture work absorbs them.

1. `StmData::AssignH(x, ty, v, en, ep)` — `frame_after` arm →
   `FLetH(x, ty, v, en, ep)`; `wp_stm`/`exec_safe_f` arms mirror
   Assign (no goals); pins `u_wp_assignh`, `u_esf_assignh`,
   `u_fa_assignh`; `stm_size` arm.
2. `RetBind::RetLetH(r, ty, val, en, ep)` — `ret_frame` arm →
   append `FLetH`; pin updates alongside the RetLet ones.
3. `StmData::If` cond-hyp names + `StmData::Assert`/`Assume` hyp
   names: **only if step-0 evidence confirms** production names these
   `_h_hoist_i` (expected). Shape: `Assert(o, hn, h)`,
   `Assume(hn, e)`, `If(c, cn, nc, ncn, t, e)`; `frame_after`/`wp_stm`
   arms thread `hn` into `FHyp(hn, …)` replacing the 0-sentinels.
   Loop cond names likewise (evidence-dependent).
4. Fixture updates: mechanical re-derivation, per-goal mode rule as
   in slice 1b (wrap-forced goals byte-identical; hoisted goals get
   real name ids from the step-0 leaf tables).
5. Keep the invariant: **0 never appears as a hyp name in a frame
   that can reach hoist mode** (0-named `All(0, h, ·)` upds collide
   with binder id 0 in the abstract semantics). After item 3 the only
   remaining 0-name emitters are model-internal fixtures, which must
   use distinct ids.

## 5. Bridge sweep (the payoff, closes b74)

1. probe9: all 13 fixture certs `goals_eq … = 1` by `decide`, plus
   mutation-kill per family (flip one name id / one eq leaf / one
   constructor — each must flip the decide).
2. probe11: re-run with the 3 tgt exec certs (apply_hom path); retire
   the honest-fail entries.
3. tgt census re-run: call-generic 0, call-forall-path 0 must hold;
   the 4 assert-query-tactus + 1 call-mut tags remain (separate
   arcs).
4. Full suite + tactus-core gate (`--lean-all-proofs`, always).

## 6. Deferred within b74 (census-gated)

- **Shadow freshening**: production renames shadowed let binders
  (`x_hoist1`) and rewrites downstream references INCLUDING leaf
  texts. The serializer's leaves are interned at emission time with
  as-written names, so a shadowed-let fn's leaf texts diverge from
  production's post-rename texts. Honest-fail with census tag
  `hoist-shadowed-let`; implement the rename mirror only if the
  census shows real hits in tgt/fixtures (expected: none — Verus SSTs
  rarely shadow).
- **Name-collision freshening** (`_h_hoist_N` as a user name):
  same treatment, tag `hoist-name-collision`.

## 7. Follow-up queue (beyond b74)

1. **Discharge Q1 — Other-provenance equation hyps** (emitter,
   lean_verify Link discharge). The 4 remaining pendings: hoisted
   `tmp__N`/let equation hyps carry census-Other provenance, which
   the spine composer treats as pending (flagged in
   DESIGN-leaf-normal-emission §5 Q1 — "until a dedicated provenance
   variant exists"). Work: add a `HypProvenance::HoistEq` variant at
   `hoist_all`'s equation-binder site, teach the discharge spine to
   compose it (it is definitionally an equation over an in-scope
   binder — the composer can rewrite with it). Restores 0-pending.
2. **b70/71 full closes** — unblocked by the §5 sweep: re-run the
   vec_read/use_clamped bridges end-to-end, mutation-kill the ∀-path
   frame, close both cards.
3. **b69 residue — Tactus-mode assert-query** (needs a Danielle
   decision): production renders the 4 remaining tgt assert-query fns
   inline (`have h : P := by <tactic>` — no separate goal; P enters
   as a hyp), so the stage-A mirror looks Assume-like. Decide the
   mirror shape (Assume-equivalent with a provenance mark vs a
   dedicated StmData variant), then a small arm.
4. **call-mut arm** — vec_push7, fill_zeros, runtime.copy_word.
   Genuinely new machinery (prophecy/rebind of `&mut` args in the
   frame mirror); card it before starting.
5. **Loop-telescope redesign** — only if step-0 evidence shows
   production dropped the leading/non-leading distinction (§2); would
   simplify `loop_maintain_frame`/`loop_use_frame`.
6. **Cache emitter-fingerprint** (parked, from the cache-key fix
   arc): the closer/emitter binary version still isn't keyed; a
   build-fingerprint tag closes the last known staleness hole.
7. **Deep-leaf coverage growth** (ongoing): each atom-fallback
   obligation shape that shows up in bridge reduces is a candidate
   for a new G-pattern in the deepener.

## 8. Order and risk

Suggested order: §2 (evidence, ~1 session incl. regen) → §4 items
1–2 + §3b Call site (unblocks use_clamped/vec_read, the two
already-reduced bridges — earliest possible decide-close as a smoke
test) → §3a naming + §4 item 3 (Assert/Assume/If) → add_capped +
count_down bridges → loop evidence decision + loop path → sum_to /
find_square → §3c deepener → §5 sweep.

Main risks:
- Loop-telescope evidence forcing a scope change (§2) — bounded by
  stopping and carding.
- Equation-text byte-mismatches (`x = v` pp drift between the
  serializer's path and production's hoist path) — mitigated by
  reusing the same pp entry points production calls, and by the
  reduce workflow (mismatch → diff the two texts directly).
- Name-ordinal drift on branchy fns — mitigated by the If-clone
  snapshot rule (§3a) and count_down's mutation-kill.
