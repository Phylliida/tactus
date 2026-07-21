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
