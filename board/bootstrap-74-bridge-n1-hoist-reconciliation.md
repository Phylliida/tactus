---
title: "bridge ↔ N1-hoist reconciliation — leaf-normal emission reshaped production goals; ALL fixture bridges honest-fail post-merge"
status: in_progress
claimed_by:
created: 2026-07-18T09:30:00Z
updated: 2026-07-18T09:30:00Z
---

## Description

Post-merge (e2e-speed + leaf-normal emission, `8accb8d`), the W2b
differential gate found exactly what it exists to find: production's
goal emission changed shape under the frozen refWp mirror, and **every
fixture bridge now honest-fails** (`decide` proves `goals_eq … = 1`
false — 13/13 CLOSE-BROKE, probe9).

**Evidence** (use_multiarg, the minimal case):
- refWp reconstruction: `All 0 1 (All 3 2 (Let 7 8 (LeafE …)))`
- production now:       `All 0 1 (All 3 2 (All 17 14 (All 15 16 (All
  13 14 (All 11 12 (All 7 1 (All 9 10 (LeafE …))))))))`

Same params, same final leaf; the single `Let` became THREE
(witness, eq-hyp) binder pairs — DESIGN-leaf-normal-emission §N1:
spine-position lets emit as theorem binders `(tmp : T) (h : tmp = e)`,
and chained lets production formerly SUBSTITUTED now hoist as their own
pairs (hoisting is linear; substitution duplicated). Bool-typed lets
are excluded (stay wrap → still `Let`-shaped). N2 match-splitting
similarly reshapes match goals per-arm.

**Pattern 2 (use_clamped evidence, 2026-07-18):** FHyp rendering
changed UNIFORMLY — production emits hypotheses as NAMED binders
(`All(h, prop)`, the theorem-binder form) where refWp renders
`Imp(prop)`. This is a rendering-layer change, suggesting part of the
reconciliation belongs in tactus-core's `close_e` (mechanical: FHyp →
named All) rather than serializer assembly — the hoisted-let pairs
remain serializer territory (they need production's hoist classifier).

**Reconciliation options:**
- (A) **Serializer assembly (recommended — Option-2 precedent):** the
  serializer's goals/SST transcription re-derives production's hoist
  (same classifier: spine-position + non-Bool → `FBind(tmp, typ_id) ∘
  FBind(h, prop_typ_id)` with the eq-prop interned as a typ; term
  position / Bool → keep `FLet`). refWp stays FROZEN; the decide
  bridge validates the assembly per cert. Precedents: count_down
  If-join desugar (bootstrap-19), #128 ret-eq path, W6e value-if-lift.
- (B) Teach refWp the hoisted rendering — rejected on frozen-refWp
  grounds unless (A) hits a wall.

**Coordination gate:** main-side N1 still has an OPEN nondeterminism
flicker (hoist-order; coercion half fixed — memory
project_tactus_e2e_speedup). Bridging against a flickering emission is
a moving target — confirm with Danielle whether to start now or after
the flicker fix settles the order.

**Also in this arc (probe9/probe11 infra, FIXED 2026-07-18):** the
defs-collapse moved bare `TactusDefs` into the prelude cache with NEW
hashes; both runners' hardcoded `prelude-e81fbf9a86375c12` pin →
probe37-style glob over all `prelude-*` + `$CORE_OUT/pkg` on
`LEAN_PATH`.

**Done when:** probe9 fixture family bridges close again (including F20
mul_bound / AssertQueryNl), honest-fail classification updated for any
documented caveats, probe11 re-run, suite green.

**Blocked by:** possibly the main-side N1 flicker fix (Danielle's
call).

## Design (2026-07-19, settled after reading `hoist_all`)

Production (`OblCtx::hoist_all`, sst_to_lean ~1865): per goal,
ALL-OR-NOTHING — if ANY `Let` frame is Bool-typed or typ-less, return
None → whole goal renders old-style (wrap: Let goals, Imp hyps).
Otherwise EVERY frame hoists: `Let(x,v,T)` → `(x:T)` +
`(_h_x_hoist1 : x = v)`; `Hyp(P)` → `(_h_hoist_i : P)` (1-based
counter over frames in order); `Binder` → itself. Shadowed let names
freshen (`x_hoist1`) with downstream references renamed; first binding
keeps the source name.

**Mirror plan — naming lives in the serializer, rendering in the
model:**
- `FrameList::FHyp` gains a NAME id: `FHyp(name, prop, rest)` —
  serializer interns production's deterministic hyp name
  (position-derived counter; freshening collisions = documented
  honest-fail).
- `FrameList::FLet(x, v, rest)` → `FLetH(x, typ, v, eq_name, eq_prop,
  rest)` for HOISTABLE lets (serializer classifies: typ known +
  non-Bool; eq_prop = interned render of `x = v`); plain `FLet`
  REMAINS for non-hoistable lets.
- `close_e` gate mirrors production exactly: any plain `FLet` in
  frames → old rendering (FHyp→Imp ignoring name, FLetH→Let via its
  v id); else hoisted rendering (FBind→All, FHyp→All(name,prop),
  FLetH→All(x,typ)∘All(eq_name,eq_prop)).
- `GoalData` UNCHANGED (hoisted chain = existing nested All).
- Semantics: FHyp name is rendering-only — `holds`/`exec_safe_f` read
  the prop; soundness untouched in meaning, arms updated mechanically
  (discharge auto-absorbs, proven twice).
- Ret-position let (`RetBind`) and Call-post FLets get the same
  treatment at their serializer assembly sites.
- Residual: goals-side deep-leaf transcription bails to atom on
  hoisted shapes (vec_read goal 2) — deepener follows the new shape,
  serializer-side, after the frame work.

Order: (1) tactus-core FrameList/close_e/arms + gate; (2) serializer
naming + classification + assembly sites; (3) fixtures bridge-close
iteratively + mutation-kill; (4) tgt 3 certs + probe11; suite.

### Design correction (2026-07-19, after reading holds/close_e)

`holds(All(x, _ty, t)) = ∀ n, holds(t, upd(st,x,n))` — the typ slot is
semantically IGNORED. Encoding named hyp-binders as `All(name, prop)`
(what the goals transcriber currently does, and what my first sketch
assumed refWp could emit) would make soundness read a hypothesis as a
spurious quantifier. Corrected plan:

- **GoalData gains `ImpN(name, prop, t)`** — holds = `hp(prop, st) ==>
  holds(t, st)`, name inert (rendering only). The goals TRANSCRIBER
  switches to ImpN for hyp-provenance binders (production's
  `(LBinder, Option<HypProvenance>)` pairs distinguish them: Some =
  hyp, None = value binder) — serializer-side, both sides of the
  bridge agree by construction.
- Hoisted let pair = `All(x, typ) ∘ ImpN(eq_name, eq_prop)`; its
  semantic reading is the ∀+eq form. The frame-telescope semantic fn
  (close_sem) gets the SAME `has_plain_flet` gate as close_e, so each
  mode's rendering and semantics stay structurally parallel and
  wp_stm_sound remains a mechanical weave.
- The `let x := v ↔ ∀ x, x = v → …` equivalence is NOT needed in the
  oracle-parametric layer — it belongs to the adequacy spine ONCE,
  where oracles are real (probe37 territory).
- "Semantics untouched" in the earlier sketch was WRONG — semantics
  gains ImpN + gated close_sem, both mechanical.

### Design FINAL (2026-07-19, third pass — the reqs precedent decides it)

The ImpN correction was itself overcorrected. `FnCtxData.reqs`
(finding-2) already established the encoding for named prop binders:
`FBind(name, prop)` → `All(name, prop)` with the abstract ∀-reading
(holds ignores the typ slot); the ADEQUACY layer recovers the real
dependent-product meaning (`∀ (h : P), G` IS `P → G` in real Lean).
The hoisted forms reuse it wholesale:

- Hyp → `FBind(_h_hoist_i, prop)`-style rendering via a NAMED FHyp:
  `FHyp(name, prop, rest)` renders `All(name, prop)` in hoist mode,
  `Imp(prop)` in wrap mode.
- Hoistable let → `FLetH(x, typ, v, eq_name, eq_prop, rest)`:
  hoist mode `All(x,typ) ∘ All(eq_name, eq_prop)`; wrap mode
  `Let(x, v)`. Plain `FLet` remains (non-hoistable), and its presence
  IS the gate: `has_plain_flet(f)` → whole goal wraps (mirrors
  hoist_all's all-or-nothing None).
- `close_e` / `close_sem_e` / `close_sem_obligs` split into
  wrap/hoist recursions with the gate applied ONCE at the top (suffix
  recursion never re-checks — matches production inspecting the whole
  frame list once). Semantics parallels rendering per mode
  (hoist-mode FHyp/FLetH read as ∀-binders like FBind; wrap mode as
  today). GoalData UNCHANGED; goals transcriber UNCHANGED.
- NO wrap↔hoist equivalence obligation in the oracle-parametric layer.

Serializer half (step 2): FHyp name ids = production's `_h_hoist_i`
ordinal among FHyps in the frame prefix (per-branch walk state); reqs
already named; Assign classification (type_map typ, non-Bool →
FLetH); Call-post FLet → FLetH; RetBind let likewise; shadow
freshening = documented honest-fail initially (no-shadow common case
first).

### Slice 1a status + LATENT MAIN-SIDE FINDING (2026-07-19)

Slice 1a (FHyp arity migration, name field + 0-sentinels, pass-through
preservation, 4 u_-lemma signatures + 9 callers) is mechanically
complete and compile-clean. Gate shows 134/7 — but the 7 reds are
**PROVEN LATENT, not caused by the migration**: on main's UNTOUCHED
code, hash-invalidating u_holds_all_binder alone (body `{ assert(true); }`
touch) reproduces the failures. The post-merge gates were green via
CACHE HITS from the main-side re-emit; the current pipeline cannot
RE-prove these quantifier lemmas cold:
  u_holds_all_binder, u_cse_bind, u_cso_bind, holds_close_e,
  cso_cons_split, prophecy_sound, prophecy_swapped_sound
(all tactus_tactic-attributed, all `∀ n, upd(st,x,n)` shapes — likely
the closer-reconciliation (eca810f) or eliminator-arm re-emit changed
closer behavior for this shape). ANY tactus-core edit that
invalidates them hits this. Needs main-side attention (or closer
re-reconciliation for the ∀-upd shape) BEFORE b74 slices can gate.

### CORRECTION + cache-key fix (2026-07-19, Danielle's sus instinct)

The "latent main-side regression" was WRONG — my red runs had dropped
`--lean-all-proofs`. With the flag, slice 1a gates **141/0, discharge
69/69** — slice 1a is DONE and there is no main-side regression. The
REAL finding: the verification-cache base hash was only
`solver + krate` — Lean mode flags weren't keyed, so verdicts cached
in all-proofs mode silently served non-all-proofs cache-hits (and
vice versa). FIXED: `lean:{lean_backend}:{lean_all_proofs}` now in the
base hash (verifier.rs). Remaining known hole (documented, not fixed):
the emitter/closer BINARY version isn't keyed — a rebuilt binary with
changed closer logic reuses old verdicts until the krate hash moves;
worth a build-fingerprint tag if it ever bites.

### Slice 1b WIP state (2026-07-19 end-of-session — spec layer DONE, proof layer mapped)

COMMITTED as WIP (gate red at proof layer, spec layer complete):
FLetH variant, has_plain_flet, close_e/close_sem_e/close_sem_obligs
split into _wrap/_hoist + non-recursive gated dispatchers (callers
unchanged), FLetH arms in frame_len/frame_append/close/havoc_lets/
has_let/strip_hyps.

REMAINING (precise map, in order):
1. Three non-exhaustive proof matches: holds_close_e (~3639),
   cso_nil_true (~3703), cso_cons_split (~3733). Restructure each as
   TWO mode lemmas (_wrap = today's proof + FLetH arm mirroring FLet;
   _hoist = FHyp arm via u_holds_all_binder against the ∀-upd sem,
   FLetH arm via TWO nested u_holds_all_binder) + a dispatcher proof
   with the ORIGINAL signature (`if has_plain_flet(f) { wrap } else
   { hoist }` — dispatchers are non-recursive open specs, Z3 inlines).
2. u_cse_hyp / u_cso_hyp as stated are now TRUE ONLY IN WRAP MODE
   (hoist-mode FHyp is the ∀-reading). Either add `requires
   has_plain_flet(t)`-style gates or split into _wrap/_hoist variants;
   fix the three concrete callers (prophecy proofs + prop_v sites
   ~3864/3957/3989).
3. prophecy_sound / prophecy_swapped_sound: their frames (FBind +
   hyps, NO lets) now dispatch to HOIST mode — their hand-computed
   ensures describe the wrap reading and must be restated in ∀-form.
   ⚠ 0-sentinel hyp names COLLIDE in hoist mode (upd(st, 0, n) hits
   binder id 0) — give model-internal fixture frames DISTINCT name ids
   (e.g. 90+), and note: serializer slice 2 must NEVER emit 0 names
   for frames that can reach hoist mode.
4. Any fixture expected-goal literals with let-free frames flip to
   hoisted shapes (cd19 keeps wrap — its Assign FLet gates it).
5. Then slice 2 (serializer): _h_hoist_i naming, FLetH classification
   (type_map + non-Bool), Call-post/RetBind conversion, deepener
   follow-up. Gate ALWAYS with --lean-all-proofs.

### Slice 1b COMPLETE (2026-07-20): 182/0, package gate green

Proof layer landed across two commits (`3918809` green, `+` discharge
recovery). Final architecture:
- One-step pins are MODE-LEVEL (u_cew/u_ceh, u_csew/u_cseh,
  u_csow/u_csoh + u_gate_* + dispatch pins); dispatcher-level cons
  unfolds are FALSE across mode boundaries and were removed.
- Dispatch pins are REQUIRES-FREE (`gate == 1 ==> ...` in ensures) —
  requires-carrying pins under `if` emit branch-guarded precondition
  VCs the Link discharge cannot compose; implication form keeps every
  caller straight-line, and the three dispatchers call BOTH mode
  chains unconditionally.
- Closer recipes that worked: dispatch pins `simp_all
  [lib.close_sem_e]` (namespaced! bare name = unknown identifier);
  dispatchers `by_cases _hgate : lib.has_plain_flet f = 1 <;>
  simp_all (config := { zetaDelta := true })` (case the GATE not the
  datatype; zetaDelta bridges Verus tmp__N lets).
- has_plain_flet is NAT-valued (bool spec fn gates emit
  Classical.propDecidable ites that stick `decide` — the file's
  has_let idiom).
- prophecy/gates/isolates corollaries are now STRUCTURAL pins (pin
  placement visible in the goal shape; discriminators preserved as
  shape differences); forwards_contract semantic with the honest
  hoisted ∀-reading.
- Fixtures: only let-free-frame goals changed (Imp→All(0,·));
  wrap-forced fixtures (any plain FLet in scope) byte-identical.

Link discharge: 102 closed / 4 pending — residual = the structural
pins' own emitted proofs hoist tmp__N/let equation hyps with
census-Other provenance (DESIGN-leaf-normal-emission §5 Q1, known
open; emitter-side). Went 69/0 → 92/14 → 102/4; the wp_stm_sound
cascade is fully discharged.

NEXT = slice 2 (serializer): _h_hoist_i naming, FLetH classification,
Call-post/RetBind conversion, deepener; then fixtures/certs bridge.

### Slice 2 plan (2026-07-20)

Full plan doc: `DESIGN-b74-slice2-serializer.md` — evidence-first
fixture-cert regeneration (step 0, with per-family open questions —
the loop telescope question can change scope), serializer naming/
classification items with file+line specifics, the small model arity
additions (AssignH, RetLetH, statement hyp-name fields), the bridge
sweep, census-gated deferrals (shadowing, name collisions), and the
follow-up queue (discharge Q1 provenance, b70/71 closes, b69
decision, call-mut, loop-telescope redesign, cache fingerprint).

### Slice 2 COMPLETE (2026-07-21): bridge ↔ N1-hoist reconciliation done — probe9 18/20 close + 2 documented; probe11 1/5 close + 4 documented; ALL CLASSIFIED ✓ on both

**probe9 (fixtures): 18 close-ok, 2 documented honest-fails** — every
fixture family bridges: asserts/seq (add_capped, all three modes in
one fn), call ret-eq (use_clamped, use_multiarg, clamped_inc,
call_g2/g3_ob, quad_exec), if-join (count_down), assert-query
(mul_bound incl. the degenerate ensures-True goal), loops (sum_to,
find_square — uniform telescope + shadow mirror), plus double_exec,
id_generic, max_u64, mk_point, scope_shape, swap_pair, tri_one.
Documented: vec_read (stage-B reference-renderer coercion — telescope
matches production EXACTLY, the gap is leaf-rendering coercion
derivation; §7.7) and head_exec (N2 match-split — new machinery,
carded separately).
**probe11 (tgt): runtime__impl__4__clone CLOSES** — the differential
gate's first real-corpus bridge subject. Documented: apply_hom_gen/
apply_hom_inv (call-arg temp lets are typ-less `Wp::LetRaw` frames →
production wraps; the serializer typed and hoisted — plus auto-ref
arg coercion `Tactus.Ref.mk <arg>` in instantiated requires; new
Call-arm machinery) and the two lemma_runtime_word_view_* fns
(assert-forall skolem binders unmodeled — stage A has no quantifier
binder; SHOULD be a loud census rejection, not a non-bridging cert —
census-gap follow-up).
**Census check (§5.3):** call-generic 0, call-forall-path 0 hold;
remaining tgt tags = 1 call-mut (runtime.copy_word) + assert-query-
tactus (separate arcs, as planned).
**Suite state:** tactus-core gate 231/0 + package gate green, Link
discharge 144/6 steady (the 6 = pre-existing other-hyp/HoistEq
residual, unchanged through all of slice 2), e2e 551/0, lean_verify
unit 400/0.
**Follow-up queue (from the card, updated):** discharge Q1 composer
arm (HoistEq exists, main `9a88b6c`); b70/71 full closes (unblocked —
re-run vec_read/use_clamped bridges end-to-end + mutation-kill the
∀-path frame); b69 Tactus-mode assert-query decision; call-mut arm;
**NEW: call-arg temp lets + auto-ref arg coercion** (apply_hom class);
**NEW: assert-forall loud census rejection**; **NEW: stmts-olean
staleness investigation** (the misleading Type-mismatch/sorry
cascade); loop-telescope residual (none — done); cache
emitter-fingerprint (parked).

### Slice 2 Round D DONE (2026-07-21): loops close — probe9 18/20 + 2 documented honest-fails, ALL CLASSIFIED ✓

Serializer `loop_stm` emits the full uniform Loop node + the shadow
mirror. The lessons, in order of increasing subtlety:
1. **Hyp numbering is PER-GOAL-PATH, not a linear walk counter**
   (find_square evidence: `0 ≤ a + 1` is `_h_hoist_10` in BOTH the
   inner body and the outer re-close). The Loop statement is a SCOPE
   boundary: telescope names consume (`bounds/invs/cond`), the body
   numbers independently from the telescope end, and the post-loop
   path resumes from the same point.
2. **Freshening happens only in HOISTED goals.** Wrap-mode goals keep
   source names (goal-position lets shadow textually). Gate:
   `flet_forced`/`poison_forced` (split because the AssertQueryNl
   scope strips hyps but keeps lets); freshen iff prefix wrap-free.
   MIX case (shadow before a later wrap-forcer) = documented
   honest-fail (`hoist-mixed-shadow`, unhit).
3. **Branch state snapshots**: bound_names/rename_env/forcing flags
   restore per If-branch (count_down's `tmp__3` is a FIRST binding in
   each branch) and the fall-through counter advances past the
   forwarded ¬cond hyp.
4. **Renames apply to obligation texts too** (`oblig_leaf`/
   `neg_oblig_leaf`, and the RawExp Var arm — the DEEP reference
   leaves carry the freshened ids); the decrease obligation renders
   AFTER the body walk (the d_old VALUE stays loop-entry-plain).
5. **`inv_obligs_exit` (model addition, evidence-driven)**: re-close
   invariant obligations carry RENAMED texts distinct from init. Slot
   discipline: deep iff the renamed id is already in `deep_ids`
   (rename no-op — `n ≤ 1000` keeps the deep Span), else `atom_ob`.
FIXTURE-TOOLING FLAG (suspicious, worth its own look): the
`TactusStmts_*` module olean went STALE silently — the gate wrote a
fresh `.lean` (16:58) but did not rebuild the `.olean` (16:48), and
the next gate's Link layer then reported a "Type mismatch" +
"contains sorry" pointing everywhere but the real cause. Rebuilt the
olean manually to unblock. This looks like a stmts-module
rebuild-logic hole, distinct from the known binary-fingerprint gap.
Classified the two remaining BROKE fixtures (probe9 run.sh):
- vec_read — stage-B reference-renderer coercion (telescope matches
  production EXACTLY; `render_exp` derives `v.deref` where production
  writes `v`, misses the CallN-arg `Int.ofNat`; follow-up queue §7.7).
- head_exec — match-statement machinery (N2 match-split; stage A has
  no Match arm — card separately).

### Slice 2 Round C DONE (2026-07-21): uniform loop telescope — gate 231/0, suite 551/0

The `has_let` leading/non-leading switch is DELETED (the §2b loop
trigger). `loop_maintain_frame`/`loop_use_frame` now build ONE uniform
telescope: `mod_var_frames` (binder + NAMED `_h_hoist_i` bound hyp),
`binderprops_to_hyps` (named inv hyps), named cond hyp + poison bit,
and `_tactus_d_old` as an `FLetH` binder pair (`Loop` gains
`cond_poison`, `d_old_ty`, `d_old_eq_name`, `d_old_eq_prop`). The
render mode falls out of the GLOBAL wrap gate, exactly as production
behaves post-`8dcac64`. Fixtures: nested-loop fixture now pins the
old "non-leading" shape as gate-driven (a surviving plain `FLet`
wrap-forces; the SAME loop node hoists without it); sum_to fixture's
12 expected goals computed by `ref_wp` itself via `#reduce` (matches
the §2b hand-derivation incl. shadow-freshened body rebinds
`i_hoist1`/`acc_hoist1` as `AssignH` pairs). FLAGGED KNOB:
`wp_stm_sound` got `#[verifier::heartbeats(1600000)]` — the 15-field
Loop node doubles the termination VC's zetaDelta normalization of the
12-arg `loop_maintain_frame`; a per-fn whnf knob, no proof-content
change (analyzed the storm first: dead mframe let-bindings simp
normalizes anyway).

NEXT = Round D (serializer `loop_stm`): emit the new Loop fields —
bound/inv/cond `_h_hoist_i` ordinals (the loop's frame position), the
d_old eq pair (`_h__tactus_d_old_<id>_0_hoist1`,
`_tactus_d_old_<id>_0 = <measure>`), cond poison — plus the
shadow-rename mirror for loop-body rebinds (`i_hoist1`,
`_h_i_hoist1_hoist1` — production's `fresh()` + `rename_frame_vars`
over downstream leaf texts). Then fixture regen + probe9 loop
families (sum_to, find_square).

### Slice 2 Round B IN FLIGHT (2026-07-21): serializer — 16/20 bridges close

Serializer (sst_serialize.rs + CertCallLeaves) mirrors the 3-mode
emission: `hyp_ordinal` walk state → `_h_hoist_i` names (If-branch
snapshot/restore — cond is `_h_hoist_1` in BOTH branches;
AssertQueryNl resets to 0 — the sub-walk numbers independently);
Assign→AssignH/AssignR/plain classification via `local_typs` (shared
`assign_let_term`); Call-dest FLet→FLetH/FLetR (dest typ = the
instantiated CALLEE ret typ, NOT the SST local's auto-deref'd typ —
`ret_typ_subst`, plumbed through `CertCallLeaves`); RetLet→RetLetH
via `ret_typ`; poison = prop LExpr mentions an in-scope residue name
(`lexpr_mentions_var`, now pub(crate)); poisoned FLetH collapses to
plain Assign losslessly; `let_binder_typs` tracked at call dests so
the Return arm's TYPED-SPINE render inserts `.deref` on Ref-typed
call results (`r = tmp__1.deref`).
Beyond the mapped work: goals-transcriber residue peel (`goal_data`
peels production's `let tmp__1 := …; @loc leaf` into `GoalData::Let`
to match `residue_fold_e`); deepener `TypeAnnot` ERASURE arm (§3c
first item — vec_read's `((view v) : Seq Int)`); Return-arm Bnd-let
peel (Ghost/spec lets inside the return exp → AssignH statements,
use_multiarg); AssertQueryNl gained the query's degenerate
ensures-`True` obligation slot (model + serializer — production's
`and_all([])` fallback at query-scope end).
CLOSES (16): add_capped (full residue show: pure-hoist, hoist+residue,
and poison-wrap goals in one fn), call_g2/g3_ob, clamped_inc,
count_down, double_exec, id_generic, max_u64, mk_point, mul_bound,
quad_exec, scope_shape, swap_pair, tri_one, use_clamped, use_multiarg.
REMAINING BROKE (4), triaged:
- sum_to / find_square — LOOPS (Round C/D: loop-telescope
  simplification + loop hyp naming + shadow-rename mirror, all
  evidence-mapped in §2b).
- vec_read — stage-B REFERENCE-RENDERER divergence, not assembly:
  the binder telescope matches production EXACTLY; `render_exp` of
  the reference RawExp derives `v.deref` where production writes `v`
  (view-call arg) and misses the `Int.ofNat` cast on a CallN arg —
  the mirror has no fn-map to derive per-arg spec-call coercions from.
  Card as stage-B deep-leaf coverage (follow-up queue §7.7).
- head_exec — needs MATCH-statement machinery (the N2 match-split;
  stage A has no match arm — genuinely new scope, card separately).

### Slice 2 Round A DONE (2026-07-21, `a2c40ad`): model 3-mode — 230/0 + package gate green

The model (tactus-core/lib.rs) now mirrors production's post-`8dcac64`
partial hoist. `FrameList`: `FHyp` gained a uniform `poison` field
(serializer-computed — model leaves are opaque; `1` ⇒ prop mentions a
residue name ⇒ whole goal wraps) and a `FLetR(x, v)` residue-let
variant. Gate: `gate_wrap = has_plain_flet || has_poisoned_hyp`. Hoist
mode is TWO-PHASE on rendering (`close_e_tel` skips `FLetR`;
`residue_fold_e` folds residue lets around the leaf,
earliest-outermost — production's own structure) and semantics
(`close_sem_*_tel/res`), with the evaluation-context invariant
documented (residue values read after all telescope upds; adequate
because residue texts only mention earlier names). `StmData` gained
`AssignH` (hoistable), `AssignR` (residue), hyp names + poison bits on
`Assert`/`Assume`/`If`; `RetBind::RetLetH`. Poisoned `FLetH` collapses
to plain `FLet` losslessly. Proof layer: pin families re-split per
phase (u_cet/u_cer, u_cset/u_cser, u_csot/u_csor + u_gatep_*), the
three big inductions restructured (`holds_residue_fold` +
`holds_close_tel` + thin hoist wrappers; cso tel/res), `wp_stm_sound`
gained AssignH/AssignR arms. Link discharge 144/6 — pendings are the
pre-existing other-hyp (HoistEq) residual, UNCHANGED by the re-split.
NEW CLOSER RECIPE: `by_cases` on the COMPOSITE `lib.gate_wrap` works
for dispatchers; straight-line mode-pin callers need `lib.gate_wrap`
in the simp set (zetaDelta doesn't delta-unfold top-level defs).

NEXT = Round B (serializer, sst_serialize.rs): §3a `_h_hoist_i`
ordinal walk state (+ If-branch snapshot/restore), §3b classification
(Assign→AssignH/AssignR/plain via `local_typs`; Call-dest FLet→FLetH —
needs dest typ plumbed into `CertCallLeaves`; RetLet→RetLetH via
`ret_typ`; poison = prop text mentions an in-scope residue name),
§3d census tags (`hoist-name-collision`, `hoist-shadowed-let`,
`hoist-unclassifiable-let`, `hoist-residue-mention`). Smoke: probe9
use_clamped + vec_read decide-close (no residue there — exercises
naming + FLetH only). Then Round C (loop-telescope simplification per
the §2b evidence) + Round D (loop naming + shadow-rename mirror —
`i_hoist1`, `_h_i_hoist1_hoist1`).

### Slice 2 step 0 DONE + scope updates (2026-07-21)

Certs regenerated with current production (fixture 32/39 certified —
call-generic rejections gone; tgt 3 exec certs + 2 lemma certs).
Evidence table in DESIGN-b74-slice2-serializer.md §2b. Three scope
changes vs the 07-20 plan (§2c there), Danielle approved starting +
residue-mirroring 2026-07-21:
1. THREE goal modes (wrap / hoist / hoist+residue) — main's
   `8dcac64` partial hoist postdates the plan. Mirror residue in the
   model (Danielle's call, not honest-fail).
2. "Mentions-residue" poison is serializer-COMPUTED and carried as a
   frame mark (model leaves are opaque).
3. Shadow-rename mirror is IN SCOPE (was census-deferred): every
   loop-body rebind hits it (`i_hoist1`, `_h_i_hoist1_hoist1`).
4. Loop-telescope redesign trigger TRIPPED: `_h_ctx_N` gone from
   goal shapes (survives in the SST `inv_hyps` side-table only);
   nested loops = flat concatenation under one per-goal counter.
   `loop_maintain_frame`/`loop_use_frame` simplify — this section IS
   the card entry the plan's stop-and-card rule asks for.
Bonus: `HypProvenance::HoistEq` already landed on main (`9a88b6c`) —
discharge Q1 shrinks to the composer arm.
