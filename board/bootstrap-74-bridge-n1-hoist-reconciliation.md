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
