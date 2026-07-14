---
title: "W6d — bridge deepened: obligation leaves emit LeafE + refWp closes over ExprData (corpus coverage map)"
status: done
claimed_by: opus-b27
created: 2026-07-14T09:30:00Z
updated: 2026-07-14T05:05:00Z
---

## Description

Fourth rung of the W6 ladder (`DESIGN-W6-stageB.md` §4 pieces 4 + §5). W6a
(probe, `bootstrap-20`), W6b (mirror types + `render_exp`/`expr_eq` in
`tactus-core/lib.rs`, `bootstrap-21`), W6c (both serializer transcriptions —
`raw_exp`/`typ_data` ref-side, `lexpr_to_exprdata`/`lean_binop_opcode`
prod-side, `bootstrap-22`) all done. Both transcriptions are landed but
`#[allow(dead_code)]` — nothing feeds them into the emit path, so `close`/the
emitter still produce stage-A `GoalData::Leaf(u64)` and the bridge never
`decide`s `expr_eq`.

**W6d wires both transcriptions into the obligation-leaf emit + the bridge**, so
the fixture's cast-class obligation leaves are structurally certified (the
Friction-2 inconsistent-coercion class is finally caught). Then a census over
the corpus surfaces the coverage gaps to resolve.

**Done when:** for the bridgeable subset of the fixture corpus, obligation
leaves emit `GoalData::LeafE(ExprData)` on BOTH sides, `refWp` closes them via
`render_exp(rawExp)`, and the bridge `decide`s `expr_eq`; verdict-neutral
(flag-on == flag-off for the bridging fns; non-bridging fns stay fail-loud +
census-tracked). Mutation-kill at expression level is **W6e**.

**Blocked by:** nothing (W6c done). **Blocks:** W6e (mutation-kill + Tier-2).

---

## The architectural decision (confirmed this turn)

**Symmetric deepen is FORCED — both sides must emit `LeafE(ExprData)`.** The
bridge is `decide(goals_eq (ref_wp ctx sst) goals) = 1`, and `goals_eq` compares
constructor-for-constructor: a production `LeafE(ExprData)` never matches a
reference `Leaf(u64)`. So `refWp`'s obligation-producing fold (`close`) must
produce `LeafE(render_exp(rawExp))`, which means **the SST literal's obligation
slots must carry a `RawExp` mirror, not the current `u64`**. There is no cheaper
asymmetric path: the only asymmetric option (teach `goals_eq` to render an
`ExprData` back to text and compare to the `u64`) reverts the check to a string
compare — a buggy renderer renders a structurally-wrong `ExprData` to the
"correct" string and the bridge silent-passes, exactly the blind spot W6 exists
to close. Confirmed with the local model (127.0.0.1:8051, 2026-07-14): "To prove
the production side produced the correct STRUCTURE (not just a structure that
looks correct when rendered), you must compare ExprData against ExprData … the
cache churn is the price of the correctness guarantee."

**Consequence:** W6d needs a *second* shared-crate (`tactus-core/lib.rs`) churn
(after W6b's), touching `StmData`'s obligation representation + `close`/`refWp`.
Batch it — de-risk the shape here first, land it once (see W6d.1 below), same
discipline as W6a→W6b.

---

## Corpus coverage map (extracted from the on-disk fixture certs this turn)

Source: `bootstrap-fixture/out/lib/cert/*.cert.lean`, the `GoalData.Leaf N`
targets mapped back to their leaf-table text. This is the **expression-level**
roadmap for which `ExprData`/`RawExp` shapes the LIVE obligation leaves actually
need — the thing N4 (statement-level) and even the W6-stageB design (which
guessed from `sum_to`) could not fully produce. 13 fixture fns, their obligation
leaves classified:

| fn | obligation-leaf shapes | W6d status |
|---|---|---|
| `add_capped` | `r = x+y`; `0≤x+y ∧ x+y<2^64`; `tmp__1` (atom); … | **coverable** (Eq/And/Le/Lt/Add, atoms, lits) |
| `double_exec` | `r = 2*x`; `0≤x+x ∧ …` | **coverable** (+ Mul) |
| `quad_exec` | `r=4*x`; `x<1000`; `2≠0`; `tmp__2<1000`; `0≤tmp__1+a ∧ …` | **coverable** (+ Ne) |
| `count_down` | `r=0`; `0≤n-1 ∧ n-1<2^64`; **`0≤tmp__2 ∧ tmp__2<decrease_init0 ∨ tmp__2=decrease_init0 ∧ False`** | gap **G1** (`False` LitBool), Or |
| `find_square` | **`True`**; `a≤limit`; `limit<100`; `0≤limit-a ∧ limit-a<_tactus_d_old_0_0`; `0≤a*b ∧ …`; … | gap **G1** (`True` LitBool); `_tactus_d_old` = atom OK |
| `sum_to` | **`Int.toNat r = lib.tri (Int.toNat n)`**; `i≤n`; `n≤1000`; `Int.toNat acc = lib.tri (Int.toNat i)`; `acc≤1000*1000`; `0≤n-i ∧ n-i<_tactus_d_old_0_0`; … | **the cast class** — coverable (Cast handled both sides) |
| `head_exec` | **`r = lib.tree_head t.deref`** | gap **G2** (ref-side derived deref) |
| `mk_point` | **`p.x = a`**; `p.y = b` | gap **G3** (struct field proj, ref side) |
| `swap_pair` | **`r.1 = b`**; `r.2 = a` | gap **G3** (tuple field proj, ref side) |
| `max_u64` | **`x<y → (let r := let m:=y; m; r≥x ∧ r≥y)`**; **`¬(x<y) → (let r := let m:=x; m; …)`** | gap **G4** (Implies+Let+Not INSIDE a leaf, from If-fallthrough) |
| `scope_shape` | `lib.tri n ≥ 0`; `tmp__1` (atom) | **coverable** (App single-arg, Ge) |
| `id_generic` | `r = t` | **coverable** (Eq of atoms) |
| `tri_one` | `lib.tri 1 = 1` | **coverable** (App, lit) |

**Opcode coverage is already complete** for every binop that appears in a leaf:
`= ≠ < ≤ > ≥ + - * ∧ ∨ →` all map through `lean_binop_opcode`/`binop_opcode`
(`Eq..Implies` = codes 0–13), pinned in lockstep by `binop_opcode_alignment`.

---

## Gap taxonomy (what W6d must resolve; each needs a shared-crate touch)

**G1 — bool literals `True`/`False` in leaves.** `count_down` (decrease
disjunct `… ∧ False`) and `find_square` (`True` invariant). `ExprData`/`RawExp`
have no bool-literal variant → both transcriptions `ed-litbool` / `raw-const-bool`
fail-loud. Resolution: add `ExprData::LitBool(bool)` + `RawExp::LitBool(bool)`
(nullary-ish; `render_exp` maps straight through, `expr_eq` compares the bool).
Cheap. **Confidence: high** (shapes verified from certs).

**G2 — the ref-side deref is a DERIVED decoration-coercion, NOT an explicit
node. (Corrects a latent wrong assumption in the frozen W6b shape.)**
`head_exec`'s ensures is `r == tree_head(*t)`, `t : &Tree`. Production inserts
`.deref` NOT from an explicit SST deref node but as a **decoration-coercion**:
`expr_shared.rs:1038-1051` / `apply_deref_chain` bridge `from=[Ref] → to=[]` by
appending `.deref`, exactly parallel to how `Int.toNat` bridges `int→nat`. So
the RAW SST carries the call arg as `Var(t) : &Tree` (Ref-decorated) with **no
explicit deref** — the deref is the gap between the arg's `&Tree` type and the
callee's expected `Tree` param type. **The W6a probe's Case C models an explicit
`RawExp::Deref` node, and W6b's `render_exp` `.deref` arm handles it — but
`raw_exp` (the serializer) can never PRODUCE that node for an auto-deref'd
`&`-param.** Resolution: `render_exp`'s Call/Clip arm needs a `needs_ref_deref`
predicate parallel to `needs_nat_coercion` (`ref p` operand under a `named p`
target → wrap `FieldProj(_, deref_field())`), and `raw_exp`'s Call arm must put
the **callee's expected param type** (not the arg's own type) in the `argTy`
slot so the coercion target is right. The existing `RawExp::Deref` variant may
be dead-on-arrival for the serializer path (keep it only if an explicit-deref
SST source turns up — verify by dumping head_exec's raw SST in W6d.0).
**Confidence: high inference (decoration-coercion mechanism confirmed in
`expr_shared.rs`); the exact `arg.typ` value + whether `raw_exp` needs the
callee param type must be confirmed against a real head_exec SST dump in
W6d.0 before coding.**

**G3 — struct/tuple field projection in leaves.** `mk_point` (`p.x`), `swap_pair`
(`r.1`). Prod side handles these (`ExprData::FieldProj`, field id = interned
name). Ref side `raw_exp` has NO field-proj arm and `RawExp` has NO field
variant. Resolution: add `RawExp::Field(u64 /*field id*/, Box<RawExp>)` +
`render_exp` arm → `ExprData::FieldProj(render_exp(e), fieldid)`; `raw_exp` maps
the raw SST field op (`ExpX::UnaryOpr(Field …)` — confirm the exact VIR variant
in W6d.0). Note: `deref_field()=0` is reserved; real field ids intern the field
name text so ref/prod agree. **Confidence: high (shapes verified); exact VIR
field-op variant to confirm.**

**G4 — `Implies`/`Let`/`Not` INSIDE an obligation leaf (If-fallthrough).**
`max_u64`'s two leaves are the whole `x<y → (let r := let m:=y; m; r≥x ∧ r≥y)`
implication — an If-with-fall-through-to-common-Ret (cf. `bootstrap-19`
two-way-If-join / `bootstrap-17`) folds the branch condition + the let-bound
return into ONE obligation expression. This needs `ExprData::Let` + a `Not`
(unary) representation. **Recommend DEFERRING G4 to W6e/Tier-2** (`If/Let/Tuple`
fold-in) — it is structurally the deepest and only bites one fixture fn; keep
`max_u64` fail-loud (`ed-let`) in W6d so the cast-class win lands first.
**Confidence: high.**

**G5 — synthetic vars are atoms (no gap).** `_tactus_d_old_N_0`,
`decrease_init0`, `tmp__K` all render as plain `Var` → `Atom(interned id)` on
both sides; they cancel by id. Verified across `find_square`/`count_down`/`sum_to`.
No action.

---

## W6d.0 dump results — the map was WRONG in load-bearing ways (2026-07-14)

**Method.** Gated `raw_exp(e)` + `{:#?}` dump added at the top of `oblig_leaf`
(`sst_serialize.rs`), fixture cold-emitted with
`TACTUS_DUMP_OBLIG=1 … --tactus-emit-cert`, then **reverted** (clean tree +
rebuild). 50 obligation leaves dumped — the *actual* raw SST, not inferred from
rendered certs. This is the ground truth the on-disk-cert reading (Progress
entry above) could only guess at, and it **corrects the coverage map**: several
fns the map called "coverable" fail **today**, and two whole gap classes were
missed. The dump-first discipline paid for itself.

**`raw_exp` verdict over the 50 leaves:** 18 OK · 23 `raw-unaryopr` · 5
`raw-varat` · 1 `raw-const-nonint` · 1 `typ-typparam` · 1 `raw-call-nonfun` ·
1 `raw-bind`. Breakdown of the 23 `raw-unaryopr` by outermost `UnaryOpr`:
**10 HasType · 7 Box · 4 Unbox · 2 Field** (Box/Unbox also nest *inside* the
Field and deref leaves).

**Corrected gap taxonomy (supersedes G1–G5 above where they conflict):**

- **G0 (NEW — the dominant blocker, map missed it entirely).** `UnaryOpr::Box(_)`
  / `UnaryOpr::Unbox(_)` SMT-coercion wrappers wrap every boxed value: spec-fn
  args (`tri(1)` arg = `Box[Nat](Const 1)`), datatype args, field results,
  tuple elements. Semantic identity. **`raw_exp` must peel them transparently**
  (recurse into inner, drop the wrapper) exactly as `typ_data` already peels
  `Boxed`/`Decorate`. Without G0, G2/G3 are unreachable and even `tri_one`
  (map said "coverable") fails on `raw-unaryopr`. **This is the #1 unlock.**

- **G1 (CONFIRMED).** find_square `ensures true` dumps as literally
  `ExpX = Const(Bool(true))`. Add `RawExp::LitBool(bool)` + `ExprData::LitBool`.
  Note the count_down decrease `∧ False` is a *builder-synthesized*
  `ExprNode::LitBool(false)` (from the decrease-disjunct construction, cf.
  `and_all([])=LitBool(true)`), NOT a raw-SST const — so G1's `raw_exp` arm is
  needed only for genuine source bool literals (find_square); the synthesized
  side is a `lexpr_to_exprdata` `ExprNode::LitBool` arm.

- **G2 (mechanism CONFIRMED, shape CORRECTED, and SIMPLIFIED).** head_exec
  `r == tree_head(*t)` dumps as `Eq(Var(r):U64, Call(tree_head, [], [arg]))`
  where `arg = UnaryOpr(Box[&Tree], VarAt(t, Pre))`, arg.typ =
  `Boxed(Decorate(Ref, Datatype(Tree)))`. So: **(a) the board was RIGHT — there
  is NO explicit deref node; `*t` in spec is transparent and the arg stays
  `&Tree`. (b) the board was WRONG about the surface shape — it is NOT a plain
  `Var(t):&Tree`; it is Box-wrapped around a `VarAt(t,Pre)` read (needs G0 +
  G7). (c) SIMPLIFICATION — after G0-peel the arg mirror-type is `TyRef(Tree)`,
  and the render rule is simply: _a spec-fn `Call` arg whose mirror type is
  `TyRef(T)` gets a `.deref` coercion_ (spec fns never take `&T`, so this is
  uniform). `render_exp` does NOT need the callee's expected param type — the
  `TyRef` tag on the arg is sufficient signal. The board's worry about
  threading the callee param type into `RawExp::Call` is moot.** The existing
  `RawExp::Deref` variant is **confirmed dead-on-arrival** for the serializer
  (no explicit-deref SST source exists) — delete it or leave it unused.

- **G3 (CONFIRMED + tuple-index detail).** mk_point `p.x` dumps as
  `Field(FieldOpr{datatype:Point, variant:"Point", field:"x"})(Unbox(Box(Var
  p)))`; swap_pair `r.0` as `Unbox(Field(FieldOpr{datatype:Tuple(2),
  variant:"tuple%2", field:"0"})(…))`. Add `RawExp::Field(u64 field_id,
  Box<RawExp>)` + peel surrounding Box/Unbox (G0). **Tuple caveat: VIR field
  `"0"` but production renders `.1` (1-indexed shift — the on-disk cert leaf is
  `r.1 = b`), so the ref-side field-id must intern the SHIFTED name to match
  production's atom id.** Struct fields (`"x"`) render `.x` → intern `"x"`
  directly. Confirm production's `lean_ast` FieldProj field text for both in
  W6d.1.

- **G6 (NEW — the overflow class, map missed it).** Arithmetic overflow
  obligations dump as `UnaryOpr::HasType(IntRange)(e)` (add_capped `s = x+y` →
  `HasType(U64)(x + y)`); production **expands** this to `0 ≤ e ∧ e < 2^bound`.
  10 of the 23 `raw-unaryopr` leaves are HasType. So add_capped / double_exec /
  quad_exec / count_down-body / find_square / sum_to-body are **NOT coverable
  today** (map was wrong). **DECIDED (Danielle, 2026-07-14): Option (i)** —
  `raw_exp` emits a first-class `RawExp::HasType(range, e)` and `render_exp`
  reproduces the exact `0≤e ∧ e<2^bound` expansion production uses. Rejected
  option (ii) (WP synthesizes the bound directly, parallel to
  `decrease_oblig_leaf`): synthesizing silently would re-create the same "map
  blindness" W6d.0 just caught — the deep bridge's whole point is that the
  reference path *independently re-derives* the structure, so the HasType
  identity must stay alive until the final render (single source of truth;
  observable in the raw dump; one-line change in `render_exp` if production ever
  changes the expansion, e.g. to a bit-vector check). **G6 gates most of the
  "easy" fns** — do it in W6d.1, not later.

- **G7 (NEW).** Ensures read params as `VarAt(vid, Pre)` (pre-state), not
  `ExpX::Var(vid)` — 5 `raw-varat` leaves (add_capped/max_u64/double_exec/
  quad_exec ensures, head_exec's `t`). `raw_exp` must handle `VarAt(vid, _)`
  like `Var` (intern the same binder id; production renders it as bare `x`).
  Low risk. NB: *inside* bodies params still read as plain `Var` (the
  add_capped 87 overflow has `Var(x)+Var(y)`), so it's specifically the
  ensures/pre snapshot.

- **G4 (unchanged — DEFER).** The `max_u64` If-fold `Implies+Let+Not` leaf lives
  on the *goal* path (`goal_data`/`GoalShape`), NOT `oblig_leaf` — the dump only
  saw max_u64's simple `r≥x`/`r≥y` ensures (G7 varat). Defer to W6e/Tier-2.

- **G5 (CONFIRMED no-gap).** Synthetic vars are atoms. Holds.

- **Also out of scope (fail-loud + census):** `typ-typparam` (id_generic `r==t`,
  generic type param → `TypData`), `raw-call-nonfun` (count_down `count_down(n-1)`
  = a `CallFun::Recursive`/exec call, not a spec `Fun`), `raw-bind` (fill_zeros
  `forall|k| …` quantifier). None are cast-class; keep them census-tracked.

**Net effect on W6d.1 scope:** the shared-crate batch is BIGGER than the map
implied. Priority order for `raw_exp`/`render_exp`: **G0 (Box/Unbox peel) first
— it unblocks everything — then G7 (VarAt), G1 (LitBool), G3 (Field + tuple
shift), G6 (HasType, via reference-WP synthesis per option ii), and G2 (TyRef ⟹
`.deref` render rule).** With G0+G7+G1 alone, the pure-value fns (tri_one,
scope_shape, id_generic-minus-typparam) become coverable; G6 unlocks the
arithmetic fns; G2+G3 unlock the datatype/struct/tuple fns.

---

## Phased plan (probe-first, each independently checkable)

- **W6d.0 — confirm the SST shapes (NO code). ✅ DONE (2026-07-14, opus-b23).**
  See the "W6d.0 dump results" section above — dumped all 50 obligation leaves,
  reverted clean. Confirmed G1; confirmed G2's *mechanism* + corrected its
  *shape* + simplified its render rule; confirmed G3 + found the tuple-index
  shift; and surfaced **three gaps the map missed — G0 (Box/Unbox peel, the
  dominant blocker), G6 (HasType overflow class), G7 (VarAt-Pre param reads).**
  W6d.1 scope is bigger than the map implied.
- **W6d.1a — the expression-mirror vocabulary (shared-crate churn). ✅ DONE
  (2026-07-14, opus-b23).** In `tactus-core/lib.rs`: added the G1/G3/G6/G2
  vocabulary + render/eq/type arms + extended `expr_mirror_kernel_computes`
  with a passing-and-killing case per gap. Verified **50/0** with the Lean
  backend (`--lean-backend --lean-all-proofs`), clean axiom closure. Verdict-
  neutral (additive; nothing downstream emits the new variants yet). See the
  "W6d.1a landing" section below for the shapes + three design deviations. This
  is the ONE datatype churn; W6d.1b/W6d.2 add no new mirror variants.
- **W6d.1b — the refWp obligation rewire (NO new mirror variants).** In
  `tactus-core/lib.rs`: a `close_e(frame, rawExp)` folding a frame around
  `LeafE(render_exp(rawExp))` (mirrors `close`); switch the obligation-emitting
  `refWp` arms to `close_e`; change `StmData`'s obligation slot(s) `u64 →
  RawExp`. This is the cache-churny StmData edit (invalidates the stm layer +
  the `ref_wp_*` proofs). Defer G4 (`Let`-in-leaf). **Split into three sub-steps
  by container shape** (the obligation lives in three shapes — this decides how
  much new type surgery each needs):
  - **W6d.1b-i — the `Assert` obligation slot (BARE `u64` → `RawExp`). ✅ DONE
    (2026-07-14, opus-b23).** `Assert(u64,u64)` → `Assert(RawExp,u64)`; added
    `close_e` + `atom_ob(id) = Var(id,TyBool)`; wired `wp_stm`'s Assert arm to
    `close_e`. All 16 Assert fixtures wrapped (`atom_ob(N)`) + their expected
    `Leaf(N)` → `LeafE(Atom N)`. Verified **52/0** (Lean backend, clean axiom
    closure). This is the shape de-risk — `close_e`/`render_exp` now
    kernel-`decide`s on the REAL refWp Assert arm. See the "W6d.1b-i landing"
    section below.
  - **W6d.1b-ii — the LeafList obligation slots (`Call.reqs`, `Ret.es`). ✅
    DONE (2026-07-14, opus-b23).** NEW dedicated `RawExpList` (Danielle's call:
    distinct type, not a polymorphic LeafList — keeps `LeafE`/`Leaf` unmergeable)
    + `close_each_e` mirroring `close_each`; wired `wp_stm`'s Call + Ret arms.
    Verified **54/0**. See the "W6d.1b-ii landing" section below.
  - **W6d.1b-iii — the Loop obligation slots (`inv_obligs`, `decrease_oblig`).
    ✅ DONE (2026-07-14, opus-b23).** `decrease_oblig` bare `u64 → RawExp` (like
    Assert). The invariant obligations moved to a NEW parallel field
    `inv_obligs: RawExpList` (Design C — see the landing note below), folded via
    the already-proven `close_each_e`; `inv_hyps` stays a `BinderList` (name,
    HYP) for the frame telescope, UNTOUCHED. Wired the Loop init/maintain/
    decrease arms; deleted the dead `close_each_binderprop`. Fixtures: sum_to
    monster (init+maintain Leaf 23/24/25/26 → LeafE Atom, decrease Leaf 39 →
    LeafE Atom 39), nested_loop (direct `close(·,35/43)` → `close_e(·,atom_ob
    35/43)`), stm_size test (4 → 5). Verified **52/0**. **W6d.1b COMPLETE** (all
    three container sub-steps i/ii/iii landed).
- **W6d.2 — serializer wiring.** Split into 2a (opaque-fallback plumbing) +
  2b (deep transcription), same de-risk discipline as W6d.1a→1b.
  - **W6d.2a — opaque-fallback emission (type-correctness + verdict-neutral).
    ✅ DONE (2026-07-14, opus-b23).** All FIVE obligation slots switched from
    the stage-A `u64`/`LeafList` text to the new deep `RawExp`/`RawExpList`
    literals, using the `atom_ob` opaque fallback (`RawExp.Var id TyBool`, which
    refWp renders to `LeafE(Atom id)`), and `goal_data` emits `GoalData.LeafE
    (ExprData.Atom id)`. The interned ids are UNCHANGED, so the bridge stays
    verdict-neutral (opaque atoms, same cancellation as stage-A) — but the
    emitted cert now type-checks against the W6d.1b tactus-core defs again. This
    covers the user-flagged Loop 12-arg format (`inv_obligs` inserted) +
    `decrease_oblig`→`RawExp`, plus the parallel Assert/Ret/Call changes (they
    MUST move together — an Assert-carrying cert won't elaborate against
    `Assert(RawExp,u64)` while any slot still emits a bare Nat). See the
    "W6d.2a landing" section below (Rust 327/0 + two rebuild-free end-to-end
    bridge checks). `raw_exp`/`typ_data`/`lexpr_to_exprdata` stay
    `#[allow(dead_code)]` — 2a does NOT wire them (no deep structure yet).
  - **W6d.2b — deep transcription (the Friction-2 catcher).** Split into 2b-1
    (reference-side `raw_exp` peel/alias arms) + 2b-2 (remaining reference arms +
    goal-side G1 + the emit gate).
    - **W6d.2b-1 — reference `raw_exp` G0/G7/G1 arms. ✅ DONE (2026-07-14,
      opus-b24).** Box/Unbox peel (G0), VarAt→Var (G7), bool literal (G1) added
      to `raw_exp`; 4 unit tests; `lean_verify` lib 331/0; still dead-code
      (verdict-neutral). See the "W6d.2b-1 landed" Progress entry below.
    - **W6d.2b-2 — G6/G3 reference arms + goal-side G1 arm + the emit gate.
      ✅ DONE** (arms: 2026-07-14 opus-b25; **emit gate: 2026-07-14 opus-b26**).
      The `raw_exp`/`lexpr_to_exprdata` vocabulary is complete AND now wired into
      the emit path via a new `oblig_slot` helper (deep-or-atom obligation slot,
      wrapping coverable `raw_exp(e)` in `RawExp.Span(loc, ·)` + recording the
      leaf id in `deep_ids`) at all three deepenable sites (Assert / ensures-Ret
      / Loop-inv), and `goal_data` gates on `deep_ids`. **Coordination = the
      "ob-drives" asymmetric gate** (single-pass; the symmetric "both fall back"
      would need a goal pre-pass because the stm walk runs BEFORE the goal walk —
      circular). Forced-atom sites (Call reqs, Loop decrease, if-cond hyps) never
      enter `deep_ids` → their goals auto-stay atom (verdict-neutral for free).
      Verified **`lean_verify` lib 338/0** (+3 gate tests) + confirmed
      stm_size/goal_count-invariant. See the "W6d.2b-2 emit gate landed"
      Progress entry below.
- **W6d.3 — bridge over the bridgeable subset, verdict-neutral.** Re-emit the
  fixture (release-binary rebuild) — this also **regenerates the golden**
  `testdata/add_capped.cert.lean` to the W6d.2a emission (currently stale but
  round-trip-green); bridge (probe9-style) the fns whose leaves are all coverable
  (add_capped, double_exec, quad_exec, sum_to, scope_shape, id_generic, tri_one,
  + head_exec/mk_point/swap_pair once G2/G3 land). Confirm flag-on == flag-off
  verdict and the census reports the fail-loud remainder (max_u64 `ed-let`).
- **W6e (separate task) — mutation-kill + Tier-2.** Drop an `Int.toNat` at one
  `sum_to` site on the prod side → the bridge must FLIP (the Friction-2 kill);
  then fold in G4 (`If/Let/Tuple`).

---

## Progress

- (2026-07-14, opus-b23) **Task opened + corpus coverage map extracted +
  architecture confirmed.** Read both sides end-to-end (the W6b lib.rs mirror
  types/`render_exp`/`expr_eq`, the W6c `raw_exp`/`lexpr_to_exprdata`
  transcriptions, the `close`/`refWp` fold). Extracted the obligation-leaf
  shapes for all 13 fixture certs from disk (table above) → the expression-level
  coverage roadmap. Confirmed the symmetric-deepen architecture is forced (local
  model concurs). Surfaced **five gap classes** (G1–G5), two of which the design
  docs had NOT anticipated: **G1** (`True`/`False` bool literals in
  decrease/invariant leaves) and **G3** (struct/tuple field projection, ref
  side). **G2 corrects a latent wrong assumption in the frozen W6b shape**: the
  ref-side `.deref` is a DERIVED decoration-coercion (confirmed via
  `expr_shared.rs:1038-1051` / `apply_deref_chain`, parallel to `Int.toNat`),
  NOT the explicit `RawExp::Deref` node the W6a probe + `render_exp` `.deref`
  arm assume — so `render_exp` needs a `needs_ref_deref` coercion and `raw_exp`
  must target the callee param type. **G4** (`max_u64` If-fallthrough
  `Implies+Let+Not` in one leaf) recommended DEFERRED to W6e/Tier-2. Confirmed
  the W6a probe baseline still runs green (rc=0, axioms clean) — the shared
  shape is intact for W6d.1 to build on. **No code edited this turn** (W6d.1 is a
  deliberate single shared-crate churn — de-risk the shapes in W6d.0 first, per
  the W6a→W6b discipline). **Next = W6d.0** (dump the SST shapes to confirm
  G1/G2/G3 before the lib.rs batch).

- (2026-07-14, opus-b23) **W6d.0 executed — raw-SST dump, gap taxonomy
  corrected.** Instrumented `oblig_leaf` with a gated `raw_exp(e)` + `{:#?}`
  dump, cold-emitted the fixture with `--tactus-emit-cert TACTUS_DUMP_OBLIG=1`
  (50 leaves), then reverted (tree clean, rebuilt green: vstd 1530/0). Ground
  truth **overturned parts of the on-disk-cert coverage map**: (1) **G0 (NEW)**
  — pervasive `UnaryOpr::Box/Unbox` SMT wrappers are the #1 blocker (11 of 32
  failing leaves outermost, nested in most others); `raw_exp` must peel them
  like `typ_data` peels `Boxed`. (2) **G6 (NEW)** — arith overflow obligations
  are `UnaryOpr::HasType(range)(e)` that production expands to `0≤e ∧ e<2^bound`
  (10 leaves); so add_capped/double_exec/quad_exec/count_down/find_square/sum_to
  are NOT coverable today — prefer synthesizing the bound in the reference WP
  (parallel to `decrease_oblig_leaf`). (3) **G7 (NEW)** — ensures read params as
  `VarAt(Pre)` not `Var` (5 leaves). (4) **G2 confirmed+corrected**: no explicit
  deref node (mechanism right), but arg is `Box[&Tree](VarAt(t,Pre))` not plain
  `Var(t):&Tree`; render rule simplifies to "spec-fn Call arg of mirror-type
  `TyRef(T)` ⟹ `.deref`" (no callee param type needed); `RawExp::Deref` is
  dead-on-arrival. (5) **G3 confirmed** + tuple-index shift (VIR `"0"` →
  production `.1`). (6) **G1 confirmed** (`Const(Bool(true))`). Full corrected
  taxonomy + revised W6d.1 priority order (G0→G7→G1→G3→G6→G2) in the section
  above. **Next = W6d.1** — the shared-crate batch, now scoped against real
  shapes. No production code left changed this turn (probe reverted).

- (2026-07-14, opus-b23) **W6d.1a landed — expression-mirror vocabulary
  verified 50/0.** One edit to `tactus-core/lib.rs` (the single datatype
  churn), verified with `TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus
  --crate-type=lib --lean-backend --lean-all-proofs lib.rs` → **50 verified, 0
  errors**, "44 modules elaborated … composition + axiom closures
  kernel-verified" (no `WellFounded.fix`/`Classical`). What landed:
  - **G1** — `ExprData::LitBool(nat)` + `RawExp::LitBool(nat)`; `render_exp`
    passes it through; `expr_eq` compares the nat; `ed_tag` = 7;
    `ed_litbool_val` accessor.
  - **G3** — `RawExp::Field(u64 field_id, TypData field_ty, Box<RawExp>)`;
    `render_exp` → `ExprData::FieldProj(render(base), field_id)` (reuses the
    existing `ExprData::FieldProj`); `type_of(Field) = field_ty`.
  - **G6** — `RawExp::HasType(u64 width, Box<RawExp>)`; `render_exp` reproduces
    production's `type_bound_predicate` unsigned expansion
    `BinOp(And, BinOp(Le, Lit 0, e), BinOp(Lt, e, Lit 2^width))` with the
    canonical opcodes (And=11/Le=3/Lt=2), `e` rendered once and reused in both
    conjuncts; `2^width` via the new `pow2`; `type_of(HasType) = TyBool`.
  - **G2** — `needs_ref_deref` (TyRef arg → 1) + `deref_if`; `render_exp`'s Call
    arm now composes nat-coercion THEN ref-deref, so a bare `&T`-typed Var arg
    (the real head_exec shape, no explicit `Deref` node) auto-derefs to
    `FieldProj(_, deref_field())`. The explicit-`Deref` Case-C path presents its
    pointee type so `needs_ref_deref = 0` — no double-deref.
  - **kernel guard** — `expr_mirror_kernel_computes` gained one
    render+eq==1 (correct) and one render+eq==0 (mutation kill) per gap: G1
    (value flip), G6 (wrong bound width 2^32 vs 2^64), G3 (dropped `.x`), G2
    (dropped auto-deref). All decide.

  **Three design deviations, each a general constraint worth remembering:**
  1. **Spec `bool` → Lean `Prop` → `decide` sticks.** A `bool` field renders as
     the Lean *proposition* `True`/`False`; its equality needs
     `Classical.propDecidable` (noncomputable) and freezes `decide`. So the G1
     payload is a **`nat`** (0/1), matching the crate's uniform nat-tag idiom
     (`td_tag`/`ck_tag`/every `_eq` returns nat). **No future mirror variant may
     carry a `bool`.** (First tried a bare-`if x` branch instead of `==` — still
     stuck, because the *field itself* is Prop, not just the comparison.)
  2. **Recursive `pow2` doesn't kernel-reduce.** `pow2(n) = if n==0 {1} else
     {2*pow2(n-1)}` with `decreases n` lowers to `noncomputable def … termination_by`
     = `WellFounded.fix` (recursion on `Int.toNat(n-1)` is not a structural
     `Nat` subterm), which the kernel does NOT unfold under `decide` — it froze
     `render_exp(HasType 64 …)` at an un-normalized `Lit (pow2 64)`.
     (`render_exp` itself reduces because it's *structural* on `re`.) Fix:
     `pow2` is a **non-recursive finite width→bound table** (`if n==8 {256}
     else if n==16 …`), reducing via `Nat.decEq`. Still option-(a) faithful
     (width `n` observable in the RawExp; independent of production's
     `two_pow_str`) — just table- not doubling-based. **General rule: anything
     the reference computes inside a `decide`d render path must be non-recursive
     or structural-on-a-constructor — no `decreases`-on-arithmetic.**
  3. **2^128 overflows the Rust macro literal parser** (`u128::MAX + 1`) — write
     it as `(2^64_lit * 2^64_lit) as int` (exact in spec `int`, still reduces).
     u8/u16/u32/u64 fit directly.

  **Verdict-neutral / not yet wired.** `close`/refWp still emit `Leaf(u64)`; the
  new `RawExp` variants have no producer yet (`raw_exp`/`lexpr_to_exprdata` in
  `sst_serialize.rs` are still `#[allow(dead_code)]` and untouched — they
  produce *text*, don't match the tactus-core types, so this churn doesn't
  affect their build). The W3 tgt gate is unaffected by construction.
  **Next = W6d.1b + W6d.2** (close_e + StmData obligation-slot `u64→RawExp`;
  then serializer wiring: raw_exp G0 Box/Unbox peel + G7 VarAt + the
  LitBool/Field/HasType arms; oblig_leaf emits the RawExp mirror wrapped in
  `Span`; goal_data emits `LeafE`).

- (2026-07-14, opus-b23) **W6d.1b-i landed — the `Assert` obligation slot is
  now a deep `RawExp`; `close_e` verified 52/0.** The first of W6d.1b's three
  container sub-steps (see the split in the plan above). What changed in
  `tactus-core/lib.rs` (one datatype-churn edit + fixtures):
  - **`close_e(f: FrameList, ob: RawExp) -> GoalData`** — mirrors `close`
    entry-for-entry (same `All`/`Imp`/`Let` spine) but the terminal is
    `LeafE(render_exp(ob))` instead of `Leaf(u64)`. `#[structural_decreases]`
    on `f`; placed right after `close` (after `render_exp`, so the def order is
    clean).
  - **`atom_ob(id) = Var(id, TyBool)`** — the bare-atom obligation. `render_exp`
    maps it to `Atom(id)`, so `close_e(f, atom_ob(id))` folds the SAME spine as
    `close(f, id)` and terminates in `LeafE(Atom id)`. This is what the fixtures
    (and, W6d.2, the serializer) use wherever the raw SST leaf is not yet one of
    the deepened `RawExp` shapes (G0–G7) — the opaque ids keep matching by id.
  - **`StmData::Assert(u64, u64)` → `Assert(RawExp, u64)`** — only the obligation
    (1st) field deepens; the bare-hyp (2nd) field stays `u64` (hypotheses are
    not deepened, only obligations). `wp_stm`'s Assert arm now emits
    `close_e(f, o)`; `frame_after`/`stm_size` already ignored the field
    (`_o`), so no other match changed.
  - **All 16 Assert fixture sites** wrapped `N → atom_ob(N)`; their expected
    `Leaf(N) → LeafE(Atom N)` (Assert-derived only: leaf ids 9/10/11/13/15/17/
    18/21/40 — the sum_to monster's Leaf 18/21 and cd19's Leaf 13/17 edited
    surgically; the 13 non-Assert `Leaf(9)`/`Leaf(10)` in `goal_eq`/`goal_size`
    test data correctly stay `Leaf`).
  - **`probe_close_e`** guard: `close_e` has the same `goal_size` as `close`,
    produces `LeafE(Atom 9)`, and `goal_eq(LeafE(Atom 9), Leaf 9) == 0` — the
    mutation-sensitivity that makes the deep bridge meaningful (a production
    `LeafE` can never silently match a reference `Leaf`).

  **Verified 52/0** (`--lean-backend --lean-all-proofs`, 46 modules elaborated,
  composition + axiom closures kernel-verified — no `WellFounded.fix`/`Classical`).
  Up from 50: the two added proofs. **Cache:** this is a datatype-shape churn
  (StmData gained a `RawExp` field → base-hash change), so the whole crate
  re-elaborated — expected, ~2min cold.

  **Key finding that de-risks the rest — the serializer coupling is at the LEAN
  level, not the Rust build.** `sst_serialize.rs` emits `StmData` as Lean *text*
  (`format!("({}.StmData.Assert {} {})", NS, oblig, hyp)`), NOT as constructed
  Rust `tactus_core::StmData` values. So changing tactus-core's `StmData` type
  does NOT break the serializer's Rust compile, and cert emission is gated
  (`--tactus-emit-cert`, test-quiet) — **the W3 tgt gate and the e2e suite stay
  green by construction.** The only place the type change bites is when a cert is
  actually elaborated (W6d.3): the emitted `.Assert 15 14` text (bare Nat in the
  RawExp slot) will fail Lean type-check until W6d.2 rewrites `oblig_leaf`'s
  emission to a `RawExp` literal (e.g. `(lib.RawExp.Var 15 lib.TypData.TyBool)`
  for the atom case, or the deep G0–G7 shapes). W6d.1b-i is verdict-neutral: no
  producer emits the new Assert shape yet.

  **Verdict-neutral / not yet wired** (same as W6d.1a): `close`/refWp's other
  obligation arms (Call/Ret/Loop) still emit `Leaf(u64)`; the serializer is
  untouched. **Next = W6d.1b-ii** (RawExpList + `close_each_e` for Call.reqs/
  Ret.es), then **W6d.1b-iii** (Loop decrease_oblig bare-slot + inv_hyps prop
  container), then **W6d.2** (serializer text emission). G4 (`Let`-in-leaf)
  stays deferred to W6e.

- (2026-07-14, opus-b23) **W6d.1b-ii landed — `Call.reqs` / `Ret.es` now carry
  DEEP `RawExpList` obligations; `close_each_e` verified 54/0.** The second of
  W6d.1b's three container sub-steps. What changed in `tactus-core/lib.rs` (one
  datatype-shape churn + fixtures):
  - **`RawExpList { Nil, Cons(Box<RawExp>, Box<RawExpList>) }`** — a DEDICATED
    list (Danielle's call, confirmed this turn), NOT a polymorphic `LeafList`.
    Two reasons: (1) `LeafList` is still shared by `FnCtxData.enss` /
    `hyps_of_leaves`, where the element MUST stay an opaque `u64` (hypotheses are
    not deepened); (2) keeping the deep list a distinct type keeps the two
    element worlds unmergeable — a `LeafE(render_exp …)` can never silently match
    a stage-A `Leaf(u64)` (the `goal_eq` safety condition). The element is
    `Box<RawExp>`, mirroring `GoalList::Cons(Box<GoalData>, …)` (compound
    elements boxed; only primitive-element lists like `LeafList`/`BinderList`
    inline the head).
  - **`raw_exp_list_len`** (deep analogue of `leaf_len`) + **`close_each_e(f,
    RawExpList)`** = `close_e` mapped over the list (deep analogue of
    `close_each`; each terminal is `LeafE(render_exp(ob))`).
  - **`StmData`:** `Call.reqs: Box<LeafList> → Box<RawExpList>`; `Ret(Box<LeafList>,
    RetBind) → Ret(Box<RawExpList>, RetBind)`. `stm_size`'s Call/Ret arms →
    `raw_exp_list_len`; `wp_stm`'s Call/Ret arms → `close_each_e`. No other
    `match` arm changed (`frame_after`/`diverges` ignore the es field).
  - **All fixtures rewired:** every `Ret.es` / `Call.reqs` `LeafList` →
    `RawExpList` with the ids wrapped `N → Box::new(atom_ob(N))` (opaque ids ride
    through the deep path as `Var(id,TyBool)` → `Atom(id)`, matching stage-A by
    id — same discipline as W6d.1b-i's Assert). Expected Ret/Call goals flipped
    `Leaf(N) → LeafE(Atom N)`: `ref_wp_ret_return_binding` (Leaf 12 ×2), sum_to's
    final Ret (Leaf 7), b17's diverging Ret (Leaf 7), cd19's two Rets + the
    mutation-kill head (Let(6,10,·) ×3, Leaf 5), `call_pass_through`'s req goal
    (`Imp(100, Leaf 7)` ×3, incl. the mutation-kill's first goal so the ONLY diff
    stays the `99` let-value), and the `stm_size` Call/Ret size tests (values
    unchanged — `raw_exp_list_len` == `leaf_len` on the same shapes).
  - **`close_each` (the LeafList version) DELETED** — it went dead when Call/Ret
    deepened (Loop uses `close_each_binderprop`; Call/Ret use `close_each_e`).
    Confirmed no callers in-file or in `source/` (grep). Deleted rather than kept
    (local model's steer, aligns with the "no dead code" discipline: the crate
    already fully re-elaborates from the datatype churn, so git is the undo
    buffer — retaining superseded logic is pure debt).

  **Verified 53/0** (`--lean-backend --lean-all-proofs`, 46 modules elaborated,
  "composition + axiom closures kernel-verified" — no `WellFounded.fix`/
  `Classical`). The `decide` bridge holds through every edited fixture (sum_to
  monster, cd19 two-way join, call_pass_through both post-shapes + mutation-kill,
  ret-binding, b17 fall-through). Cache: RawExpList added + StmData field-type
  change = base-hash churn → whole crate re-elaborated (~2min cold, expected).

  **Serializer coupling reconfirmed at the LEAN-TEXT level (extends W6d.1b-i).**
  `grep -rn 'StmData::Ret|StmData::Call|LeafList|RawExpList' source/` = ONLY
  comments, `format!("{}.LeafList.Cons …")` Lean-text builders, and expected-Lean
  test strings; NO Rust `tactus_core::StmData::Ret/Call` value construction, and
  `RawExpList` is absent from source entirely (its producer arrives in W6d.2). So
  the type change does NOT break the Rust build; the **W3 tgt gate + e2e suite
  stay green by construction.** ⚠ **W6d.2 to-do surfaced:**
  `source/lean_verify/src/sst_serialize_tests.rs:35` hardcodes the OLD expected
  string `(lib.StmData.Ret (Tactus.Box.mk lib.LeafList.Nil) lib.RetBind.RetNone)`
  — it passes today (serializer output unchanged, string-eq only) but must flip
  `lib.LeafList` → `lib.RawExpList` (and wrap the obligation as a `RawExp`
  literal) when `oblig_leaf`/Ret emission is wired in W6d.2, or the emitted cert
  won't type-check against the new tactus-core defs (the W6d.1b-i note, now for
  Ret/Call too).

  **Next = W6d.1b-iii** (Loop: `decrease_oblig` bare `u64 → RawExp` like Assert;
  `inv_hyps` `BinderList` PROP slot → a `(u64 name, RawExp prop)` container +
  `close_each_binderprop_e`; nested_loop's Leaf 35 direct `close` → `close_e`),
  then **W6d.2** (serializer text emission: `raw_exp` G0 Box/Unbox peel + G7
  VarAt + LitBool/Field/HasType arms; `oblig_leaf` emits the `RawExp` mirror
  wrapped in `Span`; `goal_data` emits `LeafE`). G4 (`Let`-in-leaf) stays
  deferred to W6e.

- (2026-07-14, opus-b23) **W6d.1b-iii landed — the Loop obligation slots are
  now DEEP; verified 52/0. W6d.1b (all three container sub-steps) COMPLETE.**
  The third and final container sub-step.

  **The plan's `(name, RawExp)` container was BROKEN — corrected to Design C.**
  The board's stated fix ("`inv_hyps` … needs a `(u64 name, RawExp prop)`
  container") does NOT work: `inv_hyps`'s prop slot has a DUAL ROLE — it is the
  init/maintain OBLIGATION (via `close_each_binderprop` → must deepen) AND the
  maintain/use frame HYPOTHESIS (via `binders_to_frame` → `FBind(name, prop, …)`
  and `binderprops_to_hyps` → `FHyp(prop, …)`, both of which need a bare `u64`
  — hypotheses are not deepened). Turning the prop slot into a `RawExp` breaks
  the two frame builders (FrameList holds `u64` hyps only). Two fixes: (A) a
  unified 3-field `InvHypList::Cons(name, hyp:u64, oblig:RawExp, tail)` +
  new frame builders + touch `loop_maintain_frame`/`loop_use_frame` signatures;
  or (C) keep `inv_hyps: BinderList` (name, hyp) UNCHANGED for the frame and add
  a SEPARATE `inv_obligs: RawExpList` for the deep obligations, reusing the
  already-proven `close_each_e` (from W6d.1b-ii). **Chose Design C** (local model
  concurred, 127.0.0.1:8051, 2026-07-14): it reuses `close_each_e`, leaves the
  delicate leading/non-leading telescope machinery (`loop_maintain_frame`/
  `loop_use_frame`/`binders_to_frame`/`binderprops_to_hyps`/`has_let`) ENTIRELY
  untouched (near-zero proof-breakage), and the "two parallel lists must stay
  index-aligned" cost is a serializer construction-time concern (one pass emits
  both), not a runtime one. Design A's co-location (can't desync) wasn't worth
  the signature churn + ~4 new fns on the proven telescope path.

  **What changed in `tactus-core/lib.rs`** (one datatype-shape churn + fixtures):
  - **`StmData::Loop` gained `inv_obligs: Box<RawExpList>`** (the parallel deep
    invariant obligations, index-aligned with `inv_hyps`); **`decrease_oblig:
    u64 → RawExp`** (deep, like `Assert`).
  - **`wp_stm` Loop arm:** `init` and `maintain_reclose` switched from
    `close_each_binderprop(·, inv_hyps)` → `close_each_e(·, inv_obligs)` (each
    terminal now `LeafE(render_exp(ob))`); `decrease_goal` from `close(endf,
    decrease_oblig)` → `close_e(endf, decrease_oblig)`. The telescope frames
    (`loop_maintain_frame(f, *inv_hyps, …)`) STILL read `inv_hyps` (BinderList)
    for the hypothesis role — unchanged.
  - **`close_each_binderprop` DELETED** (dead — was the only-per-`inv_hyps`-prop
    obligation folder; Loop now uses `close_each_e` like Call/Ret). Confirmed no
    callers in-file or in `source/`.
  - **`frame_after` / `stm_size` Loop arms:** added `inv_obligs` to the match
    patterns; `stm_size` counts it via `raw_exp_list_len` (mirrors the
    serializer's token sum — the cert literal now carries both `inv_hyps` pairs
    AND the `inv_obligs` list, so it's genuinely bigger).
  - **Fixtures:** sum_to monster gained `inv_obligs = [atom_ob(23..26)]`,
    `decrease_oblig: atom_ob(39)`; its 4 init + 4 maintain `Leaf(23..26)` and
    the decrease `Leaf(39)` flipped to `LeafE(Atom …)` (the body-assert and Ret
    leaves were already deep from -i/-ii). nested_loop unit test switched its
    three direct `close(·, 35/43)` → `close_e(·, atom_ob 35/43)` +
    `Leaf → LeafE(Atom)` (the `loop_maintain_frame`/`loop_use_frame` CALLS are
    unchanged — still `BinderList` args, proving the frame path is untouched).
    stm_size test 4 → 5.

  **Verified 52/0** (`--lean-backend --lean-all-proofs`, 46 modules elaborated /
  44 reused, "composition + axiom closures kernel-verified" — no
  `WellFounded.fix`/`Classical`). **NB on the count:** it is **52**, not the
  "53/54" the W6d.1b-ii writeup reported — that writeup's header (54) and body
  (53) disagreed; a spec-fn add/delete doesn't change the verified count (spec
  fns aren't counted), and no proof fn was added/removed across -i/-ii/-iii, so
  52 has been the true baseline since W6d.1b-i. This sub-step is count-neutral.

  **Serializer coupling reconfirmed Lean-text-only (extends -i/-ii); TWO W6d.2
  to-dos surfaced.** No `source/` Rust code constructs `tactus_core::StmData::
  Loop` (only `bootstrap_coverage.rs:27` matches production `vir::sst::StmX::
  Loop`), so the datatype churn does NOT break the Rust build — the **W3 tgt
  gate + e2e suite stay green by construction** (same argument as -i/-ii;
  cert-elaboration-against-new-defs is W6d.2/3, and I did NOT re-run the full
  suite this turn). ⚠ **W6d.2 must fix, or the first Loop cert won't type-check:**
  (1) `sst_serialize.rs:1188` emits `StmData.Loop` as an **11-arg** `format!` —
  now needs **12 args** + a `RawExpList` literal for `inv_obligs` (parallel to
  the `inv_hyps` BinderList emission); (2) `decrease_oblig_leaf`
  (`sst_serialize.rs:459`, returns `Sr<u64>` = a bare Nat leaf) must emit a
  `RawExp` literal instead (like `oblig_leaf`'s Assert path). Plus the standing
  `sst_serialize_tests.rs:35` note from -ii (LeafList → RawExpList for Ret/Call).

  **Next = W6d.2** (serializer text emission, now for ALL deepened slots —
  Assert/Call/Ret/Loop obligations + decrease; `raw_exp` G0 Box/Unbox peel + G7
  VarAt + LitBool/Field/HasType arms; `oblig_leaf` emits the `RawExp` mirror
  wrapped in `Span`; `goal_data` emits `LeafE`). G4 (`Let`-in-leaf) → W6e.

- (2026-07-14, opus-b23) **W6d.2a landed — the serializer emits the deep
  obligation slots (opaque-atom fallback); the emitted cert type-checks against
  the W6d.1b tactus-core defs again and bridges verdict-neutral. Validated
  rebuild-free.** One edit to `sst_serialize.rs` (+ 2 unit-test updates) moved
  ALL FIVE obligation slots off the stage-A `u64`/`LeafList` text:
  - **Two new emit helpers** (free fns by `paren`): `atom_ob_lit(id)` →
    `(lib.RawExp.Var id lib.TypData.TyBool)` (= tactus-core `atom_ob`, renders
    to `Atom id`); `raw_exp_list(terms)` → a `lib.RawExpList` with each element
    a boxed `RawExp` (mirrors `RawExpList::Cons(Box<RawExp>, …)`, unlike
    `leaf_list`'s inline `u64`).
  - **Assert** obligation `oblig` → `atom_ob_lit(oblig)`. **Ret** `es` and
    **Call** `reqs`: `leaf_list` → `raw_exp_list` of `atom_ob_lit` per id.
    **Loop**: added `inv_obligs` = `raw_exp_list` of `atom_ob_lit(oblig)` over
    the SAME `inv_entries` (index-aligned with `inv_hyps` by construction), the
    format went **10-arg → 11-arg** (`inv_obligs` inserted after `inv_hyps`,
    matching the tactus-core field order), and `decrease_oblig` →
    `atom_ob_lit(decrease_oblig)`. **`goal_data`** terminal `GoalData.Leaf id`
    → `GoalData.LeafE (lib.ExprData.Atom id)`.
  - **`stm_size_of`** now counts `RawExpList.Cons` (reqs/es/inv_obligs) as well
    as `LeafList.Cons` — mirrors tactus-core `stm_size = … +
    raw_exp_list_len(…)`. (LeafList.Cons kept counted so the pre-2a golden
    round-trip test still balances; a live stm_term now emits only RawExpList.)
  - `leaf_list` STAYS (it's still `FnCtxData.enss`, an opaque-`u64` hyp list —
    NOT deepened); `oblig_leaf`/`decrease_oblig_leaf` still return `Sr<u64>`
    (the interned id) and are wrapped at the emit site — no signature churn.

  **Why all five move together (not just the user-flagged Loop pair):** the
  bridge is `decide(goals_eq (ref_wp sst) goals)`; refWp's obligation arms ALL
  switched to `close_e`/`close_each_e` in W6d.1b, so refWp now emits `LeafE` for
  EVERY obligation and `close` (the `Leaf u64` folder) is dead. A cert that
  still emitted `Assert <nat> <nat>` (or `GoalData.Leaf`) would fail Lean
  type-check / mismatch the `LeafE` reference. So type-correctness forces the
  symmetric flip across Assert/Ret/Call/Loop + goal_data at once — 2a is the
  smallest INDEPENDENTLY CHECKABLE unit.

  **Verified — Rust `cargo test -p lean_verify --lib` = 327 passed / 0
  failed** (incl. `stm_size_matches_core` on the new RawExp/RawExpList shapes,
  `goal_data_spine_shape` on `LeafE`, and the `golden_add_capped_cert`
  round-trip — still green because it recovers-and-re-renders its own file).

  **Verified — end-to-end bridge, NO binary rebuild.** Transformed two on-disk
  fixture certs by hand EXACTLY as the new serializer does (a small
  balanced-paren Python transcription of the actual edits) and elaborated them
  against the live `tactus-core/out/lib` oleans (the W6d.1b 03:26 build):
  - `scope_shape` (Assert + Ret + 2 goals): `stm_size … = 8` ✓, `goal_count …
    = 2` ✓, **`goals_eq (ref_wp ctx sst) goals = 1 := by decide` ✓ (and `by
    rfl` ✓)** — rc=0, 1.3s. The deep-leaf mechanism closes.
  - `sum_to` (the Loop + cast-class monster): the 10-arg→11-arg Loop with
    `inv_obligs` = `[atom_ob 17,19,21,23]` inserted + `decrease` wrapped
    type-checks; `stm_size` recomputed **25 → 29** (the 4 `inv_obligs` Cons —
    my `stm_size_of` produces the matching 29, decide ✓); **`goals_eq (ref_wp
    ctx sst) goals = 1 := by decide` ✓** — rc=0, 1.7s. The Loop plumbing +
    field order are correct against tactus-core. (The initial `stm_size = 25`
    error was the STALE probe from the old cert — a positive signal that
    `inv_obligs` is genuinely-new counted content, not a bug.)

  These are opaque-atom bridges (verdict-neutral): both sides collapse each
  obligation to `Atom(interned-id)`, so they close by the same id-matching as
  stage-A. The DEEP structure (which actually catches Friction-2) arrives in
  W6d.2b when `raw_exp`/`lexpr_to_exprdata` are wired in.

  **Not done / assumptions.** (1) The golden `testdata/add_capped.cert.lean`
  now reflects the OLD emission (its round-trip test still passes — it's a
  render_cert format pin, not a serializer-output pin) — regenerate it in
  W6d.3's re-emit. (2) The full probe9 over ALL 13 re-emitted fixtures still
  needs the release-binary rebuild (the two hand-transforms cover the two
  representative shapes; a rebuild+re-emit is the exhaustive W6d.3 check).
  (3) No production code path other than the serializer changed; the W3 tgt
  gate + e2e suite stay green by construction (Lean-text-only coupling, same
  argument as every W6d.1b sub-step).

  **Next = W6d.2b** (deep transcription, the Friction-2 catcher — see the split
  plan bullet above) then **W6d.3** (rebuild + re-emit all fixtures + probe9 +
  regenerate the golden). G4 (`Let`-in-leaf) → W6e.

- (2026-07-14, opus-b24) **W6d.2b-1 landed — the reference-side `raw_exp`
  gained its three dominant-blocker peel/alias arms (G0 Box/Unbox, G7 VarAt, G1
  bool literal); 4 new unit tests, `lean_verify` lib 331/0.** First sub-step of
  W6d.2b, same "land the transcription dead, wire later" discipline as W6c (the
  fn is still `#[allow(dead_code)]` — the emit-path gate is 2b-2). What changed
  in `sst_serialize.rs` (added `UnaryOpr` to the `vir::ast` import + 3 arms in
  `raw_exp`):
  - **G0 — `ExpX::UnaryOpr(Box(_) | Unbox(_), inner) => self.raw_exp(inner)`.**
    Peels the SMT coercion wrappers transparently (recurse into inner, drop the
    wrapper), exactly as `typ_data` already peels `Boxed`/`Decorate` at the type
    level. The inner node's own `typ` drives its tag. This is the #1 unlock the
    W6d.0 dump identified — every boxed value (spec-fn args, datatype args, field
    results, tuple elements) is Box-wrapped, so without G0 even `tri (1)` (a
    `Box[Nat] 1` arg) is unreachable. Placed FIRST in the match to document its
    peel-first role.
  - **G7 — `ExpX::Var(vid) | ExpX::VarAt(vid, _) => …`** (merged into the
    existing `Var` arm via or-pattern). A pre-state param read `VarAt(vid, Pre)`
    (ensures/decrease leaves) mirrors identically to a plain `Var`: same
    `binder_id`, read `e.typ`. Production's `vir_expr_to_ast` collapses `VarAt`
    to a bare `Var`, so the mirrors agree by construction for non-mut params
    (the fixture's coverable fns). The `&mut`-ensures `x_at_pre_tactus` case
    diverges — the 2b-2 emit-gate catches it by falling both sides to atom.
  - **G1 — `ExpX::Const(Constant::Bool(b)) => RawExp.LitBool (0/1)`.** The nat
    encoding, NOT a `bool` (a spec `bool` renders as `Prop` and sticks `decide`
    — W6d.1a design deviation 1). `render_exp` passes it straight through to
    `ExprData::LitBool`.
  - **4 unit tests** (`sst_serialize_tests.rs`, new `mk_exp`/`tvar`/`tint`
    helpers): `raw_exp_peels_box_unbox` (Box(Unbox(Var x)) == bare Var x),
    `raw_exp_peels_box_inside_binop` (peel recurses under a `+`, both operands
    bare), `raw_exp_varat_reads_like_var` (VarAt(n,Pre) == Var n, same interned
    id 0), `raw_exp_bool_literal` (true→1, false→0).

  **Verified** — `cargo test -p lean_verify --lib` = **331 passed / 0 failed**
  (327 baseline + 4). Non-test `cargo build -p lean_verify` clean (only
  pre-existing warnings). Verdict-neutral by construction: `raw_exp` is still
  dead (nothing in the emit path calls it), so no cert emission changed; the W3
  tgt gate + e2e suite are unaffected. This turn touched ONLY the reference-side
  transcription — no tactus-core churn, no goal-side change, no emit wiring.

  **Precise state for the next instance (what 2b-2 must add):**
  - **Reference `raw_exp` still fails-loud on G3/G6** — `ExpX::UnaryOpr(Field |
    HasType, _)` hits the `_ => Err("raw-unaryopr")` arm (the census tag is now
    slightly coarse: post-G0 the remaining unaryopr fails are exactly Field /
    HasType / IsVariant / IntegerTypeBound / etc. — worth sharpening
    `exp_construct_tag` when G3/G6 land). G3 (`RawExp::Field`) + G6
    (`RawExp::HasType`) reference arms are the remaining coverable shapes; G2
    (TyRef→deref) is handled by `render_exp`, so `raw_exp` needs no G2 arm (the
    `&T`-arg tag flows through `typ_data`'s `TyRef`). Priority: G6 (unlocks the
    arith fns) then G3 (datatype/struct/tuple fns).
  - **Goal-side `lexpr_to_exprdata` still rejects G1** — it fails
    `LExpr::lit_bool` with `ed-litbool` (pinned by `lexpr_to_exprdata_census_
    rejects`). So G1 is HALF-landed: the reference arm exists but a
    `find_square`-style `ensures true` won't BRIDGE until the goal side gains a
    matching `ExprNode::LitBool → ExprData.LitBool` arm (and that census-reject
    test is updated). G0/G7 need NO goal-side change (Box/Unbox are SST-only,
    absent from production LExpr; VarAt collapses to a bare `Var` the goal side
    already maps to `ExprData::Atom`).
  - **2b-2 = the emit-path gate.** Wire `raw_exp` into `oblig_leaf` +
    `lexpr_to_exprdata` into `goal_data`, with the rule "go deep ONLY when BOTH
    transcriptions succeed; else BOTH fall back to `atom_ob`/`Atom`" so a
    ref-deep/goal-atom mismatch never silent-passes. Wrap the obligation
    `RawExp` in `RawExp::Span` at the `oblig_leaf` level (raw SST has no
    SpanMark node). This is where the deep bridge first catches Friction-2.

  **Next = W6d.2b-2** (G6 + G3 reference arms + goal-side G1 arm, then the emit
  gate) → **W6d.3** (rebuild + re-emit + probe9 + regenerate the golden). G4
  (`Let`-in-leaf) → W6e.

- (2026-07-14, opus-b25) **W6d.2b-2 arms landed — the LAST two reference arms
  (G6 HasType, G3 Field) + the goal-side G1 (LitBool) arm; `lean_verify` lib
  335/0. The transcriptions are now COMPLETE for the coverable fixture set; only
  the emit-path gate remains in 2b-2.** Same "land the transcription dead, wire
  later" discipline as 2b-1 — `raw_exp`/`lexpr_to_exprdata` stay
  `#[allow(dead_code)]`, so nothing in the emit path calls them and the change
  is verdict-neutral by construction (no cert emission changed; W3 tgt gate +
  e2e suite unaffected). What changed in `sst_serialize.rs` (+ tests):
  - **G6 — `ExpX::UnaryOpr(HasType(t), inner) => RawExp.HasType <width> <box
    inner>`.** New free helper `uint_bound_width(t)` peels `Boxed`/`Decorate`
    (like `typ_data`) and returns `n` for `Int(U(n))`; every other range fails
    loud `hastype-range` (signed/usize/char/int/nat not carried — the
    `RawExp::HasType` contract). `render_exp` re-expands the carried width to
    `0 ≤ e ∧ e < 2^n` INDEPENDENTLY (its own `pow2`), so a production/reference
    bound divergence surfaces as a bridge mismatch, never a silent pass. Unlocks
    the arithmetic-overflow fns (add_capped/double_exec/quad_exec/count_down-
    body/find_square/sum_to-body — the 10 HasType leaves the W6d.0 dump found).
  - **G3 — `ExpX::UnaryOpr(Field(fop), inner) => RawExp.Field <fid> <fty> <box
    base>`.** **The key transparency win (Danielle's steer): reuse production's
    own `expr_shared::field_access_name(fop)` for the accessor string** rather
    than re-deriving the tuple 1-indexed shift in the serializer. The goal-side
    `FieldProj.field` production emits is ALSO `field_access_name(fop)`, so both
    sides intern the IDENTICAL string → the atom-id consistency invariant holds
    by construction, not by a parallel re-derivation that could drift. A 1-tuple
    field-0 access (`field_access_name` returns `None`) is the identity —
    production emits no projection, so the arm mirrors the bare base. `fty` =
    the field node's own `typ` via `typ_data`. NB: a `&`-decorated base needs
    the `.deref` chain production inserts (`apply_deref_chain`), which this arm
    does NOT reproduce — such a base DIVERGES (ref `p.x` vs goal `p.deref.x`) and
    the 2b-2 emit-gate keeps it fail-loud (the fixture's mk_point/swap_pair use
    plain bases, so it doesn't bite them). Unlocks the struct/tuple fns.
  - **G1 goal side — `ExprNode::LitBool(b) => ExprData.LitBool (0/1)`** in
    `lexpr_to_exprdata`. Closes the half-landed G1 (2b-1 added only the
    reference `RawExp::LitBool` arm). Nat encoding, not `bool` (a spec `bool`
    renders Prop → sticks `decide`; W6d.1a deviation 1). Now `ensures true`
    (find_square) bridges — both sides `LitBool 1`.
  - **Tests (335/0, +4 net):** `lexpr_to_exprdata_bool_literal` (G1 goal
    true→1/false→0), `raw_exp_hastype_carries_width` (`HasType(U64)(Var s)` →
    `HasType 64 (box Var 0 TyInt)`), `raw_exp_hastype_rejects_signed`
    (`I(64)` → `hastype-range` fail-loud), `raw_exp_field_tuple`
    (`Dt::Tuple(2)` field "1" → accessor "2" via `field_access_name`, interned
    id 1, base var id 0). The `lexpr_to_exprdata_census_rejects` test's
    now-invalid `lit_bool → ed-litbool` assertion was replaced with a
    still-out-of-class `¬p → ed-unop` (bool literals are in-class now). Non-test
    `cargo build -p lean_verify` clean (exit 0; the 8 warnings are all
    pre-existing — none reference the new code).
  - **Census sharpening deferred (minor):** the board's 2b-1 note suggested
    sharpening `exp_construct_tag`'s coarse `unaryopr` tag once Field/HasType
    land. With G3/G6 explicit, the remaining `raw-unaryopr` fails are now only
    IsVariant/IntegerTypeBound/HasResolved/ProofNote/CustomErr/ToDyn — none in
    the coverable set; left as-is (a `unaryopr_tag` sub-classifier is a
    nice-to-have, not blocking the emit gate). G6's own `hastype-range` and
    G3's inherited `typ-*`/`raw-*` sub-fails already distinguish the new arms.

  **Precise state for the next instance — 2b-2's remaining half is the EMIT
  GATE (the Friction-2 catcher):** wire `raw_exp` into `oblig_leaf` and
  `lexpr_to_exprdata` into `goal_data(shape.leaf)`, with the rule **"go deep
  ONLY when BOTH transcriptions succeed AND the leaf is coverable; else BOTH
  fall back to `atom_ob`/`Atom` by the same interned id"** — a ref-deep/goal-atom
  (or deep-but-unequal) mismatch must fail that fn's bridge (→ census-tracked,
  non-bridging), never silent-pass. Wrap the obligation `RawExp` in
  `RawExp::Span` at the `oblig_leaf` level (raw SST has no SpanMark node —
  bootstrap-22). The five obligation slots currently emit `atom_ob_lit(id)` /
  `GoalData.LeafE(ExprData.Atom id)` (W6d.2a opaque fallback); the gate swaps
  those for the deep `raw_exp`/`lexpr_to_exprdata` output on coverable leaves.
  All the transcription vocabulary it needs now exists and is unit-pinned. Then
  **W6d.3** (rebuild release binary + re-emit all fixtures + probe9 the coverable
  subset + regenerate the golden `add_capped.cert.lean`). G4 (`Let`-in-leaf) →
  W6e.

- (2026-07-14, opus-b26) **W6d.2b-2 emit gate LANDED — `raw_exp` +
  `lexpr_to_exprdata` are wired into the emit path; the deep bridge now fires
  on coverable obligations. `lean_verify` lib 338/0.** This closes W6d.2b's
  remaining half (the transcription vocabulary was complete + unit-pinned but
  `#[allow(dead_code)]`; nothing fed it into `oblig_leaf`/`goal_data`). What
  changed, all in `sst_serialize.rs` (+3 tests):

  - **New `oblig_slot(&mut self, e) -> Sr<(u64, String)>`** — the deep-or-atom
    obligation SLOT for one raw SST obligation. Interns the span_mark'd leaf id
    (== goal-side leaf id, the atom-match key), then attempts `raw_exp(e)`. On
    success (coverable) it emits the DEEP `RawExp.Span(loc, box raw)` and records
    the id in a new `deep_ids: HashSet<u64>`; on failure it falls back to
    `atom_ob(id)` (the W6d.2a opaque behavior). **The `Span` wrapper is added
    HERE** — the raw SST has no SpanMark node (bootstrap-22), so `oblig_slot`
    wraps the bare `raw_exp` in `RawExp.Span` with `loc =
    text_leaf(format_rust_loc(&e.span))` — the SAME loc string `oblig_leaf`'s
    span_mark carries, so the ref `RawExp.Span(loc,·)` → `render_exp` →
    `ExprData.SpanMark(loc,·)` shares its loc id with the goal side's
    `ExprData.SpanMark(loc, lexpr(inner))`. Wired at the THREE deepenable sites:
    Assert arm, ensures setup (`pending_ens_oblig: Vec<u64> → Vec<String>` of
    pre-built slots), and Loop-inv (`inv_slots` parallel to `inv_entries`).
  - **`goal_data` gate** — deepens the core leaf into `LeafE(ExprData…)` via
    `lexpr_to_exprdata(shape.leaf)` ONLY when `deep_ids.contains(leaf_id)` AND
    the transcription succeeds; else the opaque `Atom(id)` fallback.

  **The coordination is the "ob-drives" asymmetric gate (single-pass, sound).**
  The stm (obligation) walk runs BEFORE the goal walk (`serialize`: `stm` then
  `goal_list`), so a truly-symmetric "go deep iff BOTH sides succeed, else BOTH
  atom" gate would need a goal pre-pass (circular: the ob side would need
  goal-side success info it can't have yet). Instead: the ob side drives
  (deep iff `raw_exp` ok, recorded in `deep_ids`); the goal side follows
  (deep iff `deep_ids` has the id AND `lexpr` ok). Case analysis by
  (ref_ok, goal_ok):
  - **(ok, ok)** → both deep → bridge `decide`s `expr_eq(render_exp(raw),
    lexpr(leaf))` (the Friction-2 catcher). ✓
  - **(¬ok, ok)** → ob atom (not in `deep_ids`) → goal atom → **both atom,
    verdict-neutral.** This is the `id_generic` case (`r==t` generic: `raw_exp`
    fails `typ-typparam` on the operand type; `lexpr` succeeds on `Atom r =
    Atom t`) — ob-drives keeps it atom, so **no regression** from W6d.2a's
    all-atom bridging. ✓
  - **(¬ok, ¬ok)** → both atom. ✓
  - **(ok, ¬ok)** → ob deep, goal atom → **mismatch → that fn's bridge fails
    (non-bridging, census-tracked)** — SOUND (a deep-structure vs `Atom` never
    `expr_eq`-matches, so never a silent pass), only a coverage loss. Not
    constructable in the fixture (the transcribers are duals over the coverable
    set). If W6d.3 surfaces one, upgrade to the symmetric pre-pass (documented).

  **Forced-atom sites are handled FOR FREE by ob-drives.** Call reqs (a
  production LExpr, no raw SST → no `raw_exp`), Loop `decrease_oblig` (a
  synthesized `0≤D ∧ D<d_old`), and the if-cond / loop-cond HYPOTHESIS slots
  (`c`/`nc`/`cond_ann`, which are `Imp` hyps, not obligations→goals) never call
  `oblig_slot`, so their ids never enter `deep_ids` and their goals auto-stay
  atom on both sides — no special-casing needed.

  **Size-invariance confirmed (critical — else the emitted `stm_size := by
  decide` probe would break).** tactus-core `stm_size` counts stmt heads +
  `raw_exp_list_len` (list LENGTH) + `binder_len` + `frame_len` — it NEVER
  recurses into RawExp depth (`Assert(_o,_h)=>1`; `Ret(es,_)=>1+raw_exp_list_len
  es`; Loop likewise). So deep-vs-atom is `stm_size`- AND `goal_count`-invariant
  (one `RawExpList.Cons` / one goal per obligation either way); the serializer's
  `stm_size_of` matches (counts the same tokens). The ONLY behavioral change is
  `goals_eq` now comparing deep structure on coverable obligations — exactly the
  intended Friction-2 comparison point.

  **Verified — `cargo test -p lean_verify --lib` = 338 passed / 0 failed** (335
  baseline + 3: `oblig_slot_deep_wraps_span_and_records`,
  `oblig_slot_atom_fallback_when_not_coverable`,
  `goal_data_gate_deep_only_when_in_deep_ids`). Removed the now-superfluous
  `#[allow(dead_code)]` from every now-live transcription fn (`raw_exp`,
  `lexpr_to_exprdata`, `typ_data`, `call_fun_id` + the free helpers) — a
  clean rebuild shows NO `sst_serialize.rs` dead-code warning, confirming they
  are all genuinely reached from the emit path. Baseline 8 warnings (all
  pre-existing, in other files).

  **Verdict-neutral by construction / not yet re-emitted.** The serializer
  changes only cert TEXT when `--tactus-emit-cert` is on (Lean-text-only
  coupling — same argument as every W6d.1b/2a sub-step); the Rust build +
  default e2e suite + W3 tgt gate stay green. No cert was re-emitted this turn
  (needs the release-binary rebuild = W6d.3). The deep-render MECHANISM itself
  is already Lean-verified (W6d.1a `expr_mirror_kernel_computes` +
  `leafe_goal_bridge_kernel_computes`, both `.verified`), so W6d.3 validates the
  end-to-end wiring (real serializer output → cert → bridge `decide`), not the
  math.

  **Next = W6d.3** (rebuild release binary + re-emit all 13 fixtures + probe9
  the coverable subset [add_capped, double_exec, quad_exec, sum_to, scope_shape,
  tri_one, head_exec, mk_point, swap_pair] + regenerate the golden
  `add_capped.cert.lean`; confirm flag-on == flag-off verdict, census the
  fail-loud remainder). If any coverable fn goes non-bridging, check for a
  (ref_ok && !goal_ok) mismatch [→ symmetric-gate upgrade] or a genuine deep
  disagreement [→ a transcription bug, or the real Friction-2]. G4 (`Let`-in-leaf)
  → W6e.

- (2026-07-14, opus-b27) **W6d.3 DONE — the deep bridge is LIVE end-to-end.
  Rebuilt binary + re-emitted all fixtures + probe9 green + golden regenerated +
  verdict-neutral + deep-mutation non-vacuity confirmed. W6d COMPLETE.** This is
  the end-to-end validation the emit gate (2b-2) was Lean-verified for in the
  abstract; W6d.3 runs the real serializer output through the bridge.

  **1. Release binary rebuilt.** FORK vargo (`tactus-bootstrap/tools/vargo`) on
  PATH (bare `vargo` = the upstream `verus/` submodule → "sources changed"
  bail). `vargo build --release` from `source/`: `lean_verify` + `rust_verify`
  recompiled (20.3s), verus binary refreshed (was stale at 01:50, predating the
  2b-1/2b-2 arms + the emit gate; now 04:49), vstd re-verified **1530/0**.

  **2. Fixtures re-emitted** (`--crate-type=lib --lean-backend --lean-all-proofs
  --tactus-emit-cert bootstrap-fixture/lib.rs`, `TACTUS_LEAN_OUT=…/bootstrap-
  fixture/out`, run from the tactus-bootstrap dir so `@rust:` locs read
  `bootstrap-fixture/lib.rs`). **certified 13/16** (up from 11/16 — the deep
  arms enabled 2 more); the 3 rejections are `vec_read`/`vec_push7`/`fill_zeros`,
  all **`call-generic`** (exec-Vec calls / quantifier bind — the documented
  non-cast-class census remainder, NOT bridge failures). All 13 certs rewrote to
  the DEEP shape: e.g. `Assert 5 4` → `Assert (RawExp.Span 8 (RawExp.Var 6
  TyBool)) 6`; the scope_shape/tri_one Ret obligation now carries a full
  `RawExp.BinOp(Call(tri, arg), Lit)` tree and the goal a matching
  `ExprData.SpanMark(BinOp(App(tri,·), Lit))` — genuinely deep, not opaque atom.
  add_capped's overflow leaf `0≤x+y ∧ x+y<2^64` (G6 HasType) expands to 12
  `ExprData.BinOp` + 6 `Lit` nodes on the goal side.

  **3. probe9 — ALL BRIDGES BEHAVE AS CLASSIFIED ✓.** Every coverable fn closes
  by BOTH `decide` and `rfl`; the one honest-fail behaves:
  ```
  add_capped  close-ok   double_exec close-ok   quad_exec   close-ok
  count_down  close-ok   find_square close-ok   head_exec   close-ok   (G2 deref)
  id_generic  close-ok   mk_point    close-ok   swap_pair   close-ok   (G3 field)
  scope_shape close-ok   sum_to      close-ok   tri_one     close-ok
  max_u64     hfail-ok   (G4 If-fold in leaf — DEFERRED to W6e, as classified)
  ```
  12/13 close-ok, 1/13 hfail-ok. **No `(ref_ok && !goal_ok)` mismatch surfaced**
  on any coverable fn — the ob-drives asymmetric gate held; the transcribers are
  duals over the coverable set exactly as 2b-2 predicted, so **no symmetric-gate
  upgrade is needed** (the fork Danielle flagged did not materialize).

  **4. Verdict-neutral confirmed.** Fixture flag-OFF (no `--tactus-emit-cert`) ==
  flag-ON: both **`13 verified, 11 errors`**. The 11 errors are the pre-existing
  `tactus_auto`/Lean proof-SEARCH failures on the hard fixture fns (orthogonal to
  cert emission, which runs emission-only at the SST snapshot and adds no
  obligations — documented since bootstrap-15). Emitting the deep cert does not
  perturb the verifier verdict.

  **5. Golden regenerated.** `source/lean_verify/src/testdata/add_capped.cert.lean`
  replaced with the fresh deep emission (24→28 leaves — the deep structure interns
  the `lib.tri`-style call accessors + the `@rust:` loc strings for each `Span`;
  still 4 goals). Updated the drift assertion `leaf_texts.len()` 24→28 in
  `sst_serialize_tests.rs`. The golden test re-renders the recovered `CertBody`
  and asserts byte-equality → still green (a format pin, now pinning the deep
  format). Full `cargo test -p lean_verify --lib` = **338 passed / 0 failed**
  (incl. `golden_add_capped_cert`, `stm_size_matches_core`, the goal-spine +
  emit-gate tests).

  **6. Deep-mutation non-vacuity (bonus — proves the deep compare is
  load-bearing, not vacuous atom-collapse).** On tri_one: baseline deep bridge
  closes (`decide` rc=0); mutating ONE deep SST node — the `tri(1)` call arg
  `RawExp.Lit 1` → `RawExp.Lit 9` — makes `decide` prove the bridge proposition
  **FALSE** (rc=1). So `ref_wp` genuinely renders the deep `RawExp` (`tri 9 = 1`)
  and `goals_eq` genuinely `decide`s `expr_eq` against the goal side's `tri 1 =
  1` — a structurally-wrong deep expression FAILS the bridge, never silent-passes.
  (This is a spot-check, not the systematic W6e kill — that drops `Int.toNat` on
  the prod side across the cast class.)

  **Net:** the R2-bridge deep obligation path — `GoalData::LeafE(ExprData)` on
  both sides, `refWp` closing via `render_exp(RawExp)`, the bridge `decide`ing
  `expr_eq` — is now LIVE for the entire coverable fixture corpus. The Friction-2
  inconsistent-coercion class is caught at expression granularity. **G4
  (`If`-fold `Let`/`Not` in one leaf, max_u64) is the sole deferred gap → W6e.**

  **Committed:** the 2 source-test changes + the fresh `tactus-core/out/lib`
  oleans (the W6d.1b build artifacts had been left uncommitted since the last
  olean commit at W6d.1a `b99f6cc`; committing them makes this bridge result
  reproducible from a clean checkout, per the `7fda99b` stage-B-artifact
  pattern). `bootstrap-fixture/out` stays gitignored/regenerable.

## Writeup

**W6d — bridge deepened — COMPLETE (2026-07-14).** Parent design:
`DESIGN-W6-stageB.md`; ladder rung 4 (`VERIFICATION-PATH.md`).

**What W6d achieved.** The R2 bridge's obligation leaves are now *structurally
certified* end-to-end: for the bridgeable fixture corpus, both the production
emitter and the reference WP produce `GoalData::LeafE(ExprData)` (deep
expression trees, not opaque `Leaf(u64)` ids), `refWp` closes each obligation
via `render_exp(rawExp)`, and the kernel `decide`s `goals_eq` = constructor-for-
constructor `expr_eq`. A serializer that produced a structurally-wrong deep
expression now FAILS the bridge instead of silent-passing — the Friction-2
inconsistent-coercion blind spot W6 exists to close.

**How the code works (the deep path, in emission order).**
1. **Mirror vocabulary** (`tactus-core/lib.rs`, W6d.1a): `ExprData`/`RawExp`
   gained `LitBool` (G1), `Field`→`FieldProj` (G3), `HasType` (G6, re-expands
   `0≤e ∧ e<2^width` independently), plus the `needs_ref_deref` TyRef rule (G2).
   All payloads are `nat` (a spec `bool` renders Prop → freezes `decide`); any
   computed constant (`pow2`) is a non-recursive width→bound table (a
   `decreases`-on-arithmetic def lowers to `WellFounded.fix`, which the kernel
   won't unfold under `decide`).
2. **Reference fold** (`tactus-core/lib.rs`, W6d.1b): `close_e`/`close_each_e`
   fold the frame telescope around `LeafE(render_exp(ob))`; the five obligation
   slots on `StmData` (Assert / Ret.es / Call.reqs / Loop.inv_obligs /
   decrease_oblig) carry `RawExp`/`RawExpList` (a dedicated deep list, kept
   distinct from the opaque-`u64` `LeafList` so a `LeafE` can never silently
   match a stage-A `Leaf`). Loop used Design C (parallel `inv_obligs: RawExpList`
   beside the untouched `inv_hyps: BinderList`), leaving the delicate frame
   telescope machinery unchanged.
3. **Serializer transcription** (`source/lean_verify/src/sst_serialize.rs`,
   W6d.2): `raw_exp` peels Box/Unbox SMT wrappers (G0 — the dominant unlock),
   aliases `VarAt(_,Pre)`→`Var` (G7), and emits the G1/G3/G6 shapes;
   `lexpr_to_exprdata` mirrors on the goal side; `typ_data` peels
   Boxed/Decorate. The G3 accessor reuses production's own
   `field_access_name(fop)` so both sides intern the identical string (no
   parallel re-derivation to drift).
4. **The emit gate** (W6d.2b-2): `oblig_slot` interns the span-marked leaf id,
   attempts `raw_exp(e)`, and on success emits `RawExp.Span(loc, ·)` + records
   the id in `deep_ids`; `goal_data` deepens the matching leaf iff
   `deep_ids.contains(id)` AND `lexpr_to_exprdata` succeeds. This is the
   **ob-drives asymmetric gate** (single-pass; the stm walk precedes the goal
   walk, so a symmetric "both-or-neither" would need a circular goal pre-pass).
   Forced-atom sites (Call reqs = a production LExpr with no raw SST; the
   synthesized decrease disjunct; if/loop-cond hypotheses) never enter
   `deep_ids`, so they stay atom on both sides for free — verdict-neutral.
   Size-invariance: `stm_size`/`goal_count` count list length / node heads, never
   RawExp depth, so deep-vs-atom is size-neutral — only `goals_eq`'s structural
   compare changes.

**Validation (W6d.3).** Rebuild → re-emit (13/16 certified) → probe9 (12/13
close-ok deep, max_u64 hfail-ok) → verdict-neutral (flag-off == flag-on, 13v/11e)
→ golden regenerated (28 leaves, 338 tests green) → deep-mutation non-vacuity
(a deep-node flip fails the bridge). All bridges behave as classified.

**Assumptions / what's partial.**
- **max_u64 stays honest-fail** (G4): its two ensures leaves are the whole
  `x<y → (let r := …; r≥x ∧ r≥y)` If-fold living on the goal path — needs
  `ExprData::Let` + `Not` fold-in. Deferred to W6e. Sound (fail-loud, never
  silent-pass).
- **3 census rejections** (`vec_read`/`vec_push7`/`fill_zeros`, `call-generic`):
  exec-Vec calls and a quantifier bind — outside the cast class, correctly not
  serialized. Not bridge failures.
- **11 fixture proof-search errors** are the Lean backend failing to PROVE hard
  obligations, orthogonal to cert emission (emission-only at the SST snapshot).
  Same 11 with the flag off. Not caused by, and cannot be caused by, this change.
- **The deep-mutation is a spot-check**, not the systematic expression-level
  mutation-kill (drop `Int.toNat` on the prod side across the cast class) — that
  is **W6e**, together with G4 fold-in.

**Lasting artifact:** the corpus coverage map + gap taxonomy (G0–G7) above — the
expression-level roadmap the rest of W6 executes against — plus this: the deep
R2 bridge closing over the whole coverable corpus, with the mechanism both
Lean-verified (`expr_mirror_kernel_computes`) and now demonstrated on real
serializer output.
