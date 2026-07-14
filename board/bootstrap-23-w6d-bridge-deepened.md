---
title: "W6d — bridge deepened: obligation leaves emit LeafE + refWp closes over ExprData (corpus coverage map)"
status: in_progress
claimed_by: opus-b23
created: 2026-07-14T09:30:00Z
updated: 2026-07-14T15:30:00Z
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
  - **W6d.1b-iii — the Loop obligation slots (`inv_hyps` props, `decrease_oblig`).**
    `decrease_oblig` is bare `u64 → RawExp` (easy, like Assert). `inv_hyps` is a
    `BinderList` whose PROP (2nd) slot is the obligation → needs a `(u64 name,
    RawExp prop)` container + `close_each_binderprop_e`. Wire the Loop maintain/
    init/decrease arms. Fixtures: sum_to monster (Leaf 23/24/25/26 init+maintain,
    Leaf 39 decrease), nested_loop (Leaf 35, via direct `close` — switch to
    `close_e`).
- **W6d.2 — serializer wiring.** In `sst_serialize.rs`: `oblig_leaf` (and the
  Ret/Loop obligation paths) emit the `RawExp` mirror into `StmData` (drop
  `#[allow(dead_code)]` on `raw_exp`/`typ_data`); `goal_data` emits
  `GoalData::LeafE(lexpr_to_exprdata(shape.leaf))` (drop `#[allow(dead_code)]`
  on `lexpr_to_exprdata`). Wrap the obligation `RawExp` in `RawExp::Span` at the
  `oblig_leaf` level (the raw SST has no SpanMark node — see `bootstrap-22`
  writeup). Keep every non-cast-class shape fail-loud + census-tracked.
- **W6d.3 — bridge over the bridgeable subset, verdict-neutral.** Re-emit the
  fixture; bridge (probe9-style) the fns whose leaves are all coverable
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
  - **`close_each` (the LeafList version) is now DEAD** — no callers (Loop uses
    `close_each_binderprop`; Call/Ret use `close_each_e`). Kept + comment-marked
    SUPERSEDED (pure spec fn, harmless; safe to delete once no stage-A obligation
    container remains — confirmed no external refs via grep).

  **Verified 54/0** (`--lean-backend --lean-all-proofs`, 46 modules elaborated,
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

## Writeup

_when done: findings, how the code works, assumptions made. Parent design:
`DESIGN-W6-stageB.md`; ladder rung 4 (`VERIFICATION-PATH.md`). This task's
lasting artifact is the corpus coverage map + gap taxonomy above — the
expression-level roadmap the rest of W6 executes against._
