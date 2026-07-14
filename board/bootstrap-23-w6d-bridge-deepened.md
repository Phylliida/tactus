---
title: "W6d — bridge deepened: obligation leaves emit LeafE + refWp closes over ExprData (corpus coverage map)"
status: in_progress
claimed_by: opus-b23
created: 2026-07-14T09:30:00Z
updated: 2026-07-14T09:30:00Z
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

## Phased plan (probe-first, each independently checkable)

- **W6d.0 — confirm the SST shapes (NO code).** Dump the raw SST for `head_exec`
  (G2), `mk_point`/`swap_pair` (G3), `count_down`/`find_square` (G1). Confirm:
  (a) head_exec's call arg is `Var(t):&Tree` with no explicit deref + what
  `arg.typ` actually is; (b) the VIR variant for field access; (c) how `True`/
  `False` appear (`ExpX::Const(Constant::Bool)`?). This resolves the G2/G3
  "confirm in W6d.0" flags before any shared-crate edit. Recommend a tiny
  gated `eprintln` of `debug_format` on the obligation `Exp` in `oblig_leaf`,
  run over the fixture cold-emit, then revert.
- **W6d.1 — the shared-crate batch (one clean churn).** In `tactus-core/lib.rs`:
  add `ExprData::LitBool`/`RawExp::LitBool` (G1); `RawExp::Field` +
  `render_exp` arm (G3); the `needs_ref_deref` coercion in `render_exp`'s Call
  arm + `expr_eq`/`type_of` deref support (G2); a `close_e(frame, rawExp)` that
  folds a frame around `LeafE(render_exp(rawExp))` (mirrors `close`); switch the
  obligation-emitting `refWp` arms to `close_e` and change `StmData`'s
  obligation slot(s) `u64 → RawExp`. Extend `expr_mirror_kernel_computes` with
  the new corpus cases (LitBool, field, derived-deref) as in-crate `decide`
  guards. Defer G4 (`Let`-in-leaf).
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

## Writeup

_when done: findings, how the code works, assumptions made. Parent design:
`DESIGN-W6-stageB.md`; ladder rung 4 (`VERIFICATION-PATH.md`). This task's
lasting artifact is the corpus coverage map + gap taxonomy above — the
expression-level roadmap the rest of W6 executes against._
