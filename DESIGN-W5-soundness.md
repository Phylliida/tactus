# DESIGN — W5, soundness of the reference WP (the bootstrap loop closes)

Master plan: `DESIGN-bootstrap.md` §5 (W5 row) + §6 (loop diagram). Open
question: `DESIGN-W2-refwp.md` §4 (W5 pointer) + §5.5 (leaf semantics). This
doc owns the W5 ladder in detail and records the decisions taken at W5a kickoff.

Board: `bootstrap-10` (umbrella) + `bootstrap-49..53` (W5a–e, split here).

---

## 0. What W5 proves, in one breath

The reference WP `ref_wp : FnCtxData → StmData → GoalList` (tactus-core
`lib.rs`, emitted as `lib.ref_wp`) walks the mirror SST `s` under a telescope
frame `f` and emits a list of obligation goals. W5 writes down an **operational
semantics** of the SST — what it *means* for `s` to be safe (no failing
assert / overflow / bounds) — and proves

> **`ref_wp_sound`**: if every goal in `ref_wp c s` holds, then `s` is safe.

authored as tactus proof fns, verified by the tactus binary (routed to Lean),
emitted as one more kernel-checked package. The loop closes non-circularly: the
tactus binary is only an *author*; a bad proof fails Lean elaboration, a bad
bridge fails `decide`, a smuggled axiom fails the closure check (§6 of the
master plan). The fixed point is anchored in the Lean kernel, outside the
system being bootstrapped.

---

## 1. Decision taken at W5a kickoff (open question §5.5) — VALUATION-PARAMETRIC (option b)

`DESIGN-W2-refwp.md` §5.5 posed: a fuel evaluator **cannot evaluate opaque
leaves** (stage-A obligation/hyp leaves are interned `u64`s / `Int`s, not
expression trees). Two ways out:

- **(a) land stage B (W6, deep expressions) first** — serializes W5 behind W6,
  loses the planned parallelism.
- **(b) valuation-parametric semantics** — the operational semantics takes a
  **leaf oracle** and `ref_wp_sound` quantifies over *all* oracles consistent
  with the leaf table's typing.

**DECIDED: (b).** Rationale (confirmed with Danielle's local model,
2026-07-14):

1. Preserves W5 ∥ W6 parallelism (the master plan's dependency shape: "W5 needs
   only W1/W2's shapes").
2. It is the natural reading of "leaves cancel at the semantic level": the same
   opaque leaf appears on both the goal side and the operational side, so its
   *interpretation* is irrelevant to whether the walk is faithful.
3. Front-loads the leaf-typing discipline W6 needs anyway.
4. It yields a **stronger** theorem: soundness holds for *any* oracle, so W6's
   later deepening (giving leaves concrete meaning) is a *specialisation* of an
   already-proven fact, never a re-proof.

Concretely the semantics is parameterised by three oracles (see §2), and
`ref_wp_sound` is `∀ oracles, …` — the "consistent with typing" side-condition
is currently trivial (all leaves range over the value universe `Int`); it
sharpens into a real leaf-table typing constraint at W5a-1/W6.

### 1.1 O5 decision (W5d) — PROPHECY = ∀-FINAL-VALUE, as spec adequacy (2026-07-15)

`DESIGN-bootstrap.md` O5 posed: model `&mut`/prophecy by **∀-quantifying the
final value** vs a **two-state** framing — "pick whichever makes W5d provable,
document as part of spec adequacy."

**DECIDED: ∀-final-value.** Rationale, grounded in the ACTUAL Verus encoding
(read off `verus/source/vir`, not first principles):

1. **It is what Verus does.** `&mut x` introduces a fresh prophesied final value
   `x_fut`; the caller does not know it, so it is **∀-quantified** (the standard
   RustHornBelt trick). `resolve` is `Assume(has_resolved(place))` — a
   **hypothesis** placed as a **statement** at the resolution point
   (`vir/src/ast.rs:1087` "`assume(has_resolved(place))`";
   `vir/src/resolution_inference.rs:77` "insert `Assume(HasResolved(p))`"), NOT
   an obligation to prove.
2. **The frame telescope already IS this model.** `closeSem`'s `FBind` arm is
   `∀ n, closeSem tail (upd st x_fut n) body` — literally the ∀-final
   quantification; the emitted `frame_after (Assume e) = frame_append f (FHyp e)`
   threads the resolve pin `FHyp(x == x_fut)` into the **continuation**. So the
   W5c `execSafeF` iff (total over `StmData`, arbitrary telescope) **subsumes**
   prophecy with **no new arm** — consistent with `DESIGN-W2-refwp` §2.6
   (`&mut` post-state flows through the same `post: FrameList` machinery as
   `Call`).
3. **Two-state is unnecessary.** `old(*x)` (an ordinary local id) and `x_fut`
   (the ∀-binder) are **distinct ids in one state** `St := Int → Int`; that is a
   projection of the two-state model into a single valuation, and it suffices —
   the ∀-final trick is precisely what lets a single-state WP talk about the
   final value without a genuine post-state.
4. **Temporal placement is the only real subtlety, and it is handled by the
   statement structure.** Because `resolve` is a *statement*, `frame_after`
   places its pin downstream (continuation obligations see it, upstream ones do
   not) — proven by `prophecy_sound` (gated `∀ x_fut, resolve → P`) vs
   `prophecy_swapped_sound` (ungated `∀ x_fut, P`). A hand-placed pre-frame
   `FHyp` would trivialize the borrow; the reference does not do that.

Landed as **probe25** (`probe-w0/probe25_w5d_sem/`), rc=0, axiom closure
`[propext, Quot.sound]`. Caller-side shape only (the site where the ∀-final trick
bites); the callee side (`&mut` param proving its ensures) is the ordinary `Ret`
obligation already covered by W5b/W5c.

---

## 2. The semantic model (the objects W5 introduces)

Types are named as they appear in the emitted Lean (`lib.*`); ids are `Int`
(u64 ids lower to `Int` in the mirror).

- **State** `St := Int → Int`. A total valuation of local ids to opaque values.
  Stage-A values are opaque, so `Int` is a placeholder universe, not a claim
  that locals are integers; W6 refines the value domain.
- **Prop oracle** `hp : Int → St → Prop`. The proposition denoted by an opaque
  leaf id — used for **hypotheses** (`FHyp h`) and opaque obligation leaves
  (`GoalData.Leaf`).
- **Expr oracle** `he : lib.ExprData → St → Prop`. The proposition denoted by a
  **deep** obligation expression — used for `GoalData.LeafE`. `render_exp` stays
  **opaque** under `he` (W5 does not evaluate rendering; that is W6/W7's bridge).
- **Value oracle** `lv : Int → St → Int`. The value denoted by a let-value leaf
  id — used for `FLet id v` and `GoalData.Let x v`.

`upd st x n := fun k => if k = x then n else st k`.

### 2.1 Goal denotation (`holds`) — the Val-level `toProp`

`holds : lib.GoalData → St → Prop`, structural on the goal:

| goal | meaning |
|---|---|
| `Leaf id`   | `hp id st` |
| `LeafE e`   | `he e st` |
| `Imp h t`   | `hp h st → holds t.deref st` |
| `All x ty t`| `∀ n : Int, holds t.deref (upd st x n)` |
| `Let x v t` | `holds t.deref (upd st x (lv v st))` |

`holdsAll : lib.GoalList → St → Prop` is the conjunction over a goal list.

This is the **Val-level** denotation of the master plan §4.3: `refWp` relates to
the operational semantics *at the data/Val level* in tactus; a thin hand-Lean
**adequacy spine** (`TGoal.toProp`, structural induction relating this Val-level
`holds` to the user-facing `Prop`s) is deferred to **W5f** — W5 v1 states
soundness at the Val level only, which is already the full drift-detector.

### 2.1.1 W5f decision (the adequacy-spine structure) — PIN-THE-ORACLES (2026-07-15)

The card (`bootstrap-54`) flagged a fork: wait for / co-design with W6's
`render_exp` semantics, or state the spine parametrically. **W6 is now done**
(`bootstrap-11`), so the spine co-designs with it. **DECIDED** (probe27, cross-
checked with Danielle's local model):

> `toProp := holds` **with the oracle triple PINNED** to concrete interpretations.
> The structural arms (Imp/All/Let) then bridge in ONE generic induction
> (definitional — `adequacy_spine` is `Iff.rfl`); ALL genuine content
> concentrates in **(a)** a concrete leaf denotation `edenote` and **(b)**
> per-user-type binder-embedding lemmas at the All arm.

This keeps the state space from exploding: the spine induction is generic (proved
once), and each user datatype contributes exactly ONE embedding lemma at the All
arm, not a re-proof of the spine.

**The SymEnv realization (why the pin is env-lookup, not new opacity).** The
emitted `ExprData.BinOp` **opcode is an interned `u64` id** (the serializer's
string table), NOT a fixed enum — `render_exp` rides it straight through
opaquely. So a *faithful* leaf denotation cannot know "op 2 means `<`" globally;
it grounds the interned ids through a **`SymEnv`** (`E.opk`/`E.av`/`E.fn`/… — the
per-crate environment literal of master plan §4.3, `probe4_denote` P4/P5).
`edenote (E : SymEnv)` thus replaces W5's **opacity** (`he` a free oracle) with
concrete **lookup**; the SymEnv is a concrete generated literal that
kernel-reduces, so the leaf bridge closes by `rfl`/`simp` (the P4 argument).
Pinning the oracle is *not* a second opacity layer — it is the honest
non-circular grounding.

**The binder-embedding lemma (the one real trap).** The Val model quantifies the
All arm over **all** of `Int` (`∀ n : Int`); the user reads `∀ u : U` over their
actual type. The per-type lemma `(∀ n:Int, P n) → (∀ u:U, P (emb u))` bridges
them (sound by over-approximation — the emitted all-`Int` goal is *stronger*).
The trap (flagged by the local model): a nested leaf in the body reads the bound
value from the threaded state — resolved because instantiating `n := emb u`
threads `upd st x (emb u)` into the body, decoding the value correctly; the body
is arbitrary, so it composes through nesting (probe27 `toProp_all_embed`).

### 2.1.2 W5f v2 decision (grounding the W7 body fragment) — SymEnv FN-PIN (2026-07-15)

W5f v1 (probe27) covered the arith/logical obligation fragment; the **W7 body
constructors** (`Ite`/`Match`/`AppN`/`Forall`/`Exists`) were stubbed. v2
(`bootstrap-55`, probe28) widens `edenote`/`eval` to them. The card asked how
`E.fn` gets grounded in the emitted def bodies. **DECIDED:**

> The grounding is a **SymEnv fn-pin, NOT an in-Lean `DefData` interpreter.** An
> interpreter over `DefData` bodies *cannot be a structural `def`* — a recursive
> spec fn's body re-enters its own call, so `eval` would need fuel / a fixpoint.
> Instead (the P5 shape) the concrete crate `SymEnv` literal **pins** `fn`/`fnN`
> to the **already-emitted Lean spec fns**. Recursion + termination live in the
> emitted defs (structural by W1.5); `eval`/`evalList` stay structural (each
> App/AppN arm = ONE oracle application over recursively-eval'd args); the
> rfl-bridge closes because the concrete env literal kernel-reduces.

**Independent of the W7 `def_eq` bridge.** W7's `def_eq` is *syntactic* (never
reduces bodies, §7.2); W5f v2 is the *denotational* counterpart. The denotation
layer needs only that the emitted defs exist and are pinned in the crate literal —
so v2 does NOT co-locate with the W7 defs-certificate machinery. Consequence: a
match-*bodied* fn is grounded through the fn oracle, so `eval` never interprets its
`Match`; eval-level body-node interpretation is only needed for nodes appearing
DIRECTLY in obligation goals.

**Per-node (probe28):** `App`/`AppN` grounded via `fn`/`fnN` (`eval`/`evalList` a
mutual structural pair); `Forall`/`Exists` genuine `∀`/`∃` (binder threaded via
`upd`, composes); `Ite` a decidable Bool-as-Int condition (O9 value/prop split, no
`Classical`). **`Match` remains scoped** — faithful eval-level Match needs the
flat-Int datatype-value-decode layer (`bootstrap-56`). Five v2 facts, all over the
real `lib.render_exp`, close over `[propext]`/`Quot.sound`/none.

### 2.2 Operational safety (`execSafe`) — no re-derivation of the frame

Reviewed as an honest reading (Danielle's local model, 2026-07-14: "defines
safety as satisfaction of obligations conditioned on the accumulation of
hypotheses, mirroring the program's sequential structure without assuming the
WP's correctness — avoids vacuity").

`execSafe : lib.StmData → St → Prop`:

| stmt | safe iff |
|---|---|
| `Skip`        | `True` |
| `Assume _`    | `True` (assume prunes; it never faults) |
| `Assert o _h` | `he (render_exp o) st` (an assert faults iff its obligation is false) |
| `Seq a b`     | `execSafe a.deref st ∧ (addedHyp a.deref st → execSafe b.deref st)` |

`addedHyp : lib.StmData → St → Prop` = the fact `frame_after` threads downstream:

| stmt | adds |
|---|---|
| `Assume e`    | `hp e st` |
| `Assert _ h`  | `hp h st` |
| `Skip`        | `True` |
| `Seq a b`     | `addedHyp a.deref st ∧ addedHyp b.deref st` |

**Deliberate:** `hp h` (asserted forward hyp, opaque leaf) and
`he (render_exp o)` (the obligation) are **independent oracles**, not
constrained equal. Production carries the assert's forward hyp as the bare
opaque leaf `h` and the obligation as the deep `o` (stage A: "hypotheses are not
deepened"). Soundness does **not** need them equal — the obligation is
discharged by its own goal; downstream safety is only *required* in states where
`hp h` holds, and we *assume* `hp h`. Keeping them independent yields the
stronger structural result (sound for any consistent oracle assignment).

### 2.3 The `safe s` top-level statement

For a whole fn, `safe s` quantifies over states satisfying the requires; the
seed frame's `FBind` params become `∀` and its `reqs`/bound hyps become
`frameHyps`. See §3 for how this lands across the sub-stages.

---

## 3. The proof skeleton (why it goes through)

Three structural bridging lemmas, then a statement induction:

- **Lemma A (close).** `holds (close_e f o) st ↔ (frameHyps f st → he (render_exp o) st)`
  for FHyp/FNil frames; the general frame adds `∀` (FBind) and `let` (FLet)
  layers, giving `closeSem f st (he (render_exp o) ·)`. Induction on `f`.
- **Lemma B (frame_after).** `frameHyps (frame_after f a) st ↔ frameHyps f st ∧ addedHyp a st`
  for `a` in the fragment. Cases on `a` + Lemma C.
- **Lemma C (frame_append).** `frameHyps (frame_append f g) st ↔ frameHyps f st ∧ frameHyps g st`.
  Induction on `f`.
- **Lemma D (goals_append).** `holdsAll (goals_append a b) st ↔ holdsAll a st ∧ holdsAll b st`.
  Induction on `a`.

**Main (fragment):** `holdsAll (wp_stm f s) st → frameHyps f st → execSafe s st`,
induction on `s`:
- `Skip`/`Assume`: `wp_stm = Nil`, `execSafe = True`. ✓
- `Assert o h`: `wp_stm = [close_e f o]`; from `holds (close_e f o) st` and
  `frameHyps f st`, Lemma A gives `he (render_exp o) st = execSafe`. ✓
- `Seq a b`: Lemma D splits the goals; IH on `a` (frame `f`) → `execSafe a`; given
  `addedHyp a st`, Lemma B gives `frameHyps (frame_after f a) st`, then IH on `b`
  → `execSafe b`. ✓

**Box-induction note.** Every recursive mirror type (`StmData`, `FrameList`,
`GoalList`) wraps its recursive fields in `Tactus.Box`, so Lean's plain
`induction` gives **no IH through the box**. Recurse instead by well-founded
recursion on `sizeOf` (`termination_by` + `decreasing_by`); the tactus prelude
ships `Tactus.Box.sizeOf_deref` as `@[simp]` exactly so `simp; omega` discharges
`sizeOf a.deref < sizeOf (Seq a b)`. (Alternatively `fun_induction`/`.induct` off
the emitted `wp_stm`, if the toolchain exposes it — the sizeOf route is the
portable one.)

---

## 4. The ladder (W5a–e, split into board cards)

Probe-first throughout (master plan §5): each stage is first proven as a
**hand-Lean probe over the emitted `lib.*` defs** (the analog of probe14 for the
bridge — no tactus-core rebuild), then authored as Rust spec/proof fns in
tactus-core (which forces the whole-crate re-verify + olean re-emit).

| Stage | Fragment / content | Board |
|---|---|---|
| **W5a-0** | `{Skip, Assume, Assert, Seq}`, FHyp/FLet frames, no `∀`-params. The core close/frame_after/goals_append induction. **First probe.** | bootstrap-49 |
| **W5a-1** | add `If` (two-way, no join — matches `wp_stm`'s flat If arm) + `FBind`/`∀` seed params + `reqs` as `frameHyps`; `ref_wp_sound` at the top level over `seed_frame`. | bootstrap-49 |
| **W5b** | `Call` (the exec call rule `DESIGN-emit-module` §4.4 leaves open) + `Ret`/`ret_frame`; the post-call frame as ∀/#128-ret-eq. | bootstrap-50 |
| **W5c** | `Loop` + havoc (`loop_maintain_frame`/`loop_use_frame`, init/maintain/decrease obligations); the WP loop rule — where the structured bugs live. | bootstrap-51 |
| **W5d** | `&mut` / prophecy — model `final`/resolve by ∀-quantifying the final value (the standard trick). Hardest modeling; do last. | bootstrap-52 |
| **W5e** | closures — `Seq (DeadEnd body) (Assume external_spec)`; no new arm (DONE). | bootstrap-53 |
| **W5f** | adequacy spine: hand-Lean `TGoal.toProp` + structural induction relating §2.1 Val-level `holds` to user-facing `Prop`s (lifts soundness from Val level to the theorems users prove). | bootstrap-54 |

Partial correctness first; termination/decreases obligations are their own
family (as Verus itself splits them) — modeled in `SstSem` via a well-founded
fuel argument, or W5 is scoped to partial correctness permanently (master plan
O6).

---

## 5. Status

- **2026-07-14 (opus-w5a-kickoff):** decision recorded (§1); model authored
  (§2–3) and peer-reviewed; ladder split into cards (§4); **W5a-0 probe**
  authored at `probe-w0/probe21_w5a_sem/` and driven toward elaboration against
  the emitted `lib.*` defs. See bootstrap-49 for the probe's live status.
- **2026-07-14 (opus-w5a1-if-params): W5a-0 AND W5a-1 both DONE (bootstrap-49
  closed).** W5a-1 probe at `probe-w0/probe22_w5a1_sem/` — rc=0, ~3.1s, axiom
  closure `[propext, Quot.sound]`. It generalises §3's skeleton from FHyp-only
  frames to an **arbitrary frame telescope** via `closeSem : FrameList → St →
  (St → Prop) → Prop` (FBind→∀, FHyp→→, FLet→let): the main theorem is now
  `holdsAll (wp_stm f s) st → closeSem f st (execSafe s ·)` with **no
  `isHypFrame` restriction**, covering `{Skip, Assume, Assert, Seq, If}` +
  the genuine all-`FBind` `lib.seed_frame`. A third oracle `lv : Int→St→Int`
  (let values, §2) is now live. The `frame_after` If fall-through
  (`¬cond`-forwarding, §2.2/§2.4.1) is out-of-fragment (needs Ret/DeadEnd) and
  collapses in-fragment via `diverges_zero_of_inFragment` → **W5b**
  (bootstrap-50) makes it live. **Next: W5b — Call + Ret/ret_frame.**
- **2026-07-14 (opus-w5b-callret): W5b DONE (bootstrap-50 closed).** W5b probe at
  `probe-w0/probe23_w5b_sem/` — rc=0, ~3.5s, axiom closure `[propext,
  Quot.sound]`. Adds `Call`/`Ret`/`DeadEnd`/`Assign` to the fragment (now
  `{Skip, Assume, Assert, Assign, Seq, If, Call, Ret, DeadEnd}`). **Design lift:**
  Call's `post` frame binds variables, which W5a-1's single-`Prop` `addedHyp`
  cannot model, so the `Seq` continuation generalised to `closeSem (frameDelta a)
  st body` and Lemma B became a corollary of the STRUCTURAL identity
  `frame_after f s = frame_append f (frameDelta s)` (`frame_after_eq_append`, +
  new `frame_append_assoc`/`frame_append_fnil_right`) + probe22's
  `closeSem_append`. This **retires `addedHyp` and `diverges_zero_of_inFragment`**.
  Call/Ret close via `holdsAll_close_each_e` (`obligsSafe`) + `closeSem_ret_frame`
  (RetLet binds the return value). The **If fall-through is now LIVE** — `Ret`/
  `DeadEnd` make `diverges = 1` reachable in-fragment, so `if C { ret } rest`
  forwards `¬C` (the W5a-1 caveat is discharged). `execSafe`'s Seq arm recurses
  under `closeSem`'s lambda and `termination_by structural` accepts it. **Next:
  W5c — Loop + havoc (bootstrap-51).**
- **2026-07-15 (opus-w5c-loops): W5c DONE (bootstrap-51 closed).** W5c probe at
  `probe-w0/probe24_w5c_sem/` — rc=0, ~2.9s, axiom closure `[propext,
  Quot.sound]`. Adds `Loop` (init / body / maintain-reclose / decrease + the
  havoc'd maintain/use telescopes), completing the whole `StmData` vocabulary.
  **The havoc fork (bootstrap-51):** a Loop's `frame_after`/maintain frames are
  `frame_append (havoc_lets f binders) tail` — `havoc_lets` DROPS mod-locals'
  pre-loop lets from the MIDDLE of `f`, so `frame_after f (Loop) ≠ frame_append
  f Δ` and the W5b `frameDelta`/`frame_after_eq_append` lift BREAKS; and no
  clean `closeSem f ↔ closeSem (havoc f)` bridge exists (intermediate opaque
  FHyp over a mod var). **Resolution (Opt-2, confirmed w/ Danielle's local
  model):** the operational predicate CARRIES the frame — `execSafeF f s st` —
  mirroring `wp_stm`'s threading; the Loop havocs `f` internally via the emitted
  `loop_maintain_frame`, and the four goal groups are each `holdsAll
  (close_each_e <opaque frame> obligs)` (frame-agnostic `holdsAll_close_each_e`)
  ⇒ the havoc is never decomposed. Two payoffs: (1) `execSafeF` is TOTAL on
  `StmData` ⇒ the theorem **sheds `inFragment` entirely** (soundness over the
  whole vocabulary); (2) W5b's `frameDelta`/`frame_after_eq_append`/
  `closeSem_frame_after`/`frame_append_*`/`closeSem_append`/`closeSem_ret_frame`/
  `retApply`/`diverges`/`is_skip` machinery is all DROPPED — Seq/If/Ret carry
  the threaded frame directly, and the theorem is now an **iff** (`holdsAll
  (wp_stm f s) st ↔ execSafeF f s st`, sound + faithful). Decrease is MODELED
  (emitted + must hold at body-end); the well-founded termination argument stays
  its own family (O6). **Next: W5d — &mut/prophecy (bootstrap-52).**
- **2026-07-15 (opus-w5d-prophecy): W5d DONE (bootstrap-52 closed).** W5d probe
  at `probe-w0/probe25_w5d_sem/` — rc=0, ~3.0s, zero warnings, axiom closure
  `[propext, Quot.sound]` on all four theorems. **O5 RESOLVED = ∀-final-value
  model** (§1 addendum below). W5d is a **frame/statement-level model, not a new
  arm** — per `DESIGN-W2-refwp` §2.6, `&mut` post-state flows through the same
  `post: FrameList`/statement machinery as `Call`, so the W5c `execSafeF` iff
  (total over StmData, arbitrary telescope) already subsumes it. Verified against
  the ACTUAL Verus encoding (not first principles): `&mut x` → a fresh
  ∀-quantified final `x_fut` (= an `FBind`; `closeSem`'s FBind arm IS the
  ∀-final quantification), and `resolve` = `Assume(has_resolved)` — a HYPOTHESIS
  placed as a STATEMENT (`vir/src/ast.rs:1087`, `resolution_inference.rs:77`),
  NOT an obligation. The emitted `frame_after (Assume e) = frame_append f (FHyp
  e)` threads the resolve pin into the CONTINUATION. Main result `prophecy_sound`:
  the reference WP for `resolve; assert P(*x)` reduces EXACTLY to `∀ x_fut,
  resolve(x_fut) → P(x_fut)`. **Temporal-placement subtlety** (flagged by
  Danielle's local model — the worry that an FHyp shifts the pin to the wrong end
  of the borrow): discharged by `prophecy_swapped_sound` — the swapped
  `assert; resolve` reduces to the UNGATED `∀ x_fut, P(x_fut)`, so the two forms
  DIFFER (they could not if resolve were a pre-body FHyp), proving `frame_after`
  places the pin temporally-correctly. Negative control (drop the resolve gate)
  fails elaboration ⇒ the iff bites. **Next: W5e — closures (bootstrap-53).**
- **2026-07-15 (opus-w5e-closures): W5e DONE (bootstrap-53 closed).** W5e probe
  at `probe-w0/probe26_w5e_sem/` — rc=0, ~3.0s, zero warnings, axiom closure
  `[propext, Quot.sound]` on all six theorems. **Closures need NO new StmData
  arm** — like prophecy (W5d), a closure IS `Seq (DeadEnd body) (Assume
  external_spec)`, both constructors already in the 10-constructor vocabulary.
  Verified against the ACTUAL Verus encoding (not first principles): a
  `NonSpecClosure` (`ast.rs:1058`) lowers to `ClosureInner{body}` +
  `Assume(external_spec)` (`ast_to_sst.rs:1964`); `ClosureInner` compiles to
  `StmtX::DeadEnd(body)` (`sst_to_air.rs:2566`); the body
  (`exec_closure_body_stms`, `:3556`) is assume-requires / body / assert-ensures —
  pure W5a–c statements. Spec closures (`ExprX::Closure`) → a pure `BndX::Lambda`
  opaque leaf. The load-bearing emitted fact is `frame_after f (DeadEnd b) = f`
  (the DeadEnd quarantines the body's hyps from the continuation). **Main result
  `closure_creation_sound`:** the reference WP for `Seq (DeadEnd body) (Assume
  ext)` reduces EXACTLY to `execSafeF f body st` — closure creation = body
  obligation under the enclosing frame; wrapper + Assume add nothing. **Isolation
  subtlety** (flagged by Danielle's local model — the "creation vs. invocation"
  quantification worry; its param premise was wrong for the reference but the
  structural instinct was right): discharged by `closure_deadend_isolates`
  (DeadEnd-wrapped assume → UNGATED continuation) vs `seq_assume_gates` (bare
  assume → GATED), which DIFFER (impossible if the DeadEnd failed to isolate) +
  negative control. ∀-params is via the outer `∀ st` (params are fresh ids, not
  frame binders — matching AIR fresh constants); creation-time-context reliance is
  sound by the **frozen-environment invariant** (Verus forbids mutable capture,
  `closures.rs::check_closure_well_formed`) — a spec-adequacy point. **Next: W5f —
  adequacy spine (bootstrap-54); the whole StmData vocabulary + prophecy +
  closures are now sound at the Val level.**
- **2026-07-15 (opus-w5f-spine): W5f v1 FIRST RUNG DONE (bootstrap-54, probe27).**
  Probe at `probe-w0/probe27_w5f_spine/` — rc=0, ~3.2s, zero warnings, axiom
  closures `[propext]` (leaf bridges) / none (embedding) / `[propext, Quot.sound]`
  (concrete soundness + carried core). **Fork RESOLVED = pin-the-oracles** (§2.1.1
  above): `toProp := holds` at a concrete oracle triple, factored into a concrete
  leaf denotation `edenote (E : SymEnv)` + per-type binder-embedding lemmas; the
  spine induction is generic (`adequacy_spine` is `Iff.rfl`). **Co-designs with W6
  (now done):** consumes the real emitted `lib.render_exp` as the data-level
  bridge. Four facts over the REAL emitted defs: (1) `adequacy_leaf_cmp`
  (`edenote (render_exp (x<10))` ≡ `E.av x st < 10`); (2) `adequacy_leaf_overflow`
  (`edenote (render_exp (HasType 64 e))` ≡ `0 ≤ e ∧ e < 2^64` — the §2 cast/
  overflow silent-unsoundness class, now checked DENOTATIONALLY); (3)
  `toProp_all_embed` (the Int↔U binder embedding, resolving the model-flagged
  state-threading trap; instantiated at `U:=Nat, emb:=Int.ofNat`); (4)
  `soundness_concrete` (carried `ref_wp_sound` at the concrete triple — emitted
  goals read concretely ⟺ safety). **The SymEnv realization:** the emitted BinOp
  opcode is an interned id (not a fixed enum), so `edenote` grounds ids through a
  `SymEnv` (opacity → env-lookup, the P4/P5 shape) — not a second opacity layer.
  **Scope:** the arithmetic/logical obligation fragment (atoms/lits/arith/cmp/
  logical/casts/apps/proj/let/span — what P4 + the fixture obligations use); the
  W7 body nodes (`Ite`/`Match`/`AppN`/`Forall`/`Exists`) are sentinel-stubbed → a
  v2 rung (a `Defs`-layer denotation grounding `E.fn` in `render_def` bodies).
  **The W5 ladder (W5a–e Val-level + W5f v1 adequacy) is now complete for the
  stage-A obligation fragment: the reference WP is sound AND its soundness lifts
  to the user-facing Props on that fragment.**
- **2026-07-15 (opus-w5f-v2): W5f v2 DONE (bootstrap-55, probe28) — body fragment
  widened.** Probe at `probe-w0/probe28_w5f_v2/` — rc=0, ~3.5s, extends probe27
  verbatim. `eval`/`edenote`/`evalList` now TOTAL over the full `ExprData` vocab;
  faithful denotations for **four of five** W7 body constructors. **Grounding fork
  RESOLVED = SymEnv fn-pin** (§2.1.2 above): pin `fn`/`fnN` to the emitted Lean
  defs, NOT an in-Lean interpreter (which couldn't be structural); independent of
  the W7 `def_eq` syntactic bridge. Five v2 facts over the REAL `lib.render_exp`:
  `adequacy_leaf_app_grounded` (`g(n)<10` ≡ `g(av n)<10`, `g:=E.fn`),
  `adequacy_leaf_forall`/`_exists` (genuine `∀`/`∃`, binder threaded via `upd`,
  composes), `adequacy_leaf_ite` (decidable Bool-as-Int cond — O9 split, no
  `Classical`), `adequacy_leaf_appn_grounded` (n-ary `h [av m, av n]<100`,
  `h:=E.fnN`, exercising the `evalList` fold). Axioms `[propext]`/`Quot.sound`/
  none — no `sorryAx`, no `Classical.choice`. **`Match` scoped** → bootstrap-56
  (flat-Int datatype-value-decode; the fn-pin already covers match-*bodied* fns,
  so only `match`-in-obligation is affected).

## 5. Final status — THE LOOP IS CLOSED (2026-07-18)

The W5 arc is complete, end to end:

- **Model + proofs authored in tactus** (bootstrap-60..65): `holds`/
  `holds_all`/`close_sem_e`/`close_sem_obligs`/`exec_safe_f` +
  `wp_stm_sound` (11-arm induction) + `ref_wp_sound` + the nine
  prophecy/closure corollaries — verified lean-only-clean, 138/0.
- **Per-fn kernel closure** (bootstrap-73): the Link discharge layer
  makes every one of those theorems a premise-free `_closed` theorem
  (67/67, 0 pending) — option (iii) of the bootstrap-66 design fork, no
  hand chain-discharge, no drift gate. Residual interface: the R-b wf
  hypotheses (`StmDataWf s`, `FnCtxDataWf c`), by-construction for
  serializer output.
- **Composition** (bootstrap-66, `probe-w0/probe37_loop_closure/`): the
  adequacy spine's Val-level spec IS the authored model (abbrevs); FACT 4
  = `iff_of_eq (lib.ref_wp_sound_closed …)` — definitional unification,
  zero bridging lemmas; the ~200-line hand `wp_stm_sound` induction is
  deleted. Composed closure `[propext, Classical.choice, Quot.sound]`,
  no sorryAx. Runner = `probe37_loop_closure/run.sh` (builds the Link
  olean from the live emission; exit-0 discipline).

What remains trusted above this theorem is exactly VERIFICATION-PATH §5's
permanent residue: the adequacy spine (denotation, oracle pins, binder
embeddings) as the written-down SPEC, the serializer, the frontend, the
kernel. The claim ladder's rung 5 is reached.
