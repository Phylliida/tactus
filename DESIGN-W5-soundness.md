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
| **W5e** | closures. | bootstrap-53 |
| **W5f** | adequacy spine: hand-Lean `TGoal.toProp` + structural induction relating §2.1 Val-level `holds` to user-facing `Prop`s (lifts soundness from Val level to the theorems users prove). | (spun out when W5a–e land) |

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
