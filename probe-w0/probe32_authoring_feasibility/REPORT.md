# probe32 — W5 loop-closure AUTHORING feasibility

**Board:** bootstrap-59. **Date:** 2026-07-14.
**Run:** `probe-w0/probe32_authoring_feasibility/run.sh` (real tactus binary,
`--lean-backend --lean-all-proofs`, isolated scratch crate, no tactus-core rebuild).

## Why this probe exists

The W5 soundness ladder is proven as **hand-Lean probes** (probe21..31) over the
emitted `lib.*` defs. Genuine **loop closure** (DESIGN-W5-soundness §0, §4) requires
*authoring* that soundness as Rust spec/proof fns **inside tactus-core**, verified by
the tactus binary (routed to Lean) and emitted as a kernel-checked package.

But tactus-core today contains **zero `spec_fn`-typed params** and **zero recursive
proof fns** — every one of its proof fns is a closed `by { decide }` bridge. So loop
closure had two untested mechanism questions, which this probe answers by porting a
**stripped** `wp_stm_sound` (probe21) — the mechanism spine minus the frame machinery
(whose soundness the hand-Lean already proved):

- **Q1** — does the Verus→Lean backend accept a **`spec_fn` leaf oracle** param (the
  valuation-parametric model, DESIGN-W5 §1 option b) in spec fns AND proof fns, and
  emit it kernel-clean?
- **Q2** — can it author a **recursive structural-induction `proof fn`** (the analog of
  `wp_stm_sound`) with a recursive helper lemma?

## Result

### Q1 — CONFIRMED (the crux). `spec_fn` oracle + recursive spec fns author + verify + emit clean.

`8 verified` in the run:
- The 4 oracle-parametric recursive `open spec fn`s — `gappend`, `all_true(hp, ·)`,
  `wp`, `exec_safe(hp, ·)` — where `hp : spec_fn(u64) -> bool` is the leaf oracle.
  The backend translates `spec_fn(u64)->bool` to Lean `Int → Prop` and emits the
  recursive defs (structural, over `Box`-nested own datatypes) with a clean axiom
  closure. **This was THE feasibility unknown for loop closure and it is positive:
  the valuation-parametric leaf-oracle semantics is expressible in tactus-core.**
- The 4 one-step **unfold lemmas** `u_gappend_nil/cons`, `u_all_true_nil/cons`
  (empty-body `proof fn`s whose `ensures` is a single constructor-unfold equation)
  — they verify, i.e. the default closer `tactus_auto` **does** discharge an isolated
  one-step unfold of a recursive `open spec fn`.

### Q2 — STRUCTURE works; the compound discharge needs a custom closer (mechanism found).

Verus accepts the recursive structural-induction `proof fn` shape: it generates the
per-arm VCs, and (with `#[verifier::structural_decreases]` on the proof fn) discharges
the **height-decrease termination VC**, and threads the **induction hypothesis** into
the Lean context correctly (verified by reading the emitted `lib__*.lean`).

The gap is purely **discharge of the compound postcondition**. Measured, atomic-by-
atomic, what the default `tactus_auto` closer does and does not do:

| closer sub-goal | `tactus_auto`? |
|---|---|
| isolated one-step unfold `all_true hp (Cons g t) = hp g && all_true hp t.deref` | ✅ closes |
| variable→constructor bridge `a == GList::Nil` / `== Cons(g,t)` inside the match arm | ✅ closes |
| single rewrite `gappend(a,b) == b` (using bridge + unfold) | ✅ closes |
| boolean simp `(true && x) == x` | ✅ closes |
| **compound postcondition** `all_true hp (gappend a b) = (all_true hp a && all_true hp b)` (multi-hyp substitution + ∧-assoc, all facts in context) | ❌ **fails** |

So `tactus_auto` is a **local/atomic** closer — one unfold, one rewrite, one bool-simp —
but it does **not** perform the multi-hypothesis rewriting a structural-induction
postcondition needs (that is `simp_all`, a T2 dev-tactic per DESIGN-transparent-
automation §2). The hand-Lean probe21 closes the analogous goal with
`simp only [u_* rfl-lemmas]` — a **T1** tactic.

**The mechanism to supply that is found:** `#[verifier::tactus_tactic("first |
tactus_auto | (<custom Lean tactic>)")]` — a per-fn attribute
(`source/lean_verify/src/sst_to_lean.rs:964`, `attributes.rs:692`) that overrides the
closer for every VC of the fn. The tactus corpus uses it with real multi-step tactics,
e.g. `tactus-group-theory/src/runtime.rs:376`:
`"first | tactus_auto | (intros <;> simp only [lib.…Gen_val0, …] <;> rw […] <;> congr 1)"`.

**What is NOT done (honest):** the exact `tactus_tactic` string that closes the
induction postcondition. A first attempt `first | tactus_auto | (intros <;> simp_all)`
left the goal unsolved — the emitted VC carries the body asserts as `let`-bound Props
plus `_tactus_ret : Unit` binders, which the naive `simp_all` doesn't consume; a
correct closer must `subst`/case the bridge equality and rewrite (probe21's
`simp only [u_*]` shape is the model, adapted to the projector-form VC). This is
**tactic engineering, not a mechanism blocker** — it is the concrete next rung.

## Bottom line for loop closure

- **The math is done** (hand-Lean probe21..31).
- **The hard authoring unknown is resolved positive** (Q1): tactus-core CAN carry the
  `spec_fn`-oracle valuation-parametric recursive semantics with a clean axiom closure.
- **The one remaining blocker is a discharge idiom** for the induction postconditions:
  a per-fn `#[verifier::tactus_tactic]` closer (T2 `simp_all` for discovery → squeezed
  to T1 `simp only [named u_* lemmas]` for the artifact). Building that string, then
  scaling to the real `wp_stm_sound` + its frame lemmas, is the loop-closure authoring
  work — now precisely scoped, mechanism-known, no open feasibility question.

## Files

- `lib.rs` — the probe. `Stm`/`GList` mirror datatypes; `gappend`/`all_true`/`wp`/
  `exec_safe` oracle-parametric spec fns; `u_*` unfold lemmas (verify); `all_true_append`
  (recursive append lemma) + `wp_sound`/`wp_sound_bites` (the soundness rung) — the
  latter three carry the atomic-step scaffold and fail only on the compound discharge.
- `out/lib/pkg/lib__*.lean` — the emitted VCs (read these to see the IH threading and
  the exact unsolved goal).
