# Decision: keep `nat → Nat`; fix the `as nat` inconsistency by materializing consistently — not Option B, not a closer rung

**Status:** Decided 2026-06-02 (Danielle). Resolves the deliberately
"non-committal" framing of [`DESIGN-cast-hygiene.md`](DESIGN-cast-hygiene.md),
which laid out the options without choosing.

> **Implementation update (2026-06-05).** The *policy* below is unchanged
> (`nat → Nat`; not Option B; not a closer rung; `as nat` renders as a
> consistent `ℕ`). The *mechanism* changed: instead of a Tactus-side
> `insert_nat_coercions` pre-pass re-materializing the `Clip` after Verus
> dropped it, Verus now **keeps** the `uN/usize → nat` cast as `Clip{Nat}`
> directly, gated on a `--lean-backend` flag (vstd builds without it, Z3 path
> unchanged). The ~200-line `nat_coercion.rs` module is deleted; the gate is
> ~20 lines. This keeps every `as nat` consistently `ℕ` more uniformly than
> the pre-pass did (it now covers comparisons too). See DESIGN.md
> § "U → Nat coercion — gated Verus `Clip` for the Lean backend".

**TL;DR:** Tactus keeps rendering Verus `nat` as Lean `Nat`. The `as nat` cast
*inconsistency* (Friction 2) is fixed by rendering `as nat` **consistently** —
a nat-typed arithmetic op materializes its Int-rendering operands to `Int.toNat`,
so `(x as nat) * f(…)` renders the same `ℕ` form everywhere. This is **not**
Option B (`nat → Int` + `0 ≤ x` bound, rejected) and **not** an auto-extended
closer (Option A's rung, rejected). It is a faithful, visible rendering change
that keeps `nat → Nat`, and it landed with **zero blast radius** (482 e2e / 0,
vstd 1530 / 0).

---

## Background

`DESIGN-cast-hygiene.md` explored three options for the `Int.toNat` "paper cut"
that surfaces when an exec fn over `uN` types (`u8 … u128`, which render as Lean
`Int` with a `0 ≤ x ∧ x < 2^N` bound) is verified against a recursive `spec fn`
over `nat` (which renders as Lean `Nat`):

- **Option A** — keep the rendering; add a named `Tactus.CastHygiene` simp set
  and a `tactus_auto` rung that folds `Int.toNat` shapes before `omega`.
- **Option B** — render `nat` as `Int` with a `0 ≤ x` bound hypothesis (mirroring
  how the `uN` types already work); deletes the `insert_nat_coercions` pre-pass;
  closes the USize subtraction soundness gap as a side effect.
- **Option C** — emit spec fns as `opaque` + equation axioms (mirror Verus's Z3
  encoding); breaks `unfold`/`simp [f]`, adds an asserted-axiom trust delta.

The concrete trigger was `BUG-ch5-pow-iter-lowering-frictions.md` (the tutorial's
exponentiation-by-squaring capstone), which named three frictions:

- **Friction 1** — a loop's invariant clauses were glued into a single `∧`
  hypothesis, so non-splitting user tactics (`nlinarith`, `linarith`,
  `assumption`) couldn't reach a buried fact. **Fixed** independently — invariant
  clauses now push as individual `CtxFrame::Hyp` frames (`walk_loop`;
  `test_exec_loop_invariant_clauses_split_for_user_tactic`). Not a cast question.
- **Friction 2** — the *same* surface `as nat` renders in `ℤ` in one position and
  `ℕ` in another. **This is the inconsistency this document is about.** Verus
  *elides* the `uN → nat` cast on a bare variable (`result as nat` → `result :
  Int`) but *keeps* it on a compound (`(result * b) as nat` → `Int.toNat (…)`,
  because the inner product is unbounded `Int` in spec mode) and Tactus
  re-materializes it on call args. So an invariant `(result as nat) * pow(…)`
  landed in `ℤ` while a structurally-identical assert landed in `ℕ`, and the two
  wouldn't combine with the `ℕ` spec-fn facts a proof naturally produces.
- **Friction 3** — `pow`'s body `(e - 1) as nat` renders `Int.toNat (↑e - 1)`, so
  once-unfolded recursive indices carry cast noise (`↑e.toNat - 1` vs `e - 1`).
  Separate normalization, not addressed here.

---

## Decision

1. **Keep `nat → Nat`.** Do not adopt Option B.
2. **Do not auto-extend `tactus_auto`** with a cast-hygiene simp set (Option A's
   closer rung).
3. **Fix the Friction-2 inconsistency by rendering `as nat` consistently** — a
   nat-typed arithmetic op materializes any Int-rendering operand to `Int.toNat`.
   Landed (see "The fix that landed").

---

## Why not Option B (`nat → Int`)

The deciding cost is *not* the ~1–2 week implementation (the feared vstd audit
was already de-risked — vstd has zero `Nat.succ`-style bodies). It's two **values**
costs:

- **`0 ≤ x` proliferation.** Rendering `nat` as `Int` forces a `0 ≤ x` bound
  hypothesis to accompany *every* nat-typed value, the same way the `uN` types
  already carry `0 ≤ x ∧ x < 2^N`. Every spec-fn signature and every goal that
  mentions a nat picks up extra `0 ≤ …` clutter that `nat → Nat` gets for free —
  because in `Nat`, non-negativity is **intrinsic to the type**, not a separate
  fact to carry and discharge.
- **Transparency regression.** `nat → Nat` is the *faithful* mapping: Verus's
  `nat` is exactly "non-negative integer," and Lean's `Nat` is the one-to-one
  mirror, with non-negativity carried by the type itself. `nat → Int + (0 ≤ x)`
  demotes a type-level fact to an external hypothesis. Strictly **less
  self-documenting**.

This is the *same* principle Tactus already chose elsewhere, deliberately:

- **Wrapper types over peeling** (DESIGN § "Why we keep the wrappers: faithfulness
  to Rust types"). Tactus renders `&Box<u8>` as `Tactus.Ref (Tactus.Box Nat)` —
  exactly — rather than peeling to bare `Nat`, paying a visible `.deref` / `.mk`
  cost, *because* faithfulness to the source type beats collapsing it into
  something more convenient. `nat → Nat` over `nat → Int` is the identical trade.
- **Keep SMT-shaped artifacts, handle uniformly downstream** (DESIGN §
  "Self-assignment snapshot temps"; `feedback_transparency_is_faithfulness`):
  *transparency = faithfulness + predictability, not artifact-minimization.*

Option B *would* dissolve Frictions 2 & 3 and close the USize gap — but it buys
that by making every nat value noisier and less faithful **everywhere**. The
consistent-materialization fix below gets the Friction-2 win without that global
cost.

---

## Why not extend the closer (Option A)

Option A keeps `nat → Nat` (good) and folds the `Int.toNat` shapes in the closer.
We don't adopt it as an automatic `tactus_auto` rung for two reasons:

- **It cuts against minimal automation.** The standing preference is to keep
  `tactus_auto` minimal and prefer *transparent user proofs* over extending the
  closer's simp set (`feedback_minimal_automation`, `feedback_layered_automation`).
  An always-on cast-folding rung is exactly that kind of silent closer extension —
  the proof on screen would no longer reflect the reasoning. Same line drawn for
  the `Bool.xor_comm` gap (DESIGN § "Bool vs Prop").
- **It doesn't fix the inconsistency.** A folds the `Int.toNat` *in the closer*,
  so proofs close — but the *rendering* stays inconsistent: `result as nat` still
  shows as `result` (`ℤ`) and `(result * b) as nat` as `Int.toNat (…)` (`ℕ`). A
  buys consistent *closing*, not the consistent *rendering* the concern was about.

---

## The fix that landed: consistent `as nat` materialization on arithmetic operands

**Mechanism.** Verus elides a bare `x as nat` (a `u64` is trivially a nat) to
`x : U(64)`, but the enclosing op keeps its `IntRange` — a nat product is
`ArithOp Mul (… IntRange Nat)` even when its operand reads as `U(64)`. In Lean
`U(_)` renders `Int` and `nat` renders `Nat` (distinct types), so an Int-rendering
operand under a nat-typed op needs the `Int.toNat` the elided cast would have
produced. The coercion pass (`rewrite_one_call_for_coercions{,_expr}` in
`sst_to_lean.rs`, both the SST and VIR-AST sides) gains a `BinaryOp::Arith` arm:
for a nat-typed arith op, wrap any operand where
`needs_nat_coercion(operand.typ, e.typ)` in `Clip{Nat}`. The op's own result type
(`e.typ`) is the operand type for arith ops, so it's the coercion target — the
same `needs_nat_coercion` predicate the call-arg path already uses.

Result: `(x as nat) * f(…)` renders `Int.toNat x * f …` uniformly with the
compound and call-arg cases (which Verus already materializes). The pow chapter's
invariant goes from `result * ↑(pow …) = ↑(pow …)` (`ℤ`) to
`result.toNat * pow … = pow …` (`ℕ`), so it combines with the `ℕ` spec-fn facts
and matches the body asserts' `ℕ` form.

**Why this is the right shape** (and a different, better category than A and B):

- **Faithful, not lossy** — it *honors* the `as nat` the user wrote, instead of
  silently dropping it. Strictly *more* transparent than the elision.
- **Predictable** — `as nat` means one thing (`ℕ`) everywhere. The property the
  decision is about.
- **Keeps `nat → Nat`** — no `0 ≤ x` proliferation. Not Option B.
- **A rendering choice, visible in output** — not an invisible closer rung. Not A.
- **Sound by construction** — `Int.toNat x` with `0 ≤ x` in scope is exactly the
  cast `as nat` denotes; same semantics the call-arg pass already relies on
  (vstd 1530/0).
- **Precise / zero blast radius** — fires *only* on nat-typed arith ops with
  Int-rendering operands, which only arise from `as nat`-typed spec arithmetic.
  Full e2e suite 482/0 (incl. the new pin), vstd 1530/0 — nothing existing moved.

**Pinned by** `test_exec_arith_operand_as_nat_materializes`: `(x as nat) * (x as
nat) == sq(x as nat)` closes via `simp only [sq]` (core, no Mathlib) *only* when
the LHS materializes to `Int.toNat x * Int.toNat x` to match `sq`'s unfolded `ℕ`
body — fails without the change.

**Scope limits (honest).** This fixes the Friction-2 *rendering inconsistency*; it
is not a turnkey "the chapter verifies":

- **Comparisons / `Eq` are not arith ops** and have no clean "expected nat operand"
  signal, so `result * b <= pow(…)` (a `ℤ` product compared to a `ℕ` pow, no
  `as nat`) stays mixed. That's intentional: the user controls that boundary by
  writing `(result * b) as nat <= …`, which then materializes consistently.
- **Friction 3 is untouched** (the `↑e.toNat - 1` vs `e - 1` index noise).
- **Existing hand-written proofs authored against the old `ℤ` shape** may need a
  small update to meet the new (cleaner, uniform-`ℕ`) shape — e.g. an equality
  maintain whose goal now equals the invariant hypothesis just needs `exact`.

---

## When to revisit (Option B specifically)

The two *no*s stand, but Option B would be reconsidered if:

- The **USize subtraction soundness gap** (DESIGN § "usize/isize bounds";
  `USize → Nat` lets `x - y` truncate silently) becomes load-bearing enough to
  force a uniform-`Int` rendering. B closes it as a side effect, and that
  *soundness* pressure could outweigh the `0 ≤ x` *ergonomics* cost. (A and C have
  their own disqualifiers, so a soundness fix would specifically raise B.)
- The `0 ≤ x` clutter turns out, on a real spec library, to be cheaper than feared
  *and* a class of cast frictions the consistent-materialization fix doesn't cover
  (comparisons, Friction 3) becomes a recurring, load-bearing pain.

Absent those, `nat → Nat` + consistent `as nat` materialization is the
proportionate, faithful answer.
