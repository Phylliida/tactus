# Cast hygiene in Tactus: three options

## Problem

Tactus currently renders Verus integer types as follows:

| Verus type | Lean type | Bound hypothesis |
|---|---|---|
| `int` | `Int` | — |
| `nat` | `Nat` | (implicit in type) |
| `u_N` (u8/u16/u32/u64/u128) | `Int` | `0 ≤ x ∧ x < 2^N` |
| `i_N` | `Int` | `-2^(N-1) ≤ x ∧ x < 2^(N-1)` |
| `usize` | `Nat` | (none; see below) |
| `isize` | `Int` | `-isize_hi ≤ x ∧ x < isize_hi` |
| `char` | `Nat` | `x < 0x110000` |

This rendering forces a coercion every time a `u_N`-typed value flows into a `nat`-typed position — most commonly when an exec fn's iterative implementation relates to a recursive `spec fn` taking `nat` (the canonical "factorial-style" verification pattern).

After BUG-as-nat-cast.md's fix (2026-05-15), Tactus's `insert_nat_coercions_in_{exp,stm,expr}` pre-pass inserts `Clip(Nat, _)` at Call sites where args render as Int but params render as Nat, producing `Int.toNat` in the Lean output. This closes the *correctness* problem — the bug doc's reproducer verifies. But it leaves a *usability* paper cut: chains of `Int.toNat` operations in goals (e.g., `fib (↑k + 1 - 2).toNat`) trip up `omega`, which then needs `simp` lemmas it doesn't have. Every recursive spec proof ends up with 1-3 `rw [show ... from by omega]` lines of casting ceremony.

The tutorial-writing audience hits this on every chapter that verifies an iterative algorithm against a recursive specification.

## Why this is a Tactus problem and not a Z3 problem

Z3's model is fundamentally different:

- **No types in the Lean sense.** Everything is `Int` with refinement predicates (`is_u64(x) := 0 ≤ x ∧ x < 2^64`; `is_nat(x) := 0 ≤ x`). No casts because there's nothing to cast *between*.
- **Spec fns are uninterpreted function symbols with equation axioms**, not recursive definitions. `declare-fun fact (Int) Int` plus `(assert (= (fact 0) 1))` and `(assert (forall ((n Int)) (=> (> n 0) (= (fact n) (* n (fact (- n 1)))))))`. Fuel-bounded unrolling controls how many axiom instances Z3 considers.
- **No totality requirement.** Axioms only constrain known cases. "What does `fact` return on `-5`?" is meaningless to ask — the value is whatever Z3 chooses to satisfy the constraints.
- **`decreases` is a Verus-level obligation**, not part of the SMT encoding. Verus emits `n' < n` constraints at recursive call sites; Z3 checks them.

Lean has different fundamentals:

- **Strict type discipline.** `Nat` and `Int` are distinct types.
- **Defs must be well-founded.** Recursive definitions need a termination proof so they have a meaning in the kernel.
- **Functions must be total.** `f x` has a value for every `x` in the domain.
- **Reducible by default.** `simp [f]` and `unfold f` work on definitions in a way they don't on axioms.

The cast complexity in Tactus comes from absorbing Z3's "untyped Int + refinements" model into Lean's "strict types + well-founded defs" model. The three options below pick different points on the absorption gradient.

---

## Option A: Cast hygiene lemmas

Keep the current rendering. Add a small focused simp set in `TactusPrelude.lean` that normalizes `Int.toNat` expressions, and a ladder rung in `tactus_auto` that tries it.

### What Lean sees

Unchanged from today. Spec fns are clean `noncomputable def`s on `Nat`. Loop invariants relating u-typed values to nat-typed spec fns contain `Int.toNat` chains, which the simp set folds into omega-friendly forms before the final omega rung.

### Prelude additions

```lean
namespace Tactus.CastHygiene
  @[simp] theorem toNat_ofNat (n : Nat) : (↑n : Int).toNat = n := ...
  theorem toNat_of_nonneg {n : Int} (h : 0 ≤ n) : (n.toNat : Int) = n := ...
  theorem toNat_add_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b).toNat = a.toNat + b.toNat := ...
  theorem toNat_sub_nonneg {a b : Int} (hba : b ≤ a) (hb : 0 ≤ b) :
    (a - b).toNat = a.toNat - b.toNat := ...
  -- ... a handful more for the (↑k + a - b).toNat shape family
end Tactus.CastHygiene
```

### `tactus_auto` extension

```lean
macro "tactus_auto" : tactic => `(tactic|
  tactus_first
    | rfl
    | decide
    | omega
    | simp_all
    | (simp_all only [Tactus.CastHygiene] <;> omega)   -- new rung
    | tactus_case_split (simp_all <;> first | omega | done)
    | tactus_case_split (simp_all)
    | fail "...")
```

### What it doesn't fix

- USize subtraction soundness gap (DESIGN.md flags this; unchanged here).
- The visual noise of casts in generated Lean — they're cleaned by tactics, but they still appear in goal states the user might inspect.
- Edge-case cast shapes that the lemma set didn't anticipate (each surfaces as a `tactus_auto` failure; user adds an explicit `simp [Tactus.CastHygiene]` at the assertion site).

### Pros

- **Smallest change.** ~1-2 days to implement, well-bounded lemma set.
- **Reversible.** If we later move to Option B or C, delete the simp set — nothing built on top.
- **Substrate-class, not user-domain.** The lemmas clean up artifacts of Tactus's own rendering choice (the user didn't write `Int.toNat`, our pre-pass did). Different category from the xor-comm pushback — those were user-domain algebraic identities; these are boundary normalizers.
- **Conservative on `tactus_auto`.** New rung uses `simp_all only [Tactus.CastHygiene]` (named scope) plus omega; doesn't pollute the default simp set.
- **No churn.** Existing tests, vstd, spec fn semantics all unchanged.

### Cons

- **Maintenance burden grows.** Every new cast shape that omega can't fold becomes a new lemma. The set could grow to 20+ over time.
- **Doesn't eliminate the friction, just papers it.** Users still see `Int.toNat` in goal states. When `tactus_auto` doesn't close, users have to know to invoke `simp [Tactus.CastHygiene]` themselves.
- **USize gap stays open.**
- **Tutorial readability hit.** Generated Lean output (a `cat` away) still has `Int.toNat` clutter. Proof-script readers see it.

### Implementation scope

- ~1-2 days of focused work.
- New file or section in `TactusPrelude.lean` for the simp set.
- One new ladder rung in `tactus_auto`.
- 2-3 e2e tests modeling the factorial chapter's invariant shapes (e.g., `fib (↑k + 1 - 2).toNat`).
- DESIGN.md updates documenting the substrate framing.

---

## Option B: Render Verus `nat` as Lean `Int`

Change `typ_to_expr`'s `IntRange::Nat` arm to return `Int` instead of `Nat`. Emit a `0 ≤ x` bound hypothesis for nat-typed values via `type_bound_predicate`. Same pattern u-types already use.

### What Lean sees

```lean
-- Before:
noncomputable def fact (n : Nat) : Nat :=
  match n with | 0 => 1 | k + 1 => (k + 1) * fact k

-- After:
noncomputable def fact (n : Int) : Int :=
  if h : n ≤ 0 then 1 else n * fact (n - 1)
termination_by n.toNat
decreasing_by simp_wf; omega
```

User code:
```rust
proof fn lemma_u64_to_nat(i: u64)
    ensures fact(i as nat) ≥ 0
by { omega }
```

Before:
```lean
theorem lemma_u64_to_nat (i : Int) (h_i_bound : 0 ≤ i ∧ i < 2^64) :
    fact (Int.toNat i) ≥ 0 := by omega
```

After:
```lean
theorem lemma_u64_to_nat (i : Int) (h_i_bound : 0 ≤ i ∧ i < 2^64) :
    fact i ≥ 0 := by omega
```

`omega` works directly — no toNat to chase.

### Substrate work

1. **`typ_to_expr`**: `IntRange::Nat` returns `Int`. Similarly for `Char` (currently Nat) and possibly `USize`.
2. **`renders_as_lean_int`**: add `Nat`, `Char`, possibly `USize` to the "renders as Int" set.
3. **`type_bound_predicate`**: emit `0 ≤ x` for nat-typed values. (Char and Usize have analogous bounds.)
4. **`spec_fn_to_ast`**: for recursive spec fns with `decreases n` (n : nat), translate to `termination_by n.toNat` and emit a `decreasing_by` block with appropriate tactic.
5. **Spec fn body totality**: for recursive nat-typed defs, add a guard for the negative-input case (`if n ≤ 0 then default_value else recursive_body`). Verus's mode checker prevents Tactus from ever calling these with negative inputs in practice, but Lean still requires totality for the def to elaborate.
6. **Delete `insert_nat_coercions_in_*`**: ~250 lines come out (the entire bug-fix pass).
7. **Spec fn body audit**: any spec fn body using `Nat`-specific operations (`Nat.succ`, `match n with | 0 => ... | k+1 => ...`, `Nat.zero?`) needs translation. Most Verus spec fns use generic operators (`+`, `-`, `*`, `==`, `if`) which work uniformly on Int.
8. **Test re-verification**: every Tactus e2e test that mentions a nat-typed signature in generated Lean sees the signature change. Most pass automatically; need a careful sweep.

### Bonus: USize soundness gap

DESIGN.md notes: *"USize subtraction truncates silently — `let r: usize = x - y` for usize `x, y` truncates at zero if `y > x`. Parallel to the u8-subtraction soundness hole before the u8 → Int change. Proper fix is the same: find a way to make USize render as Int without breaking const-generics."*

The const-generic break was caused by Verus eliding `as nat` casts from usize in spec contexts, making const-generic bodies `N as nat` render as `Int` while the declared return type was `Nat`. **If `nat` renders as Int, the const-generic body `N as nat` becomes `Int → Int` (USize as Int, nat as Int) — no mismatch.** USize can then also render as Int, closing the subtraction soundness gap.

One change, two known issues closed.

### What it doesn't fix

- **Decidability through definitions changes slightly.** `decide : fact 5 = 120` currently reduces via Nat's structural rec. With Int + guard, `decide` still works but goes through the `if n ≤ 0` branch first; equivalent but slightly heavier reduction.
- **Pattern matching on nat-as-Int is different.** `match n with | 0 => ... | k+1 => ...` becomes `if n = 0 then ... else let k := n - 1 in ...` — same semantics, different syntactic form. Users coming from Lean's natural pattern style may find Tactus-emitted spec fns less idiomatic to read.

### Pros

- **The cast paper cut disappears entirely.** Not patched — gone. No casts to clean up.
- **`omega` works uniformly across all numeric reasoning.** Tutorial proofs become Lean-standard.
- **Closes the USize soundness gap** as a side effect.
- **Deletes the nat-coercion pre-pass.** Architectural simplification.
- **Generated Lean is cleaner.** No `Int.toNat` clutter in goals or output.
- **Substrate cost is one-time.** Once Tactus emits the right termination/totality plumbing, it's done.

### Cons

- **Bigger one-time substrate cost.** ~1-2 weeks of focused work.
- **Spec fn defs are slightly less idiomatic.** Lean readers expecting `match n : Nat with | 0 => ... | k+1 => ...` see `if n ≤ 0 then ... else ...` instead.
- **Termination measure becomes `n.toNat`**, requiring a substrate translation that's invisible to the user but a maintenance point for Tactus.
- **Spec fn body audit** for `Nat.succ`-style uses is one-time but non-trivial across vstd's spec library.
- **All existing tests need re-verification.** Bounded but tedious sweep.

### Implementation scope

- ~1-2 weeks of focused work.
- ~6 files touched in `lean_verify`: `to_lean_type.rs`, `to_lean_sst_expr.rs`, `to_lean_fn.rs`, `sst_to_lean.rs`, `generate.rs`, `expr_shared.rs`.
- Delete `insert_nat_coercions_in_*` and its supporting infrastructure.
- DESIGN.md updates documenting the rendering choice and substrate translations.
- All e2e + unit tests re-verify.
- vstd audit for `Nat`-specific operations in spec fn bodies.

---

## Option C: Spec fns as `opaque + axiom` (mirror Z3 directly)

Render Verus spec fns not as Lean recursive defs but as opaque function symbols with equation axioms. Mirrors Z3's `declare-fun` + assertion encoding directly.

### What Lean sees

Before:
```lean
noncomputable def fact (n : Nat) : Nat :=
  match n with | 0 => 1 | k + 1 => (k + 1) * fact k
```

After:
```lean
opaque fact : Int → Int
axiom fact_eq_zero : fact 0 = 1
axiom fact_eq_pos : ∀ (n : Int), 0 < n → fact n = n * fact (n - 1)
```

User code that previously used `unfold fact; omega` now uses `rw [fact_eq_pos h]; omega` (or names a single combined equation lemma).

### Substrate work

1. **Spec fn emission overhauled**: instead of one `Command::Def`, emit `Command::Axiom` (opaque) plus per-branch equation axioms.
2. **Body case analysis**: traverse the spec fn body, extract per-case equations. For `if c then a else b`, emit two axioms: `c → fact = a` and `¬c → fact = b`. For `match`, one axiom per arm. For complex bodies (nested matches, computed conditions), may need helper definitions.
3. **Termination + totality become non-issues.** Axioms only constrain known cases; no WF check.
4. **Render nat as Int** (same as Option B — axioms work on Int).
5. **Delete `insert_nat_coercions_in_*`** (same as Option B).
6. **Provide unfold ergonomics**: Tactus could emit a convention like `@[simp] theorem fact_def : ∀ n, fact n = if n ≤ 0 then 1 else n * fact (n - 1) := by ... (using the axioms)`, giving `simp [fact_def]` users a familiar idiom. But this re-introduces the recursive simp loop concern (see below).
7. **Test re-verification.**

### What it doesn't fix

- **The `unfold` muscle memory.** `unfold fact; omega` currently works because `fact` is a `def`. With axioms, it becomes `rw [fact_eq_pos h]` or `simp [fact_eq_pos]`. Lean users coming from Mathlib will write `unfold` and get nothing.
- **`decide : fact 5 = 120` becomes slow.** With a def, `decide` reduces via the kernel's evaluation. With axioms, it has to rewrite step-by-step (and a recursive `@[simp]` axiom needs fuel control to avoid looping).
- **`simp [fact]` no longer expands recursively.** Lean's simp on defs unfolds them up to a depth. On axioms, only the literally-rewritable cases fire.

### Pros

- **Mirrors Verus's Z3 encoding directly.** The fewest translation degrees of freedom. The "Verus's spec fn is encoded correctly" claim becomes: "Tactus's axioms match Verus's assertion set." Verus's own correctness story propagates.
- **No termination/totality machinery.** The cleanest substrate.
- **All cast complexity dissolves** (Int everywhere, same as Option B).
- **Closes USize soundness gap** (same as Option B).
- **Conceptually elegant for Z3-trained users.** Fuel-bounded unfolding via explicit axiom rewrites maps onto their existing mental model.

### Cons

- **Diverges from "standard Lean" proof idioms.** `unfold f` doesn't work. `simp [f]` doesn't auto-unfold. Users reading Mathlib proofs can't directly apply patterns to Tactus theorems.
- **Recursive `@[simp]` axioms can loop.** `@[simp] axiom fact_pos : ∀ n, 0 < n → fact n = n * fact (n-1)` would expand `fact n` to `n * fact (n-1)` indefinitely. Solution: don't `@[simp]`-tag recursive equations; require explicit `rw` or fuel-guarded unfolding. Trades automation for predictability.
- **Decidability through computation breaks.** `decide` can't reduce concrete cases through axioms.
- **Axiom emission is more complex than def emission** for spec fns with non-trivial structure. Match arms, nested ifs, computed conditions — each becomes an axiom or a helper.
- **Soundness footprint subtly grows.** Currently, spec fn defs are checked by Lean's kernel for well-formedness. Axioms are asserted. The trust delta isn't large (we already trust Tactus's translation correctness), but it's a visible shift.
- **Pedagogical cost for tutorial.** Newcomers learning verification through Tactus would be learning a non-standard Lean idiom; transferable knowledge to other Lean projects (Mathlib) decreases.

### Implementation scope

- ~1 week of focused work for the axiom emission (more if spec fn body shapes are diverse).
- ~6 files touched (similar to Option B).
- vstd audit for spec fn body shapes that resist clean axiomatization.
- Provide `@[simp]`-tagged unfold lemmas where safe (non-recursive cases); document the rewrite-tactic idiom for the rest.
- Substantial DESIGN.md updates documenting the new spec fn emission strategy.
- All e2e + unit tests re-verify; many proof scripts need adjustment for the new unfold idiom.

---

## Comparison

| | A: Cast lemmas | B: Render-as-Int | C: Axioms |
|---|---|---|---|
| Time to implement | 1-2 days | 1-2 weeks | ~1 week |
| Pre-pass deleted | No | Yes (~250 lines) | Yes (~250 lines) |
| Cast clutter in goals | Reduced (lemmas fold most) | Gone entirely | Gone entirely |
| USize soundness gap | Open | **Closed** | **Closed** |
| `omega` Just Works on numeric proofs | Usually | Yes | Yes |
| `unfold f` works | Yes | Yes | **No (rw instead)** |
| `simp [f]` expands | Yes | Yes | **No** |
| `decide` on concrete cases | Yes | Yes | Slow / loops without fuel |
| Recursive spec fn elaboration | Standard | Substrate translation | Axiomatic |
| Spec fn body audit needed | No | Yes (Nat-specific ops) | Yes (axiomatize each shape) |
| Translation correctness story | Substrate translation | Substrate translation | Direct mirror of Verus's Z3 encoding |
| Soundness trust delta | None | None | Axioms asserted (slight increase) |
| Tutorial impact | Some `simp [CastHygiene]` ceremony | Clean Lean-standard proofs | Non-standard unfold idiom |
| Reversibility | Just delete prelude lemmas | Delete + add back pre-pass + re-render | Delete + add back defs |

## Open questions

These are unresolved enough to warrant probing before committing to any option:

1. **For Option B**: how does Verus's `recursion::check_decrease` interact with `n.toNat` as a termination measure? Does the existing `CheckDecreaseHeight` lowering (which Tactus already does for proof fn recursive calls) generalize cleanly, or do recursive spec fns need a different obligation shape?

2. **For Option B**: which spec fns in vstd use `Nat.succ` or `match n : Nat with | 0 => ... | k+1 => ...` style? Quick grep would scope the audit.

   *Probed 2026-05-17.* vstd has zero uses of `Nat.succ` / `.succ()` syntax. Spec fns taking `nat` use generic integer operators (`==`, `-`, `*`, `<`, `if`) and route through `as nat` casts. The recursive nat-typed spec fns are minimal:
   - `arithmetic/power.rs` — `pow(b: int, e: nat) -> int decreases e` (body: `if e == 0 { 1 } else { b * pow(b, (e - 1) as nat) }`). Generic operators only.
   - `arithmetic/power2.rs` — `pow2(e: nat) -> nat` delegates to `pow` (not directly recursive).
   - `arithmetic/logarithm.rs` — `log(base: int, pow: int) -> int` takes int, not nat (not affected).
   - Other vstd files with `nat`-typed spec fn params (`endian.rs`, `bits.rs`, `seq.rs`, etc.) use them as length / count arguments, not in recursive structural-match patterns.

   **Audit cost is LOW.** Under Option B, the `pow` translation would be `if e ≤ 0 then 1 else b * pow b (e - 1)` with `termination_by e.toNat`. No `Nat`-specific machinery to replace; bodies are already generic-operator-clean. The audit pessimism in the original Option B writeup was overestimated.

3. **For Option C**: what's the right `@[simp]` tagging policy? Non-recursive equations can be `@[simp]` safely. Recursive equations need either explicit fuel control or a wrapper lemma that's safe to `@[simp]`. Worth probing.

4. **For Option C**: how does `unfold` semantics on `simp [fact_def]` actually feel in practice? May be cleaner than expected if the equation lemmas are named well.

5. **All three**: what does the factorial chapter LOOK like under each? Three side-by-side full proofs of `factorial(n: u64) -> u64 returns fact(n as nat)` would directly answer "which is better pedagogically?"

## Decision criteria

The right answer depends on which property dominates:

- **If "ship the tutorial chapter this month" dominates**: Option A. Bounded, reversible, fastest path to unblocked.
- **If "give tutorial readers the cleanest Lean-standard proof experience" dominates**: Option B. Substrate cost is real but one-time; user experience is permanently better.
- **If "match Verus's Z3 encoding as faithfully as possible" dominates**: Option C. Conceptual elegance; trade-off is non-standard Lean idioms.
- **If "close USize soundness gap" matters**: B or C (A doesn't address it).
- **If "audience knows Mathlib and expects standard Lean idioms" matters**: A or B (C diverges).
- **If "audience comes from SMT/Z3 and finds axiom-style natural" matters**: C (idiomatic to that mental model).

Not mutually exclusive in sequence: A as a tactical step, then B or C later if the friction proves too high, is a valid path. The lemmas from A would become dead code after a migration but cost little to remove.

---

*Document written 2026-05-16 as a non-committal design exploration for the Tactus cast-hygiene problem surfaced by tutorial-chapter writing on factorial verification.*
