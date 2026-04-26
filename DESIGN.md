# Tactus Design Document

Tactus is a verified Rust tool built by modifying Verus to use Lean 4's proof kernel instead of Z3. All proof obligations go through Lean — there is no Z3 backend. Users write `.rs` files with specs and Lean-style tactic proofs. The `.rs` files are the single source of truth.

## Why

Verus uses Z3 (SMT solver) for proof checking. This works well for simple obligations but causes pain for hard mathematical proofs:

- **Context pollution**: Z3 is superlinear in proof size. Functions >50 assertions consistently fail even with high rlimit.
- **No goal states**: Z3 says "assertion might not hold" with no indication of what remains to prove.
- **Manual guidance**: Users write 150+ line assert chains to guide Z3 through algebraic identities.
- **eqv infrastructure**: Z3 needs explicit equivalence relations (`eqv`) with congruence axioms, symmetric/transitive chains, direction management.
- **Fragile automation**: Z3's heuristics are unpredictable. Small edits can cause rlimit explosion.

Lean replaces all of this:

- **Tactics**: `ring`, `omega`, `nlinarith`, `simp`, `field_simp` solve in one line what takes 150 lines of assert chains.
- **Goal states**: On failure, Lean shows exactly what remains to prove.
- **Propositional equality**: `==` maps to Lean's `=`. No `eqv`, no congruence axioms, no direction flipping.
- **Mathlib**: Hundreds of thousands of proven lemmas for algebra, analysis, number theory, etc.
- **Deterministic**: Tactics either work or show remaining goals. No heuristic rlimit games.

## Design principles

1. **Transparency**: Nothing happens automatically behind the user's back. Imports are explicit. Mutual recursion is user-declared. No magic auto-detection.
2. **Lean-native**: All proofs go through Lean. No Z3, no SMT, no dual backend. Tactic proofs are the only proof language.
3. **Source of truth**: `.rs` files contain everything. No separate `.lean` files for users to manage.
4. **Minimal axioms**: Every axiom is a soundness risk. Use `def` instead of `axiom` when the value is computable. Keep the trusted base small.

## Pipeline

### Verus today
```
.rs → verus! macro → rustc_driver → HIR → VIR-AST → VIR-SST → sst_to_air → AIR → SMT-LIB → Z3
```

### Tactus
```
.rs → tactus! macro → rustc_driver → HIR → VIR-AST → VIR-SST → sst_to_lean → Lean 4 → lean kernel
```

We replace `sst_to_air` (and everything after it) with `sst_to_lean`. The AIR crate, SMT-LIB encoding, and Z3 invocation are removed entirely.

### Why cut at SST?

**VIR-AST** has the original program structure but hasn't generated verification conditions yet.

**VIR-SST** is a cleaned-up AST: no side effects in expressions, no statements inside expressions. It's the input to VC generation.

**AIR** is too low — it encodes generics as `Poly` (universal type with box/unbox, an SMT workaround for Z3's lack of parametric polymorphism) and generates triggers. Lean has native parametric polymorphism and doesn't need triggers. Translating AIR → Lean would mean undoing SMT-specific encodings.

We implement **fresh VC generation targeting Lean directly** in `sst_to_lean`, rather than reusing `sst_to_air`. This avoids inheriting SMT-specific design decisions (Poly encoding, trigger inference, fuel encoding, expression flattening).

### Proof fns vs exec fns

**Proof fns** (with `by { ... }` tactic blocks) bypass VC generation entirely:
- `requires` → Lean theorem hypotheses
- `ensures` → Lean theorem goal
- Tactic body → Lean proof (verbatim pass-through)

**Exec fns** need VC generation (loops, mutation, overflow, bounds):
- VIR → SST (existing `ast_to_sst`, unchanged)
- SST → Lean VCs via `sst_to_lean` (new, Phase 2)
- Each obligation becomes a Lean `theorem` with auto-tactics

Phase 1 implements proof fn support. Phase 2 implements exec fn VC generation — this is the **hard part** (see Phased Implementation).

## What Tactus code looks like

### Lean imports (first-class syntax, explicit)

```rust
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
```

`import` is a first-class Tactus keyword, not a macro. It mirrors Lean's import syntax exactly because these ARE Lean imports — they control what `import` statements appear in the generated Lean. Users explicitly declare which Mathlib modules they need. No auto-detection.

Tree-sitter-tactus recognizes `import` declarations at the top of files. The proc macro passes them through to the Lean generation layer.

### Spec functions

```rust
spec fn double(x: nat) -> nat {
    x + x
}

spec fn triangle(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + triangle((n - 1) as nat) }
}
```

### Spec fn opacity model

All spec fns are **irreducible by default** — Lean tactics cannot see their bodies unless explicitly unfolded. This prevents Lean's elaborator from diverging on recursive functions and gives users full control over what gets unfolded.

- `spec fn` → `@[irreducible] noncomputable def` (body hidden, use `unfold f` in tactics)
- `open spec fn` → `noncomputable def` (body visible to `simp` and other tactics)

The Verus attribute `#[verifier::opaque]` is redundant with the default and is not needed. In Tactus, all spec fns behave like Verus's `opaque` by default. `open` is the opt-in for transparency.

This matches how well-written Lean code works — you mark definitions `@[irreducible]` and explicitly control unfolding. The `reveal(f)` pattern from Verus maps to `unfold f` in tactic blocks.

### Mutual recursion (user-specified)

```rust
mutual
spec fn is_even(n: nat) -> bool
    decreases n
{
    if n == 0 { true } else { is_odd((n - 1) as nat) }
}

spec fn is_odd(n: nat) -> bool
    decreases n
{
    if n == 0 { false } else { is_even((n - 1) as nat) }
}
end mutual
```

Mirrors Lean's `mutual ... end` syntax. Mutual recursion is not inferred — the user wraps mutually recursive functions in `mutual ... end mutual`.

### Proof functions (tactic bodies)

```rust
proof fn lemma_norm_nonneg(re: int, im: int, d: int)
    requires d <= 0
    ensures re * re - d * (im * im) >= 0
by {
    nlinarith [sq_nonneg re, sq_nonneg im]
}
```

The `by` keyword signals "what follows is Lean tactic syntax, not Rust." This is visually distinct from exec fn bodies and unambiguous to the parser.

### Proof blocks inside exec functions

```rust
fn compute(x: u32) -> (result: u32)
    requires x < 100
    ensures result == x + 1
{
    let result = x + 1;
    proof {
        // Tactic proof — results thread into VC context
        have h : result == x + 1 := by omega
    }
    result
}
```

`proof { ... }` keeps its syntax. The body is Lean tactics. Tactic results (`have h : P := by ...`) are threaded into the VC context as hypotheses for subsequent proof obligations (handled by `sst_to_lean` in Phase 2).

### Exec functions with auto-generated obligations

```rust
fn binary_search(v: &Vec<i32>, target: i32) -> (idx: Option<usize>)
    requires is_sorted(v@)
    ensures match idx {
        Some(i) => i < v.len() && v@[i as int] == target,
        None => !v@.contains(target),
    }
{
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi
        invariant
            lo <= hi <= v.len(),
            forall|i: int| 0 <= i < lo ==> v@[i] < target,
            forall|i: int| hi <= i < v.len() ==> v@[i] > target,
        decreases hi - lo
    {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < target {
            lo = mid + 1;
        } else if v[mid] > target {
            hi = mid;
        } else {
            return Some(mid);
        }
    }
    None
}
```

Auto-generated obligations (from `sst_to_lean`, Phase 2) are checked with `tactus_auto`. If it fails, the user sees the goal state and can add an explicit `proof { }` block.

### Assume expressions

```rust
assume(P);  // → have : P := sorry (with compiler warning)
```

`assume(P)` translates to `have : P := sorry`. Tactus emits a warning: "unproved assumption at line N". This is the escape hatch for incremental development.

## Unicode and Lean syntax in tactic blocks

Lean tactics use Unicode: `⟨a, b⟩`, `·`, `∀`, `∃`, `¬`, `∧`, `∨`, `→`, `↔`, `≤`, `≥`, `≠`. They also use `--` line comments, `/- -/` nestable block comments, and other syntax that isn't valid Rust.

### The problem

Rust's lexer runs before any proc macro or parser sees the source. Unicode punctuation like `⟨⟩` causes lexer errors, and Lean syntax like `--` or `/- -/` isn't recognized. The proc macro never gets a chance to see the content.

### The solution: FileLoader sanitization

A custom `FileLoader` intercepts `read_file()` before rustc's lexer runs. It finds tactic blocks (`by { }`, `proof { }`, `assert(...) by { }`), and replaces their content with spaces — same byte length, preserving newlines.

```
.rs file (on disk)
  │
  └→ TactusFileLoader.read_file()
       1. Read original file
       2. Find tactic blocks (by {}, proof {})
       3. Replace content between { } with spaces (same byte offsets)
       4. Return sanitized source to rustc
  │
  ├→ rustc lexer/parser → proc macro → VIR
  │   (sees only spaces inside tactic blocks — no Unicode errors)
  │   proc macro records byte range via Span::byte_range()
  │
  └→ At verification time: read ORIGINAL file at byte range → real tactic text
```

The FileLoader scanner:
- **Phase 1 (Rust context)**: scans for `by` or `proof` keywords with word-boundary checks, skipping Rust strings (`"..."`, `r#"..."#`), comments (`//`, `/* */`), and char literals
- **Phase 2 (Lean context)**: counts braces to find matching `}`, understanding Lean `--` line comments, `/- -/` nestable block comments, and `"..."` strings (all of which can contain `}`)
- **Phase 3**: replaces content between `{` and `}` with spaces, preserving `\n`

Byte offsets are identical between sanitized and original, so `Span::byte_range()` works unchanged.

### `//` in tactic blocks

`//` (Lean's integer division) is **not supported** in tactic blocks. Use `Nat.div` or `Int.div` instead. This avoids a fundamental conflict: Rust's lexer treats `//` as a line comment (consuming the rest of the line including potential `}`), and tree-sitter's extras mechanism makes `//` comments globally unavoidable in the grammar.

In practice, `//` rarely appears in tactic proofs. Tactics are proof steps (`omega`, `simp`, `ring`, etc.), not computations. `--` is the Lean comment syntax and works correctly.

### tree-sitter-tactus grammar

tree-sitter-tactus has Lean-aware rules for tactic block content:
- `_tactic_brace_body`: `{ ... }` with Lean-aware content parsing
- `_tactic_item`: handles `--` comments, `/- -/` nestable block comments, `"..."` strings, Unicode content, nested `{ }` braces
- `line_comment` stays in `extras` (global) — `//` is treated as a Rust comment everywhere including tactic blocks

The grammar has **184 tests** including 36 tactic-specific tests covering all Lean syntax edge cases.

## Keyword handling in tactic blocks

### The `forall`/`exists` conflict

`forall` and `exists` are Verus keywords with special syntax (`forall|x| P`). Inside tactic blocks, they may appear as Lean identifiers (`exact forall_comm`).

**Fix**: The proc macro enters "tactic mode" when processing `by { }` or `proof { }` bodies. In tactic mode, all Verus-specific keyword parsing is suspended. The body is captured as a `TokenStream` (balanced braces handled by Rust's tokenizer) and the **source span** is recorded as `TacticBlock(span)` in VIR.

The actual tactic text (including any Unicode) is retrieved from tree-sitter-tactus's output at Lean generation time, using the span as a key. The proc macro never needs to understand or represent Unicode tactic content.

### `assert forall` auto-intro

```rust
assert forall|x: nat, y: nat| x + y == y + x by {
    omega
}
```

The translation auto-inserts `intro` for quantified variables:
```lean
have h : ∀ (x y : Nat), x + y = y + x := by
  intro x y
  omega
```

## Tactic block parsing (tree-sitter-tactus)

Inside `by { }` and `proof { }`, we parse Lean-like tactic syntax drawing from tree-sitter-lean's grammar. Well-known tactics get specific rules (for highlighting and structure). Unknown tactics fall through to a balanced token-tree catch-all.

Key Lean syntax supported:
- `| name binders => ...` (induction/cases arms)
- `·` and `.` for focusing
- `⟨a, b⟩` anonymous constructors
- `[expr, expr, ...]` simp/rw lemma lists
- `at h` / `at *` location specifiers
- Nested `by { }` inside `have`

## Equality model

`==` in spec mode maps to Lean's `=`. No `eqv` trait, no congruence axioms, no direction management.

In VIR, equality is `ExprX::Binary(BinaryOp::Eq(Mode::Spec), lhs, rhs)`. The translation emits `l = r`.

### Extensional equality

Verus's `=~=` (extensional equality) also maps to Lean's `=`. This is correct because Lean 4's type theory includes function extensionality: for function types, `f = g ↔ ∀ x, f x = g x` is provable (via `funext`). So Lean's `=` on functions IS extensional equality — no separate encoding needed.

In VIR: `BinaryOpr(ExtEq(deep), l, r)` → `l = r` in Lean. The `deep` flag (for nested extensionality on collections, etc.) is also handled by Lean's `=` since it's structural equality on inductive types.

### Migration

`eqv(a, b)` translates to `a = b`. Congruence axioms become trivially true. Existing code works — the `eqv` infrastructure is redundant but not broken.

## Lean invocation

### Mathlib setup (precompiled oleans)

Tactus manages a persistent Lake project:

```
~/.tactus/
  lean-project/
    lakefile.lean        # imports Mathlib
    lean-toolchain       # pins Lean version
    .lake/               # precompiled Mathlib oleans
    TactusPrelude.lean   # built-in type definitions (Seq, Set, etc.)
    _check/              # temp generated .lean files
```

First-run setup:
```bash
tactus setup
# 1. Creates ~/.tactus/lean-project/
# 2. Writes lakefile.lean with Mathlib dependency + lean-toolchain
# 3. Runs `lake exe cache get` to download precompiled Mathlib oleans
#    (~2 GB download, ~2-5 minutes — no compilation needed)
# 4. Done
```

If precompiled oleans aren't available for the pinned toolchain, falls back to `lake build` (~30-60 min, 16+ GB RAM). Clear progress indication shown.

`tactus setup --no-mathlib` creates the project without Mathlib for faster setup (core Lean tactics only: `omega`, `simp`, `decide`, `exact`, `apply`, `intro`, `induction`, `cases`, `rfl`).

### Invocation

```bash
lake env lean ~/.tactus/lean-project/_check/MyModule.lean --json -q
```

Per-module `.lean` files generated in `_check/`. Each file imports `TactusPrelude` and the user's declared imports.

### Caching

Lean's `.olean` caching handles incremental checking. Unchanged modules skip re-elaboration. We do NOT use Verus's function-level SHA-256 cache — Lean's built-in caching is sufficient.

## Generated Lean structure

### Namespacing

Generated Lean definitions use VIR's `Path` (fully qualified name) as namespace:

```lean
namespace my_crate.my_module

@[irreducible] noncomputable def double (x : Nat) : Nat := x + x

theorem lemma_double_pos (x : Nat) (h₀ : x > 0) : double x > x := by
  unfold double
  omega

end my_crate.my_module
```

This prevents name collisions between modules. Tactic bodies reference function names within the same namespace — `unfold double` works because `double` is in scope.

### Definition ordering

Lean requires definitions before use within a file. Generated definitions are topologically sorted using VIR's call-graph dependency information.

Mutual recursion uses `mutual ... end` blocks (from the user's `mutual ... end mutual` declarations in Tactus source).

### Prelude (TactusPrelude.lean)

The prelude defines Verus's built-in types. **No `sorry`, no unnecessary axioms.** Values known at compile time use `def`, not `axiom`.

```lean
import Mathlib.Data.Int.Lemmas

-- Seq type (Verus's spec-level sequence)
abbrev Seq (α : Type) := List α

namespace Seq
  def empty : Seq α := []
  def len (s : Seq α) : Nat := s.length

  -- Opaque indexing: in-bounds is specified, out-of-bounds is truly unspecified.
  -- Using opaque + axiom ensures no equalities are provable between different
  -- out-of-bounds indices, exactly matching Verus's semantics.
  opaque index {α : Type} (s : Seq α) (i : Nat) : α
  @[simp] axiom index_in_bounds {α : Type} (s : Seq α) (i : Nat) (h : i < s.length) :
      index s i = s[i]'h

  def push (s : Seq α) (x : α) : Seq α := s ++ [x]
  def subrange (s : Seq α) (lo hi : Nat) : Seq α := (s.drop lo).take (hi - lo)
  def update (s : Seq α) (i : Nat) (x : α) : Seq α := s.set i x
  def contains [DecidableEq α] (s : Seq α) (x : α) : Prop := x ∈ s
end Seq

-- Set type
abbrev VerusSet (α : Type) := Set α

-- Integer clip functions (fixed-width type semantics)
def u_hi (bits : Nat) : Nat := 2 ^ bits
def i_lo (bits : Nat) : Int := -(2 ^ (bits - 1))
def i_hi (bits : Nat) : Int := 2 ^ (bits - 1)
def u_clip (bits : Nat) (x : Int) : Nat := (x % (u_hi bits)).toNat
def i_clip (bits : Nat) (x : Int) : Int :=
  let m := u_hi bits
  let r := x % m
  if r ≥ i_hi bits then r - m else r

-- Arch word size — axiom because the correct value depends on the compilation
-- target, and we want proofs to hold for the declared architecture without
-- hardcoding a specific value. Axiom is sound as long as --target matches
-- the actual deployment architecture.
axiom arch_word_bits : Nat
axiom arch_word_bits_valid : arch_word_bits = 32 ∨ arch_word_bits = 64
```

### Axiom inventory

The prelude's trusted base:
1. `Seq.index` (opaque constant) — existence of a total indexing function
2. `Seq.index_in_bounds` — in-bounds behavior matches `List.get`
3. `arch_word_bits` — word size for the target architecture
4. `arch_word_bits_valid` — word size is 32 or 64

Axioms 1-2 are sound by construction: any total function from `List α × Nat → α` that agrees with `List.get` on in-bounds indices satisfies these. `Classical.choice` guarantees such a function exists.

Axioms 3-4 are a configuration parameter — sound as long as `--target` matches the deployment platform.

Cross-crate declarations (see below) add axioms for externally-verified theorems. Each is sound assuming the source crate verified correctly and the translation was correct.

All other prelude definitions are `def` (computable, no trust needed).

### Spec fn translation

Default (irreducible):
```rust
spec fn double(x: nat) -> nat { x + x }
```
→
```lean
@[irreducible] noncomputable def double (x : Nat) : Nat := x + x
```

Open (transparent):
```rust
open spec fn double(x: nat) -> nat { x + x }
```
→
```lean
noncomputable def double (x : Nat) : Nat := x + x
```

Recursive with `decreases`:
```rust
spec fn factorial(n: nat) -> nat
    decreases n
{ if n == 0 { 1 } else { n * factorial((n - 1) as nat) } }
```
→
```lean
@[irreducible] noncomputable def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)
termination_by n
```

### Proof fn translation

```rust
proof fn lemma_double(x: nat)
    requires x > 0
    ensures double(x) > x
by {
    unfold double
    omega
}
```
→
```lean
theorem lemma_double (x : Nat) (h₀ : x > 0) : double x > x := by
  unfold double
  omega
```

**Rules**:
- Each `requires` clause → hypothesis parameter `(hᵢ : clause)`
- `ensures` clause → theorem goal
- Multiple ensures → conjunction `E₁ ∧ E₂ ∧ ...` (user splits with `constructor` or `refine ⟨?_, ?_⟩`)
- Tactic body → verbatim after `:= by`
- Named return `-> (result: T)` → `result` bound in the goal

### Auto-generated obligations (Phase 2)

Each exec fn obligation becomes a separate Lean theorem:

```lean
macro "tactus_auto" : tactic => `(tactic|
  tactus_first
    | rfl
    | decide
    | omega
    | simp_all
    | tactus_case_split (simp_all <;> first | omega | done)
    | tactus_case_split (simp_all)
    | fail "tactus: auto-tactic failed — add explicit proof block")
```

Built on two combinators in `TactusPrelude.lean`:

**`tactus_first | t1 | t2 | …`** — variant of `first` that wraps each alternative in `; done`. Without it, a tactic that succeeds while leaving unsolved subgoals (e.g., `simp_all` in some configurations) would commit early and block later alternatives. The closure contract lives at the combinator name rather than relying on every alternative to remember to append `; done`.

**`tactus_case_split closer`** (elaborator tactic, #58): tries each user-datatype-typed local in turn, running `closer` on each subgoal produced by `cases`. Commits the first split where `closer` closes ALL subgoals; restores state and tries the next candidate otherwise. Throws if no candidate works — composes with `tactus_first` for fallthrough. "User datatype" is gated on having a companion `.height` fn (which `to_lean_fn::height_fn_for_datatype` emits for every concrete non-generic datatype — see "Non-int decreases"). The gate filters out `Int` / `Nat` / `Bool` / `List` / etc., which have their own automation (omega / simp_all) and would explode the subgoal count if case-split.

`tactus_auto` uses `fail` as the final fallback, not `sorry`. This makes auto-tactic failures real errors. User-written `sorry` in tactic blocks remains a Lean warning for incremental development.

## Semantic details

### Nat subtraction

Lean's `Nat` has truncating subtraction: `5 - 7 = 0`. Verus's `nat` requires `b ≤ a` for `a - b`.

This works naturally: Verus's precondition becomes a Lean hypothesis. Lean's truncating subtraction agrees with mathematical subtraction when `b ≤ a`. No special handling needed.

### Integer division

VIR uses Euclidean division (`ArithOp::EuclideanDiv`). Lean's `Int.div` is T-division (rounds toward zero).

**Fix**: Use Mathlib's `Int.ediv` and `Int.emod` for `Int`. For `Nat`, Lean's `/` and `%` are already Euclidean.

### Bool vs Prop

VIR's `TypX::Bool` in spec context → Lean `Prop`. In exec context → Lean `Bool`. VIR tracks modes.

### Seq indexing

Verus's `s[i]` in spec mode is total — returns an unspecified value for out-of-bounds. Lean's `List.get` requires a bounds proof.

**Fix**: Opaque `Seq.index` (see prelude). Out-of-bounds is truly unspecified — no equalities provable between different out-of-bounds indices. Exactly matches Verus semantics.

### Seq as List

`Seq` is `abbrev`'d to `List`, meaning all `List` lemmas from Lean's standard library and Mathlib apply directly. Users can use `List.length_append`, `List.get_set`, etc. in their tactic proofs. Type errors show `List` (not `Seq`) which is transparent — the user knows `Seq = List`.

### Seq.subrange edge cases

`Seq.subrange s lo hi` = `(s.drop lo).take (hi - lo)`. When `lo > hi`, this gives `take 0 ... = []` (empty). When indices exceed length, `drop` and `take` truncate naturally. This matches Verus's edge-case semantics.

## vstd (Verus standard library) translation

Verus ships `vstd` — its verified standard library (`vstd::seq::Seq`, `vstd::set::Set`, `vstd::map::Map`, `vstd::arithmetic::*`, etc.). Every Verus program depends on it.

**Approach**: Translate `vstd` to a Lean library (`TactusStd.lean`) that lives in the managed Lake project alongside `TactusPrelude.lean`. This is a parallel workstream to the core tool.

### VIR path → Lean name mapping

VIR represents function calls with fully-qualified paths (`vstd::seq::Seq::<T>::push`). The Lean translation needs a lookup table mapping Verus built-in paths to their Lean equivalents:

| VIR Path | Lean Name |
|----------|-----------|
| `vstd::seq::Seq::empty` | `Seq.empty` |
| `vstd::seq::Seq::len` | `Seq.len` |
| `vstd::seq::Seq::index` | `Seq.index` |
| `vstd::seq::Seq::push` | `Seq.push` |
| `vstd::seq::Seq::subrange` | `Seq.subrange` |
| `vstd::seq::Seq::update` | `Seq.update` |
| `vstd::seq::Seq::add` | `(· ++ ·)` (List.append) |
| `vstd::seq::Seq::ext_equal` | `(· = ·)` |
| `vstd::set::Set::empty` | `(∅ : Set _)` |
| `vstd::set::Set::contains` | `(· ∈ ·)` |
| `vstd::set::Set::insert` | `Set.insert` |
| `vstd::set::Set::union` | `(· ∪ ·)` |
| `vstd::set::Set::intersect` | `(· ∩ ·)` |
| `vstd::map::Map::empty` | `(∅ : Finmap _)` |
| `vstd::map::Map::dom` | `Finmap.keys` |
| `vstd::map::Map::index` | `Finmap.lookup` |
| `vstd::pervasive::arbitrary` | `Classical.arbitrary` |
| ... | ... |

This table is built incrementally. Initially we support functions that DON'T use vstd. As vstd functions are translated, entries are added.

### vstd translation strategy

1. **Start with no vstd support** — functions using vstd types/methods get "unsupported vstd function" errors
2. **Translate core Seq/Set/Map operations** — the prelude already covers basics
3. **Translate vstd spec fns** — each becomes a Lean `def` in `TactusStd.lean`
4. **Translate vstd proof fns** — each becomes a Lean `theorem` (may need rewriting from assert-chain to tactic style)
5. **Arithmetic lemmas** (`vstd::arithmetic::*`) — many map directly to Mathlib lemmas

This is ongoing work that grows the supported surface area incrementally.

## Soundness and trust model

### Trusted computing base

The correctness of Tactus depends on:

1. **Lean's kernel** — small, well-audited, formally specified
2. **VIR → Lean translation** (`to_lean_expr.rs`, `to_lean_type.rs`, `to_lean_fn.rs`, `sst_to_lean.rs`) — **NEW, unaudited.** This is the primary soundness risk.
3. **Prelude axioms** — 4 axioms (see inventory above)
4. **Cross-crate axioms** — one per externally-verified theorem
5. **The proc macro** (`builtin_macros`) — modified to handle tactic blocks

### The translation correctness risk

If `to_lean_expr.rs` has a bug that translates VIR expression `P` to Lean expression `P'` where `P' ≠ P`, Lean verifies `P'` but the user thinks `P` is verified. This is **silent unsoundness**.

**Mitigations**:
- **Differential testing**: Run the same spec through both Verus (Z3) and Tactus (Lean). If both verify, confidence increases. If they disagree, investigate.
- **Translation unit tests**: For each VIR expression type, verify the Lean output against a known-correct reference.
- **Lean `#check` assertions**: Optionally emit `#check` statements that validate translated types match expectations.
- **Keep translations simple**: Prefer direct 1:1 mappings over clever optimizations. Boring code has fewer bugs.
- **The translation is auditable**: Generated Lean is readable text. Users can inspect it via `tactus translate file.rs`.

## Heartbeat annotations

Lean's deterministic timeout uses `maxHeartbeats`. Reuses Verus's rlimit annotation pattern:

```rust
#[verifier::heartbeats(1600000)]
proof fn expensive_lemma(...)
by {
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
}
```
→
```lean
set_option maxHeartbeats 1600000 in
theorem expensive_lemma ... := by
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
```

Default: 800000 heartbeats (configurable via `--heartbeats N`).

## Variable naming in Lean output

SST renames variables for disambiguation (`x` → `x@0`). This produces ugly goal states.

**Fix**: `sst_to_lean` uses original Rust variable names from VIR. Disambiguation suffixes added only for actual collisions (two `x` in nested scopes → `x` and `x'`). SST tracks original names via `VarIdentDisambiguate`.

## Cross-crate spec fn availability

When crate B depends on A, B's generated Lean needs A's spec fn definitions.

Each crate generates a `CrateDecls.lean` containing spec fn signatures and axiomatized ensures:

```lean
namespace crate_a.module
@[irreducible] noncomputable def double (x : Nat) : Nat := x + x
axiom lemma_double_pos : ∀ (x : Nat), x > 0 → double x > x
end crate_a.module
```

Downstream crates import declaration files. Axioms are sound because crate A verified the theorems.

Phase 1 is single-crate. Multi-crate is Phase 3.

## Type mapping (VIR/SST → Lean)

| VIR/SST Type | Lean Type | Notes |
|--------------|-----------|-------|
| `TypX::Int(IntRange::Int)` | `Int` | |
| `TypX::Int(IntRange::Nat)` | `Nat` | |
| `TypX::Int(IntRange::U(n))` | `Nat` | Overflow as separate obligation |
| `TypX::Int(IntRange::I(n))` | `Int` | Range as separate obligation |
| `TypX::Bool` | `Prop` (spec) / `Bool` (exec) | Context-dependent |
| `TypX::Tuple(types)` | `T₁ × T₂ × ...` | |
| `TypX::Lambda(params, ret)` | `T₁ → T₂ → ... → Ret` | |
| `TypX::Datatype(name, args)` | Lean structure/inductive | |
| `TypX::Boxed(t)` | `t` | Boxing erased in spec |
| `TypX::TypParam(name)` | `name` | Native polymorphism |

## Expression mapping (VIR/SST → Lean)

| VIR/SST Expr | Lean |
|--------------|------|
| `Const(Bool(b))` | `True` / `False` |
| `Const(Nat(n))` | `(n : Nat)` |
| `Var(x)` | `x` (original name) |
| `Binary(Eq(Spec), l, r)` | `l = r` |
| `Binary(Ne, l, r)` | `l ≠ r` |
| `Binary(Inequality(Le), l, r)` | `l ≤ r` |
| `Binary(Inequality(Lt), l, r)` | `l < r` |
| `Binary(Inequality(Ge), l, r)` | `l ≥ r` |
| `Binary(Inequality(Gt), l, r)` | `l > r` |
| `Binary(Arith(Add(_)), l, r)` | `l + r` |
| `Binary(Arith(Sub(_)), l, r)` | `l - r` |
| `Binary(Arith(Mul(_)), l, r)` | `l * r` |
| `Binary(Arith(EuclideanDiv(_)), l, r)` | `Int.ediv l r` (Int) / `l / r` (Nat) |
| `Binary(Arith(EuclideanMod(_)), l, r)` | `Int.emod l r` (Int) / `l % r` (Nat) |
| `Binary(And, l, r)` | `l ∧ r` |
| `Binary(Or, l, r)` | `l ∨ r` |
| `Binary(Implies, l, r)` | `l → r` |
| `Unary(Not, e)` | `¬ e` |
| `Quant(Forall, binders, body)` | `∀ (x : T), body` |
| `Quant(Exists, binders, body)` | `∃ (x : T), body` |
| `If(cond, then_, else_)` | `if cond then ... else ...` |
| `Call(fun, args)` | `fun arg₁ arg₂ ...` |
| `Bind(Let, binders, body)` | `let x := val; body` |
| `Choose(params, cond, body)` | `Classical.choose ...` |
| `BinaryOpr(ExtEq, l, r)` | `l = r` (see note) |

**Note on ExtEq**: Verus's `=~=` (extensional equality) maps to Lean's `=` because Lean 4's type theory includes function extensionality. For function types, `f = g ↔ ∀ x, f x = g x` is provable via `funext` (which is a theorem, not an axiom, in Lean 4 due to eta-expansion in definitional equality). So Lean's `=` on functions IS extensional equality — no separate encoding needed.

## VC generation for exec functions (Phase 2)

Phase 2 implements **weakest-precondition VC generation** fresh in `sst_to_lean`. This is textbook WP, implemented from scratch targeting Lean rather than extracted from `sst_to_air` (which is entangled with Poly encoding, triggers, fuel, and SMT expression flattening).

**Important**: VIR-SST is a cleaned-up AST, NOT a set of pre-generated VCs. The actual VC generation (turning imperative code into logical formulas) happens in the `sst_to_*` step. In Verus, that's `sst_to_air` (~3000 lines). In Tactus, it's `sst_to_lean` (comparable complexity). This is the largest single engineering effort in the project.

### WP rules

For a function with `requires P`, body `S`, `ensures Q(result)`, the obligation is: `P → wp(S, Q)`.

| Statement | Weakest precondition |
|-----------|---------------------|
| `let x = e; rest` | `let x := e; wp(rest, Q)` |
| `if c { s1 } else { s2 }` | `(c → wp(s1, Q)) ∧ (¬c → wp(s2, Q))` |
| `return e` | `Q(e)` |
| `while cond inv I dec D { body }` | Three theorems: I_init, I_maintain, I_use |
| `assert(P) by { tactics }` | `have h : P := by <tactics>; wp(rest, Q)` |
| `proof { have h : P := by t }` | `have h : P := by t; wp(rest, Q)` |
| `assume(P)` | `have h : P := sorry; wp(rest, Q)` (warning) |
| `x = e` (mutation) | SSA: `let x' := e; wp(rest[x→x'], Q)` |

Additional cases handled in Phase 2 but not listed for brevity: pattern matching (case splits), closures, borrow semantics (mutable references as functional updates), break/continue/early return (control flow), Ghost/Tracked parameter unwrapping.

### Loop obligations

```
while cond invariant I_1, I_2, ... decreases D { body }
```

Per-obligation emission (D, 2026-04-26) generates the following separate Lean theorems:

1. **Init**: one theorem per invariant — `<outer ctx> → I_i` for each `i`. The invariant must hold at loop entry.
2. **Maintain**: walk `body` in maintain ctx (`∀ mod_vars + bounds + I_1 ∧ ... as hyps + cond as hyp + _tactus_d_old := D` let). The body's `Done(I_1 ∧ ... ∧ I_n ∧ D < d_old)` terminator splits per-conjunct via `emit_done_or_split` — yielding one theorem per invariant (LoopInvariant kind) plus one for the decrease (LoopDecrease kind). User-written assertions inside the body emit their own theorems too.
3. **Use**: walk `after` in use ctx (`∀ mod_vars + bounds + I_1 ∧ ... as hyps + ¬cond as hyp`). Produces theorems for the post-loop continuation (Postcondition theorems for the fn's ensures, plus any obligations in the post-loop code).

Each theorem auto-checked by `tactus_auto`. Failure points the user at `_tactus_loop_invariant_<fn>_at_<loc>_<id>` / `_tactus_loop_decrease_<fn>_at_<loc>_<id>` / `_tactus_postcondition_<fn>_at_<loc>_<id>` etc. with the matching `(loop invariant)` / `(loop decrease)` / `(postcondition)` kind label.

### Overflow obligations

Each arithmetic op on fixed-width types generates:
```lean
theorem overflow_check_line_N ... : 0 ≤ result ∧ result < 2^bits := by tactus_auto
```

**Current implementation status**: u8/u16/…/u128 render as Lean `Int` with both-sided refinement; i8/i16/…/i128 also render as `Int`. `HasType(e, U(n))` emits `0 ≤ e ∧ e < 2^n`; `HasType(e, I(n))` emits `-2^(n-1) ≤ e ∧ e < 2^(n-1)`. Each fixed-width param picks up a `(h_<name>_bound : …)` hypothesis via both `exec_fn_theorem_to_ast` (exec fns) and `fn_binders` (proof fns). `IntegerTypeBound(kind, _)` (i.e., `u8::MAX`, `i32::MIN`, etc.) evaluates to a decimal literal at codegen when the bit-width argument is a `Constant::Int`; `ArchWordBits` emits a reference to the prelude axiom.

**Why u-types render as `Int` rather than `Nat`.** Lean's `Nat` has truncating subtraction (`0 - 1 = 0`). If we rendered u-types as `Nat`, the overflow check `HasType(x - y, U(n))` would reduce to `0 ≤ x - y ∧ x - y < 2^n` — and the left half is trivially true for any `Nat`, so unguarded u8 subtraction would silently verify despite underflowing in Rust. Rendering as `Int` with an explicit `0 ≤ x` lower-bound hypothesis makes subtraction give the true mathematical value, so the refinement check can catch underflow. Mul and add on u-types worked either way (Nat doesn't truncate upward); only sub was at risk.

### `usize`/`isize` bounds — emitted but rarely auto-discharged

`type_bound_predicate` emits `0 ≤ e ∧ e < usize_hi` for `USize` and `-isize_hi ≤ e ∧ e < isize_hi` for `ISize`, where `usize_hi` / `isize_hi` are prelude `Int` constants defined as `(2 : Int) ^ arch_word_bits` and `(2 : Int) ^ (arch_word_bits - 1)`. Fn params and `HasType` sites both pick up the refinement.

`arch_word_bits` itself is an axiom (`arch_word_bits : Nat`) with a validity disjunction (`arch_word_bits_valid : arch_word_bits = 32 ∨ arch_word_bits = 64`). The concrete value is left abstract so proofs hold for any supported target; the disjunction is there for users who need to case-split.

**Rendering: `USize` → Lean `Nat`, `ISize` → Lean `Int`**. USize *wants* to be `Int` (same argument as for u-types — `Int` semantics catch subtraction underflow), but Verus elides `as nat` casts from `usize` in spec contexts, so const-generic bodies like `N as nat` render as just `N`. If `USize` rendered as `Int`, those const-generic defs would have body type `Int` and declared return type `Nat` — a mismatch that breaks the translation (`test_const_generic`). ISize has no such constraint and does render as `Int`.

**Trade-off: USize subtraction truncates silently.** Because `USize` → `Nat`, `let r: usize = x - y;` for usize `x`, `y` truncates at zero if `y > x`. The `0 ≤` side of the `usize_hi` refinement is then trivially true and the underflow silently passes. Parallel to the u8-subtraction soundness hole before the u8 → Int change. Proper fix is the same: find a way to make USize render as Int without breaking const-generics. Open.

**tactus_auto can't discharge `< usize_hi` automatically.** `omega` doesn't reason about `2 ^ arch_word_bits` for unknown `arch_word_bits`. `tactus_auto`'s current toolbox (`rfl | decide | omega | simp_all`) can't either. Non-trivial usize arithmetic needs user-written `proof { … }` blocks that case-split `arch_word_bits_valid` and invoke `Nat.pow_le_pow_right` / `Int.pow`-style lemmas — a significant ergonomics burden. A custom `tactus_usize_bound` tactic that automates this is an obvious future addition; until then, the bound is *present* for soundness but not discharged for usability.

### Known codegen-complexity trade-offs

`Wp::Branch`'s two sub-trees each hold their own continuation (`after` cloned into both). N sequential ifs at the same level produce 2^N copies of the innermost continuation in the Wp tree. For realistic exec fn bodies (few-level nesting) this is fine; for pathological cases it could bloat codegen time and the generated `.lean` file.

Investigated: introducing a `let _goal_k := <rest_goal>` binding at each if and having both branches refer to `_goal_k` preserves logical equivalence with linear size. **Rejected** as a codegen fix because Lean's `simp_all` / `omega` zeta-reduces through the let, so the tactic-level work still duplicates — the generated `.lean` file gets smaller but the proof search cost stays exponential. The proper fix would be a custom tactic that shares sub-proofs structurally (reuse at the tactic level, not the expression level). Not worth doing until a real program hits the wall.

**Why `Box<Wp<'a>>` and not `Rc` / arena?** Each `Wp` node is heap-allocated via `Box` — one allocation per node, minimal overhead. `Rc<Wp<'a>>` would give structural sharing (the DAG shape on `Branch`) but adds refcount traffic on lowering and doesn't help the tactic-level duplication noted above. An arena (`typed-arena` / `bumpalo` / custom `Vec<Wp>`+indices) would make `after: &'arena Wp<'a>` possible with `Copy`-able references and zero allocations beyond the arena's bump — but at the cost of threading an additional lifetime through every builder signature (`WpCtx<'a>` gains `'arena`, every function taking `&WpCtx` becomes `WpCtx<'arena, 'a>`, etc.). Verification is I/O-bound on Lean anyway; `Box` is fine until a profile says otherwise.

`lift_if_value`'s closure (`&dyn Fn(LExpr) -> LExpr`) also allocates: each recursive call clones the captured body-ast when invoking `emit_leaf`. Each invocation is O(expression size), so the full cost is O(branches × size). Same "fine for realistic code, not worth optimising yet" story — a `FnOnce`-based rewrite or an iterative version would reduce cloning if this ever shows up in profiles.

### `StmX::Call` — landed (slice 7, with recursion)

Exec fns can call other exec/proof/spec fns. The WP rule for
`let y = foo(a1, a2)`, lowered by `walk_call` in
`sst_to_lean.rs`:

```
requires_conj[p1 := a1, p2 := a2]
∧ ∀ (ret : RetT), h_ret_bound(ret) →
    ensures_conj_using_ret[p1 := a1, p2 := a2] →
    let y := ret; walk_obligations(after)
```

Param substitution is done via **Lean-AST substitution**
(`lean_ast::substitute`, capture-avoiding with a lazy per-scope
capture check) rather than emitting `let p := arg; body` wrappers.
Direct substitution avoids name shadowing when the caller and
callee share a param name — the earlier let-wrapping produced
`let n := n - 1; ...; n` at self-recursion sites, which defeated
omega's let-handling and forced a `(simp_all; omega)` rung on
`tactus_auto`. That rung is gone; generated Lean now reads
`tmp_ < decrease_init0` directly.

The callee does NOT need its own Lean definition; we inline its
requires/ensures from its `FunctionX` via `vir_expr_to_ast` at each
call site. `WpCtx::new` builds the `Fun → &FunctionX` lookup (and
the type map for loop modified-var quantification and the fn's
ret_name + ensures_goal for Return to write to).

`build_wp_call` (in `sst_to_lean.rs`) validates the call shape and
produces the `Wp::Call` node with the post-call continuation as its
`after: Box<Wp<'a>>` sub-tree. `walk_call` emits the Lean.

**Termination via Verus's own `CheckDecreaseHeight`.** For any
recursive call (direct or mutual across an SCC), Verus's
`recursion::check_recursive_function` pass inserts a
`StmX::Assert(InternalFun::CheckDecreaseHeight)` right before the
`StmX::Call`. Our walk sees it as a plain `Wp::Assert`;
`sst_exp_to_ast_checked` lowers `CheckDecreaseHeight` to the int-
typed termination obligation:

```
(0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)
```

where `cur` is the decrease expression with call-site args
substituted, `prev` is the decrease-at-entry for the current fn,
and `otherwise` is the lexicographic-tail marker (`False` for
single-expression decreases). See `to_lean_sst_expr.rs`'s
`CheckDecreaseHeight` arm for the lowering; `render_checked_decrease_arg`
handles the Bind(Let) param-substitution wrapper Verus puts on
`cur`.

Mutual recursion across an SCC works by construction — Verus's
recursion pass covers all cross-fn calls in the cycle the same way.

**Restrictions (rejected by `build_wp_call`):**

* **Trait-method calls** — `resolved_method: Some(_)` rejected.
* **Trait-default-impl calls** — `is_trait_default: Some(_)` rejected.
* **Generic calls** (`typ_args` non-empty) — rejected.
* **`&mut` args** — `contains_loc` peels transparent wrappers
  (Box/Unbox/CoerceMode/Trigger) and rejects any `ExpX::Loc`.
* **Split-assertion calls** (`split: Some(_)`) — rejected.
* **Cross-crate callees** — rejected (fn_map is single-crate).
* **Non-int decreases** — datatype-typed decreases rejected because
  we don't encode a Lean `height` function yet. Int decreases work
  via the transparent-identity `height` for ints (see prelude
  axioms in `vir/src/prelude.rs:1030-1037`).

### `_tactus_d_old` aliasing across nested loops

`sst_to_lean::walk_loop` emits `let _tactus_d_old := D; …` inside every loop's maintain clause to capture the decrease measure pre-body. The name is literal, not gensym'd, so nested loops' `let _tactus_d_old` bindings shadow each other in Lean.

This is correct for the current architecture: the inner loop's shadow is confined to the inner's maintain conjunct, and the outer's `_tactus_d_old` reference lives in the outer's maintain conjunct (a sibling, not a descendant), so they never clash in scope. A gensym'd `_tactus_d_old_<loop_id>` would make the independence syntactically obvious but doesn't change semantics. Worth threading a counter through `walk_loop` if we ever refactor loops into a structure where scoping IS ambiguous — until then, the literal name is fine and keeps the generated Lean readable.

### Known deferrals, rejected cases, and untested edges

A flat catalogue of things that don't work yet, organized by where in the pipeline they're rejected or where the gap lives. If a gap has its own detailed section elsewhere in this doc, it's cross-referenced rather than duplicated.

#### Statement-level forms rejected by `build_wp`

Each one returns `Err("… not yet supported")`; users get a clean rejection instead of silent pass.

* **`StmX::BreakOrContinue`** — `break` / `continue` inside loops. Blocks `while`-with-exit patterns. Enabling this also requires relaxing `cond: Some` (loops that break compile to `cond: None`) and accepting `invariant_except_break` invariants (at-entry but not at-exit).
* **`StmX::AssertBitVector`** — `assert by(bit_vector)`. Bitvector reasoning backend.
* **`StmX::AssertQuery`** — `assert by(…)` with specific tactics / queries. Would need to translate the `AssertQueryMode` into a Lean tactic choice.
* **`StmX::DeadEnd`** — markers Verus uses for unreachable code. Usually harmless to skip, but we reject rather than silently strip in case a future pipeline relies on them.
* **`StmX::OpenInvariant`** — atomic invariant opening for concurrent verification. Out of scope until concurrency support lands.
* **`StmX::ClosureInner`** — exec closure bodies. Depends on `ExpX::CallLambda` support.

#### Expression-level forms rejected by `sst_exp_to_ast_checked`

`sst_exp_to_ast_checked` is the primary validator+renderer for SST expressions; `check_exp` is a thin wrapper (`.map(|_| ())`). Single case analysis for both validation and rendering.

* **`UnaryOp` variants beyond `Not` / `Clip` / `CoerceMode` / `Trigger`** — the spec-fn path (`to_lean_expr`) handles more (BitNot, IntToReal, etc.) but the SST path on exec bodies is conservative; add as needed.
* **`BinaryOp::HeightCompare { … }`** — VIR's termination-height comparison (the fn-level wrapper; `CheckDecreaseHeight` below is the per-call-site SST form we DO lower).
* **`BinaryOp::Index(_, _)`** — array / slice indexing with bounds check.
* **`BinaryOp::StrGetChar`** — string character lookup.
* **`BinaryOp::IeeeFloat(_)`** — IEEE float comparisons. Verus doesn't support `f32`/`f64` at all; this branch exists for completeness.
* **`ExpX::Ctor(..)`** — datatype constructors in exec fns. Blocks any exec code that constructs enum/struct values. Regression test: `test_exec_ctor_rejected`.
* **`ExpX::CallLambda(..)`** — closure calls. Blocks fns that invoke stored closures.
* **`ExpX::ArrayLiteral(_)`** — `[a, b, c]` literals. Verus rejects these upstream when slice indexing isn't wired, so the Err arm is unreached in practice.
* **`ExpX::Old(..)`** — `old(x)` (pre-state). Relevant for `ensures` that compare post-state to pre-state.
* **`ExpX::Interp(_)`** — only appears inside Verus's interpreter; an internal-bug rejection rather than a feature gap.
* **`ExpX::FuelConst(_)`** — fuel-reveal constants. Blocks `reveal_with_fuel` in exec fns.
* **`CallFun::InternalFun(_)` other than `CheckDecreaseHeight`** — `CheckDecreaseHeight` is lowered (for int-typed decreases); other `InternalFun` variants rejected.
* **Non-int `CheckDecreaseHeight`** — datatype-typed decreases need a Lean `height` function encoding. Reject at validation time rather than emit an unsound obligation.

#### Lossy accepted forms (renders but drops info)

Forms we accept and render, but with semantic information dropped. None of these cause unsoundness today — the dropped info is either irrelevant to VC validity or is auxiliary metadata. Listing here so a future behaviour change (e.g., a tactic that *does* use the dropped info) has a bug site to start from.

* **`ExpX::NullaryOpr(_)` renders as `True`.** All nullary operators (e.g., `NoInferSpecForLoopIter`) collapse to `True`. Loses the operator-specific meaning. Safe today because VCs don't depend on it.
* **`ExpX::WithTriggers(_, inner)` drops the triggers.** We render the inner expression as-is; the attached trigger annotations (used by Z3's quantifier instantiation in Verus's pipeline) are ignored. Lean's tactics don't use them, so no downstream effect.
* **`BndX::Quant(_, binders, triggers, _)` drops triggers + the trailing param.** Same rationale. Universally-quantified spec clauses render their body correctly; the triggers and whatever the fourth field is get dropped silently.
* **`ExpX::VarAt(ident, at_label)` treats all VarAt occurrences identically to `Var`.** The `at_label` information (which distinguishes pre-state from post-state references in old-style ensures) is discarded. Acceptable because `ExpX::Old(..)` is already rejected upstream, so at-labels shouldn't arrive with meaning attached. If a future VIR change routes at-state expressions through `VarAt` without going through `Old`, we'd silently conflate them.
* **`BinaryOp::Xor`** — renders as `App(Var("xor"), [l, r])`. Relies on Lean's `xor` being defined or imported; no test exercises it in an exec-fn body.
* **`ExpX::Bind(BndX::Choose, ...)` → `Classical.epsilon (fun ... => cond ∧ body)`.** Untested directly; `Classical.epsilon` is total but its behaviour on unsatisfiable `cond` is unspecified. Exec-fn tests don't exercise the Choose shape.
* **`lift_if_value` only handles single-binder `Bind(Let)`.** Multi-binder lets (`let (a, b) = expr; …`) pass through without peeling. An if-expression buried inside a multi-binder let won't lift to goal level — omega would then see it as a value-position if and fail.

#### Loop-shape restrictions (rejected by `build_wp_loop`)

* **`loop_isolation: false`** — non-isolated loops (body sees outer context directly rather than via the invariant).
* **Non-empty condition setup block** — `while` conditions that desugar into a small statement prelude (complex expressions that aren't pure).
* **Lexicographic `decreases`** — multi-expression measures (`decreases (a, b)`). Only single-expression is accepted.
* **`invariant_except_break` / `ensures` loop invariants** — any invariant with `at_entry: false` or `at_exit: false`. Only "true at entry AND exit" variants accepted. User's `invariant x <= n` syntax produces at_entry = at_exit = true by default, so common cases work; uncommon desugarings (e.g., from `while let Some(x) = it.next() { … }`) may hit this.
* **Labeled `break` / `continue`** — `break 'outer;` / `continue 'outer;` rejected in `build_wp`. Unlabeled break/continue in `while` loops works via #57. Pinned by `test_exec_loop_labeled_break_rejected`.

Accepted via #57: **`cond: None`** loops (the form Verus produces when lowering `while c { … break; … }` or `loop { … break; … }`). Maintain/use clauses drop the cond-gate in this case; break/continue in the body thread through `WpLoopCtx`.

#### Soundness trade-offs accepted (not pure bugs, but worth knowing)

* **Usize subtraction truncates silently** — see the usize/isize section above.
* **Usize arithmetic rarely verifies automatically** — bounds are emitted but `tactus_auto` can't discharge symbolic `< usize_hi`; users need custom `proof { … }` with `arch_word_bits_valid` case-split.
* **Char bound admits surrogates** — `c < 0x110000` covers U+0000..U+10FFFF but includes the UTF-16 surrogate range U+D800..U+DFFF. Verus / Rust's `char` also don't distinguish, so our bound matches their semantics. No downstream soundness impact within the same system.
* **`Wp` clone cost is exponential in nested if-branch depth** — both branches of `Wp::Branch` clone the outer `after` continuation. Same behaviour as the prior `BodyItem` shape; the DSL refactor didn't fix this. Fine for realistic code.
* **`_tactus_d_old` shadows in nested loops** — relies on scope to disambiguate; documented in its own section.
* **`substitute`'s capture check panics rather than alpha-renames** — when a real capture is detected, we panic with a clear message instead of rewriting the binder. Alpha-renaming is the proper fix for when that fires; no test hits it today because callee specs are simple arithmetic.
* **`Classical.propDecidable` opens all Props.** Added to `TactusPrelude.lean` so accessor-derived Props (from `datatype_to_cmds`'s synthesized `Type.isVariant`) decide in `if <prop> then … else …` contexts. Side effect: `decide` can't reduce through classical-only Props — `decide` loses some reducibility relative to a prelude without this. `tactus_auto` uses `omega` / `simp_all`, not `decide` directly, so no current impact. A future tactic relying on `decide` to compute through Prop formulas would need to be aware.
* **Tactus tactic-text prepending runs at theorem level, not locally.** When a user writes `assert(P) by { tac }` or `proof { have h := by tac }` inside a loop body (or any nested construct), the `have` is prepended to the THEOREM's tactic at theorem-start — before any `intro` of modified-var quantifiers. Variable references in the tactic resolve to the OUTER scope (fn param, not loop-local). For simple cases (e.g., `assert(x < 256) by { omega }` where `x` is a u8 fn param and the tactic only uses fn-level bounds) this works. For tactics that would need a loop invariant as a hypothesis, the invariant isn't in scope at theorem-tactic prefix. Known design limitation; a per-loop-scoped `have` would require per-loop tactic emission, which we don't have. Not tested end-to-end with tactics that depend on loop-local state.
* **Proof-block goal-modifying tactics affect the outer goal.** `proof { simp_all }` simplifies the entire theorem goal, not just a local sub-proof. Users coming from Verus's self-contained proof blocks may be surprised. Pinned by `test_exec_proof_block_goal_modifying_tactic`; the alternative (wrapping in a local `have _ : True := by <tac>`) breaks the common `have h : P := by tac` propagation case — which is the primary reason users write proof blocks.
* **`tactus_case_split` tries each user-datatype local in turn.** Takes a `closer` tactic argument and commits the first split where the closer closes ALL subgoals; restores state and tries the next candidate otherwise. Means a fn with multiple datatype locals — e.g., `(a: Foo, b: Bar)` — works regardless of which is the right scrutinee. Cost is O(n_candidates × closer_cost), bounded by the locals in scope. The `.height`-existence gate filters out `Int`/`Nat`/etc. so we don't case-split on primitives. Pinned by `test_exec_match_enum_with_int_args` (mixed enum + int locals).

#### User-facing features not tested (or possibly broken)

* **`proof { … }` blocks inside exec fns — LANDED (#49).** Covered by `test_exec_proof_block_user_tactic`. Caveats: tactic runs at theorem level (see Soundness trade-offs); goal-modifying tactics affect the whole goal.
* **`assert(P) by { tactics }` — LANDED (#50).** Covered by `test_exec_assert_by_user_tactic`.
* **`assume(P)` warnings** — DESIGN.md promises a "unproved assumption" warning. Not wired; `StmX::Assume` emits the hypothesis silently.
* **Return in the `else` branch of an if** (where `then` falls through) — inverse of `test_exec_early_return`. Untested.
* **Return inside a loop body** — ✅ covered by `test_exec_return_inside_loop` and `test_exec_return_inside_loop_with_break`. Pins the Wp DSL's fn-exit semantics (Return writes `ctx.ensures_goal` regardless of nesting or `loop_ctx`).
* **Loops modifying multiple variables** — `quantify_mod_vars` handles arbitrary-arity modified sets, but every loop test modifies at most two vars.
* **Nested if where each branch contains a different loop** — combinatorial coverage gap.
* **Loop body ending in an early return** — ✅ covered by `test_exec_return_inside_loop_with_break`.
* **Bit-width coverage** — only `u8`, `u32`, `i8` tested end-to-end. `u16` / `u64` / `u128` / `i16` / `i32` / `i64` / `i128` go through the same codegen path but lack regression tests.
* **Direct unit tests for `walk_loop` and `walk_call`** — the two largest walker functions are only exercised via e2e tests. Constructing the synthetic Wp + FunctionX + arg list + ObligationEmitter to unit-test them is involved; we cover cheaper variants (`Done`/`Let`/`Assert`/`Assume`/`Branch`) directly and trust e2e for the rest.
* **Name collision: callee's ret name vs caller-scope names** — `walk_call` emits `∀ <ret_name_cal : T>, …` using `sanitize(callee.ret.name.0)`. If the caller has a local variable with the same sanitized name, Lean's ∀ shadows it inside the scope — semantically fine (the ∀ binding is what Verus intends) but visually confusing in the generated Lean. No test pins a collision scenario.
* **Zero-arg callee spec referencing the dummy param** — for a fn with no user params, Verus injects a `no%param` dummy; our `walk_call` substitutes `{no_param: Const(0)}`. If the callee's `require` / `ensure` ever syntactically references this dummy (they shouldn't, by Verus convention), we'd inline `0` for it — semantically correct but relies on the convention holding.
* **Non-constant `IntegerTypeBound` bit width** — `const_u32_from_sst` / `_vir` extract the bit width via `.expect("…non-constant bit width…")`. Verus's `IntegerTypeBound(kind, bits)` always has `bits` as a literal for concrete int types, but a const-generic context (`<const N: u32>` as bit width) would panic at codegen. Untested.
* **Empty `proof { }` / `assert(P) by { }` brace bodies** — user-written empty tactic blocks inside tactus_auto fns. FileLoader sanitizes to empty, we detect via HIR-body-empty, read tactic_text = whitespace. Emitting `have h : P := by` with empty body after would fail Lean parsing. Not common but plausible (e.g., user writes `proof { }` as a stub). Untested.
* **Enum accessor fns for types with non-Inhabited field types** — `datatype_to_cmds` emits accessor bodies using `default` for unreachable match arms (other variants). For field types lacking `[Inhabited α]` (user-defined types without a derived instance), Lean elaboration fails. The `emit_accessors: bool` flag skips accessor synthesis in the proof-fn entry path — spec fns reference such types routinely and use native Lean match, not accessors. For an exec fn matching on an enum with non-Inhabited-field'd variants, we'd emit accessors that fail to elaborate. All current test enums have Int/Nat/Bool fields (auto-Inhabited). Untested for user-defined types.
* **Generic calls don't verify trait-bound / where-clause constraints** — `#53`'s substitution accepts any `typ_args` without checking callee-side bounds. For callees whose body only uses type-level references to the type parameter, this is fine. For callees that rely on bounds for operations (e.g., `T: Ord` enabling `<` on T values), the callee's spec might assume properties we can't guarantee for the instantiation. Current generic exec fn tests are identity-like; no bound-dependent exec callees exercised.
* **`assert forall|v| P by { tac }` via Tactus path** — the #50 / #49 infrastructure goes through `ExprX::AssertBy` which can carry `vars`. Our Tactus short-circuit handles `vars = []` (plain assert-by and proof blocks). The forall variant with non-empty `vars` isn't exercised for Tactus (tactic_span still populated at rust_to_vir, but the SST emission doesn't account for the binders). Untested.
* **Tactus tactic referencing loop-local variables** — see the "tactic-text prepending runs at theorem level" soundness trade-off. A user's `assert(inv) by { exact h_loop_inv }` inside a loop body wouldn't find `h_loop_inv` at theorem-tactic prefix. Untested directly.

#### Tactic / automation limitations

* **`tactus_auto`'s toolbox is `rfl | decide | omega | simp_all`.** Exec-fn obligations needing `nlinarith`, `ring`, `polyrith`, `aesop`, `positivity`, etc. fall through to the `fail` branch. Proof fns *can* use any Mathlib tactic in their `by { … }` block; exec fns can't.
* **No per-fn tactic override.** A user who wants `ring` for a specific exec fn has no way to request it. A `#[verifier::tactus_tactic("ring")]` attribute plumbed into `FunctionAttrs` would fix it.
* **Mathlib auto-tactics unused for exec fns.** Exec-fn `tactus_auto` is intentionally minimal to keep verification predictable; extending it is a design call, not a straight addition.

#### Architecture debts (working-but-not-ideal)

* **Two parallel expression renderers — shared leaves extracted, deeper unification rejected.** `to_lean_expr.rs` (~495 lines, proof fn / callee spec inlining) and `to_lean_sst_expr.rs` (~565 lines, exec fn bodies) render structurally different trees: VIR-AST's `Block`/`Match`/`Ctor`/`PatternX`/`PlaceX` don't cross to SST; SST's `CheckDecreaseHeight`/`CallFun::InternalFun`/flattened statement sequence don't cross to VIR-AST. The shared rules — op tables, constant rendering, `Clip` coercion direction, binder construction — live in `expr_shared.rs` so divergence is a compile error. Full unification (trait over source-expression type, or routing callee specs through SST) was investigated and rejected; see the dedicated § "Two parallel expression renderers" above for the analysis.
* **Two-pass over loop bodies.** `build_wp_loop` calls both `collect_modifications` and `build_wp` on the body; fusing would save a pass but entangles modifications with WP construction. Documented; left alone.
* **Sanity-check allowlist maintained by hand.** Adding a prelude def (like `usize_hi`) requires remembering to update `sanity.rs`. No automated sync; compiler error on mismatch (panic in debug builds).
* **Expected VIR variant list for coverage is hand-maintained.** `tactus_coverage.rs` lists variants we expect to see. Macro-deriving from the enum would need Verus-upstream `strum` derives — not feasible without vendoring changes.
* **`_tactus_d_old` not gensym'd** — see its dedicated section.
* **`OblCtx::with_frame` clones the whole `frames` Vec per call** — O(N²) memory across deeply-nested recursion (asserts inside branches inside loops). Realistic exec fns don't go deep enough for this to matter; switching to `Rc<im::Vector<_>>` (structural sharing) would fix it without changing the API. Documented inline at the function site.
* **`substitute` boilerplate.** ~130 lines of per-variant dispatch across `substitute_impl` / `collect_free_vars`. Adding an `ExprNode` variant means editing three places (plus `lean_pp`). A `walk_children` helper or proc-macro would collapse it to ~30 lines — not worth doing yet, worth flagging.
* **No shape-drift test for `CheckDecreaseHeight` Assert-before-Call ordering.** We have a test for the `cur` arg's Bind(Let) shape (`full_check_decrease_height_shape_pinned`) but not for the pass-ordering invariant ("Assert is inserted before the Call in the SST statement sequence"). A drift here would produce recursive fns that verify without termination checks. Worth adding: construct a self-recursive SST fragment and assert the first `Wp::Assert` precedes the `Wp::Call` in the built Wp tree.
* **No test that `WpCtx::new` rejects an Err-form req/ensure cleanly.** We have `test_exec_ctor_rejected` for body-path Ctor, but no direct test that a `requires Ctor(...)` clause produces the WpCtx::new Err path (vs. panicking or passing through). Low risk — the validation logic is shared with the body — but a regression guard would be cheap.
* **`lift_if_value` single-binder Bind(Let) restriction.** Multi-binder lets (`let (a, b) = …; …`) pass through without peeling. If a user writes `let (a, b) = foo(); if x { … } else { … }` the if won't be lifted to goal level — currently fine because such let-patterns aren't common in our tests, but the restriction is implicit.
* **No direct test of `simplified_krate()` None branch.** Unreachable by design (verify_crate_inner populates it before verify_bucket runs). If a future code path hits the unreachable branch, users see our "pipeline ordering bug" error instead of a panic — but we don't exercise the error path.

#### Track B tightening roadmap (in-scope, not yet landed)

Distinct from the "Phase-3 non-goals" list below: these are items that
*should* be part of Track B's tight feature set but currently aren't
wired. Ordered by unlock-per-day-of-effort. Each is a bounded piece of
work, sized in rough days for a focused session; the top-tier items
are what separate "demo-quality Track B" from "usable on realistic
exec fns."

##### Tier 1 — immediate wins (1–2 days each)

* **`proof { ... }` blocks inside exec fns — LANDED.** Built on
  #50's infrastructure: `TactusSpan::kind` carries which surface
  form produced the AssertBy (`AssertBy` vs `ProofBlock`);
  `AssertQueryMode::Tactus` carries the same kind through to SST;
  `Wp::AssertByTactus::cond` is `Option<&Exp>` (None = proof block
  — emit tactic raw, no `have h : P :=` wrap).
  `rust_to_vir_expr` synthesises an AssertBy-wrapped-in-Ghost for
  user-written `proof { }` blocks in tactus_auto fns,
  discriminating from auto-wrapped blocks (from Verus's
  `auto_proof_block` pass on every `assert(…);`) by HIR-body
  emptiness. sst_to_lean emits the tactic text raw — the user's
  own `have` statements propagate to theorem level for subsequent
  automation. Regressions: `test_exec_proof_block_user_tactic`,
  `test_exec_auto_proof_block_not_tactus` (shape-drift guard for
  the HIR-body-empty discriminator).

  **Caveat — goal-modifying tactics in proof blocks.** Since the
  tactic is emitted as a raw theorem-level prefix, goal-modifying
  tactics like `unfold foo; simp_all` affect the **entire**
  theorem goal, not just a local sub-proof. Users may expect the
  Verus-style "self-contained proof block" semantics and be
  surprised. Isolating the effect (via `have _ : True := by
  <tac>`) would break the common `have h : P := by tac` case,
  where we *want* the hypothesis to propagate. Accepted trade-off
  for now; pinned by `test_exec_proof_block_goal_modifying_tactic`.

* **`assert(P) by { tactics }` with user tactic bodies — LANDED.**
  `AssertQueryMode` grew a `Tactus { tactic_span, kind: TactusKind }`
  variant (moving the enum from `Copy` to `Clone` — ~5 mechanical
  sites). `rust_to_vir` captures the `{ … }` byte range onto
  `ExprX::AssertBy::tactus: Option<TactusSpan>` (a struct holding
  file path + byte range + `TactusKind`), only populated inside
  `tactus_auto` fns. `ast_to_sst` short-circuits that shape to
  `StmX::AssertQuery` with Tactus mode, bypassing the DeadEnd
  desugaring. `sst_to_lean`'s `build_wp` reads the verbatim Lean
  tactic text from the source file via the span and produces a
  `Wp::AssertByTactus { cond: Some(P), tactic_text }` node.
  Post-D (2026-04-26), `walk_assert_by_tactus` emits a single
  obligation theorem for `P` with the user's tactic as the closer
  (rather than `tactus_auto`); `P` then enters body's `OblCtx` as
  a hypothesis for subsequent obligations. Regression:
  `test_exec_assert_by_user_tactic`. `sst_to_air` short-circuits
  Tactus mode to a no-op for secondary queries (recommends-check
  etc. still flow through sst_to_air for tactus_auto fns, but
  the obligation is Lean's job).

* **Source mapping for exec-fn errors — LANDED (#51).**
  `walk_obligations` and friends wrap obligation expressions in
  `ExprNode::SpanMark { rust_loc, kind, inner }`. `rust_loc`
  is the pre-resolved `path:line:col` from the SST `Span`
  (populated by `rust_verify::spans::to_air_span` via
  `SourceMap.lookup_char_pos`). `kind: AssertKind` carries
  the obligation's semantic class — `Plain`, `LoopInvariant`,
  `LoopDecrease`, `LoopCondition`, `BranchCondition`,
  `CallPrecondition`, or `Termination`.

  The pp emits `/- @rust:LOC -/` regular block comments before
  the inner expression (visible debug aid in the generated
  `.lean` file) AND records `SpanMarkLandmark { line, loc, kind
  }` in `Landmarks::span_marks` directly during emission. On
  Lean error, `format_error` calls `find_span_mark(pos.line)`
  to surface the closest preceding landmark as
  `at <path>:L:C (<kind label>):` in the error body.

  Coverage: `Wp::Assert` (Plain or Termination by detection),
  `Wp::Branch.cond`, `Wp::Loop.invs` / `decrease` / `cond`,
  `Wp::Call` (call-site requires_conj). Loop body / call
  continuation use the inner `Wp::Assert` marks recursively.

  **Known imperfection: position-of-mark vs position-of-failure.**
  Pre-D (i.e., before 2026-04-26): Lean's diagnostic `pos.line`
  reported the failing *tactic* invocation line (typically the
  line of `tactus_peel; all_goals tactus_auto` near the end of
  one mega-theorem per fn), not the line of the failing
  obligation expression in the goal tree. `find_span_mark`
  returned the closest preceding landmark to that tactic line —
  usually the LAST mark in the theorem. When the failing
  obligation was also the last mark, the reported `loc` and
  `kind` were exactly right. When the failing obligation was
  earlier in the goal tree (e.g., a Termination check on a
  recursive fn whose call also has a precondition mark
  afterward), `find_span_mark` returned a mark that was
  structurally adjacent but not the actual one — the kind
  label was one off.

  **Fixed by D (2026-04-26).** Per-obligation theorem emission
  isolates each obligation in its own theorem with its own
  `:= by` block; the closest preceding mark to a failing
  tactic line is now structurally guaranteed to be the
  obligation mark for that theorem. AssertKind labels are
  exactly right by construction. See HANDOFF.md session entry.

##### Tier 2 — realistic-code unblockers (2–4 days each)

* **`ExpX::Ctor` + pattern matching in exec fns — partially landed.**
  * **Struct Ctor + field access: works end-to-end.** `ExpX::Ctor`
    for `Dt::Path` with a sole variant renders as `TypeName.mk arg₁
    arg₂ …` via the shared `ctor_node` helper in `expr_shared`.
    Field access via `structure`-auto-derived accessors. Test:
    `test_exec_ctor_struct`.
  * **Enum ctor: works.** `ExpX::Ctor` for multi-variant `Dt::Path`
    renders as `TypeName.Variant arg₁ arg₂ …`.
  * **Infrastructure for enum match: landed.** `datatype_to_cmds`
    emits per-variant discriminator fns (`Type.isVariant : Type →
    Prop`, body = `match x with | Type.Variant _ => True | _ =>
    False`) and accessor fns (`Type.Variant_val0 : Type → FieldTy`,
    fallback `default`). `field_access_name` routes
    multi-variant `Field` projections to the accessor naming
    (`Variant_val0`). `Classical.propDecidable` is opened in the
    prelude so match-defined Props decide in `if`-contexts.
    Accessor emission is guarded (`emit_accessors: bool` on
    `krate_preamble`) to run only for the exec-fn entry point —
    spec/proof fns preserve native Lean match, and emitting
    accessors for types with non-Inhabited fields (which spec fns
    routinely use) breaks Lean elaboration via the `default`
    fallback.
  * **Enum match automation: deferred (task #58).** The desugared
    if-chain over discriminators + @[simp]-unfolded accessors is
    structurally correct, but `tactus_auto` (`rfl | decide | omega
    | simp_all`) can't case-split on the scrutinee to close the
    residual `match k with …` subterms. Needs either a
    `cases`-introducing step in `tactus_auto` / `tactus_peel`, a
    new `tactus_cases` tactic that scans enum-typed hypotheses, or
    codegen-level `rcases k` insertion when the body matches on k.
    Current state pinned by `test_exec_match_enum_automation_gap`
    (an Err expectation).
  * **Dep_order regression fixed along the way.** `walk_expr`
    previously skipped `StmtX::Decl { init, .. }`, so
    `let p = Ctor(...)` missed the Ctor's datatype reference and
    the preamble omitted the struct/enum definition. Now walks
    the `init` Place.

* **Generic calls (non-empty `typ_args`) — LANDED.** Exec-fn calls
  can now pass `typ_args` to a generic callee. `Wp::Call` carries
  `typ_args: &'a [Typ]`; `walk_call` composes the value-param
  subst with a type-param subst (mapping each `callee.typ_params`
  name to the rendered `typ_args` via `typ_to_expr`) and applies
  both to the inlined `require` / `ensure` via the existing
  `lean_ast::substitute`. Works because `typ_to_expr`'s
  `TypX::TypParam` arm renders as `Var(name)`, so the value-level
  substitute rewrites type references in-place. Exec fns also now
  emit `(T : Type)` binders at theorem level (via
  `build_param_binders`), so generic exec fns have their
  typ_params in scope. Regression: `test_exec_call_generic`
  (identity over a generic T).

* **Non-int `decreases` (Lean `height` function per datatype).**
  **MVS landed** for concrete, non-generic datatypes:
  1. `to_lean_fn::height_fn_for_datatype` emits `@[simp] noncomputable
     def T.height : T → Nat` alongside the datatype in
     `datatype_to_cmds`. For recursive types: match over variants
     summing `1 + height(f)` per self-referential field (peeling
     `TypX::Boxed` / `TypX::Decorate` to match `typ_to_expr`'s
     Lean-level rendering). For non-recursive types: `fun _ => 1`.
     Lean's equation compiler proves termination structurally.
  2. `sst_exp_to_ast_checked`'s `CheckDecreaseHeight` arm
     dispatches via `decrease_height_datatype(&cur.typ)`: int
     → fast arithmetic path; concrete datatype → `T.height cur
     < T.height prev ∨ (T.height cur = T.height prev ∧
     otherwise)`; other (generic, tuple, etc.) → rejected with
     a clear deferrals message.
  3. `deriving Inhabited` added to every non-generic datatype
     (via a new `Datatype.derives` AST field). Needed because
     accessors like `Stack.Push_val1 : Stack → Stack` have a
     `default` fallback that requires `[Inhabited Stack]`.
     Generic types skip this — would need `[Inhabited A]`
     bounds we don't thread.

     **Future polish — accuracy:** we currently over-derive,
     emitting `deriving Inhabited` on every non-generic datatype
     even when no accessor's `default` fallback is reachable in
     practice (e.g., a single-variant struct never needs the
     fallback because its accessor is total). Lean's derive is
     cheap and over-deriving is harmless, so this hasn't been a
     problem; if/when we hit a datatype whose Inhabited
     derivation Lean rejects (zero-variant enums, recursively-
     uninhabitable shapes), narrow the gate to "emit only when
     a multi-variant accessor with a non-Inhabited field type
     exists."

  **Known interaction with #58 (match automation):** pinned by
  `test_exec_call_recursive_datatype_termination` — recursive
  enum fns compile, the termination obligation is emitted in
  correct shape (`Stack.height rest < Stack.height s` under
  `¬s.isEmpty`), but closing it requires case analysis on `s`
  which is #58's gap. Test asserts the Lean error mentions
  `.height` and isn't the old deferrals rejection; when #58
  lands it flips to `=> Ok(())`.

  **Explicit deferrals (still rejected with clear message):**
  - **Generic datatypes.** `Tree<A>` would need a `[SizeOf A]`-
     style height axiom routed through Lean typeclasses.
     Rejected at `decrease_height_datatype` (requires
     `args.is_empty()`).
  - **Mutually recursive datatype SCCs.** Height fns would need
    a `mutual` block; currently emitted standalone, which Lean
    rejects for cross-type recursion. Defer until a real user
    case motivates the plumbing.
  - **Recursive function fields** (`struct S { f: FnSpec(int) →
    Option<S> }`). Verus has a special axiom
    (`recursive_function_field` in `datatype_height_axioms`) for
    this; we don't mirror it.
  - **Lexicographic `decreases a, b`.** Check if exec fn
    `decreases` is even multi-tuple today — may already be
    rejected upstream.

##### Tier 3 — bigger slices (~1 week each)

* **`&mut` args on calls (#55).** Currently rejected in
  `build_wp_call` via `contains_loc`. Pinned by
  `test_exec_call_mut_arg_rejected` with a rejection message
  that names the task and suggests the
  refactor-to-non-mutating workaround.

  **Semantics**: after `foo(&mut x)` returns, `x` is an
  arbitrary value satisfying its type invariant AND the
  callee's `ensures` (which may reference the new `x`).
  Plus aliasing: two `&mut` args to the same call must be
  distinct (Rust's borrow checker guarantees this upstream,
  so we don't need to check).

  **Implementation plan (MVS scope):**
  1. Detect `&mut` parameters at callee-registration time:
     check `callee.params[i].x.is_mut` (or whatever VIR's
     field is called — read before coding). Collect indices
     of `&mut` positions on callee.
  2. At each call site: for each `&mut` index, extract the
     caller-side destination `VarIdent` from `args[i]` (the
     arg is a `Loc` of the mutated caller var).
  3. In `walk_call`, emit `∀ (x_i' : T_i), type_inv(x_i')`
     binders for each mutated caller var, threaded around
     the post-call continuation. The ensures clause is
     substituted with `p_i ↦ x_i'` (not `p_i ↦ arg_i`).
     After the ensures implication, the continuation sees
     `x_i'` as the new value — achieved by textually
     re-binding the caller var: `let <caller_var_i> :=
     x_i' in <continuation>`.
  4. The single-arg case (one `&mut` param) is the MVS;
     multi-arg is a straightforward extension via nested
     `∀` quantifiers.

  **Explicit deferrals:**
  - **`old(x)` in callee's ensures.** Verus's `ExpX::Old`
    references the pre-call value; currently rejected at
    the expression level. When supporting `&mut` we need to
    pass through `old(x)` as a reference to the pre-call
    value — specifically, the current binding of the
    substitution `p ↦ arg`. Simplest: substitute
    `old(p) ↦ arg` and regular `p ↦ x'` in the ensures
    rewrite.
  - **`&mut` on a non-local expression** (e.g.,
    `foo(&mut v[i])` — mutating through an index). The
    `Loc` may not reduce to a simple `VarIdent`. First
    slice assumes the arg-side `Loc` extracts to a single
    `VarIdent` via `extract_simple_var_ident`; reject
    otherwise.
  - **Multi-`&mut` aliasing** between args is precluded by
    Rust's borrow checker at compile time, so no runtime
    check needed on our side.

  **Companion test to add when feature lands:** the
  currently-pinned `test_exec_call_mut_arg_rejected` flips
  to `=> Ok(())`. Add non-decreasing / ensures-violation
  companions similar to the #54 pattern.

* **Trait-method calls (dynamic + resolved static).** Currently
  rejected via `resolved_method: Some(_)` / `CallTargetKind::
  Dynamic`. Fix: for `DynamicResolved` we can emit a direct call to
  the resolved impl's Lean name (infrastructure exists in
  `to_lean_expr`'s `call_to_node`); for `Dynamic` we need trait-
  method-via-instance encoding (use Lean's typeclass machinery or
  emit `TraitName.method` with the impl inferred from the receiver
  type).

* **`break` / `continue` — LANDED (partial).** Unlabeled break /
  continue in while-shaped loops works end-to-end.
  `Wp::Loop::cond` is now `Option<&Exp>` — `Some` for simple
  `while c { … }`, `None` for Verus's break-lowered form (`while
  c { … break; … }` → `loop { if !c { break; } … }`).
  `WpLoopCtx { break_leaf, continue_leaf }` threads through
  `build_wp` as an `Option<&WpLoopCtx>` parameter; loop body is
  built with this loop's leaves as innermost context.
  `StmX::BreakOrContinue` emits `Wp::Done(leaf)` with the right
  leaf. Still rejected: labeled break/continue (would need a
  label-keyed stack); `invariant_except_break` / `ensures`
  classifications (only at_entry=at_exit=true invariants accepted,
  which matches what the user's `invariant x <= n` syntax
  produces by default). Tests: test_exec_loop_with_break,
  test_exec_loop_with_continue.

##### Ordering rationale

Tier 1 is ordered first because each item is low-cost and unblocks
existing users: every realistic exec fn needs `proof { }` when
automation fails, every realistic exec fn wants readable errors.
Tier 2 is realistic-code unblockers — users can work around missing
pattern matching by avoiding enums, but only so far. Tier 3 is where
we hit scoping breaks: each is its own mini-project with internal
design choices, and each depends on infrastructure that the lower
tiers don't require.

Not on the list: tactic expansion (e.g., routing `nlinarith` /
`ring` / `polyrith` into `tactus_auto` for exec fns) — that's a
design call about automation predictability, not a missing
feature. If a fn needs it today, users can add `proof { by
nlinarith [...] }` once Tier 1 lands.

#### Phase-3 work (explicit non-goals for current scope)

These are deferred by design — the current slice is single-crate exec+proof-fn verification.

* **Cross-crate verification** — `CrateDecls.lean` files holding signatures for downstream crates. DESIGN.md "Cross-crate spec fn availability".
* **`#[verifier::heartbeats(N)]` attribute** — per-fn Lean `maxHeartbeats` override. DESIGN.md mentions; not wired through `vir::ast::FunctionAttrsX`.
* **Lean version pinning / CI matrix.** `lean-toolchain` is pinned to `v4.25.0`; tactic behaviour could shift on upgrade. No automated regression against multiple Lean versions.
* **Per-module `.lean` file generation.** Current design emits one file per fn (`target/tactus-lean/{crate}/{fn}.lean`). At scale, per-module would amortize preamble and olean caching; HANDOFF notes it as future work.

#### Verus-side invariants we depend on

Assumptions about upstream VIR/SST shape or Verus compiler-pass ordering that aren't (and can't straightforwardly be) enforced by Rust's type system. If any of these drift in an upstream rebase, our verification silently mis-compiles or panics. Each has either a shape-drift test, a compile-catch, or a documented fix site.

* **`vir::recursion` inserts `CheckDecreaseHeight` BEFORE the recursive `StmX::Call`.** Our `Wp::Assert` walk relies on this ordering — the assert must appear in the statement sequence strictly before the Call so `build_wp`'s right-to-left fold produces `Assert(CheckDecreaseHeight, Call(...))` rather than `Call(..., Assert(CheckDecreaseHeight))`. If Verus changes the pass to insert after (or inline the check into the call somehow), recursive fns would verify without the termination obligation. **No compile catch; no shape-drift test.** A regression test that constructs a minimal self-recursive SST and verifies the Assert-Call ordering in the walk output would lock this down.
* **`CheckDecreaseHeight.args[0]` is `Bind(Let(params → args, decrease))`** — possibly wrapped in Box/Unbox/CoerceMode/Trigger. `render_checked_decrease_arg` peels and substitutes. **Shape-drift test**: `full_check_decrease_height_shape_pinned` asserts the substituted form, with a failure message naming the fix site.
* **`DUMMY_PARAM = "no%param"` is always position 0 of `callee.params` for zero-arg fns.** `is_zero_arg_desugared` (now retired) relied on this. Post the simplified-krate refactor, both `callee.params` and the call-site args carry the dummy symmetrically, so the check disappeared — but we still rely on Verus inserting the dummy consistently on both sides.
* **Poly wrapper set is `UnaryOpr::Box` / `Unbox` / `Unary::CoerceMode` / `Trigger`.** `peel_transparent` centralises it. Adding a new transparent wrapper that we don't peel would be silently miscompiled. **Shape-drift tests**: `peel_transparent_*` covers each wrapper and the Loc-not-peeled / If-not-peeled cases.
* **`VarIdent` equality by string content, not disambiguate.** Our `sanitize(&ident.0)` uses only the name string, collapsing different `VarIdentDisambiguate` tags with the same name into the same Lean identifier. Verus uses this for SSA renaming (`VarIdent("x", Renamed(2))` vs `VarIdent("x", AirLocal)`). In practice the cases we see are all either fully-renamed (different strings) or consistently-tagged, so collapse is safe — but a future Verus change that relies on disambiguates having different string-level effects would surprise us.
* **Param name stability.** `walk_call`'s substitution map is keyed by `sanitize(param.name.0)`. If Verus starts appending disambiguators to param names (e.g., `foo@0`), the keys in our map and the references in the callee's require/ensure would drift apart.
* **`FunctionX` fields we read:** `params`, `ret`, `require`, `ensure.0`, `typ_params`, `item_kind`, `attrs.broadcast_forall`, `decrease` (via `CheckDecreaseHeight`). Renames break compile (good). Semantic changes (e.g., `require` splitting into static/dynamic halves) would need re-evaluation.
* **`FuncCheckSst` fields we read:** `reqs`, `body`, `post_condition.dest`, `post_condition.ens_exps`, `local_decls`. Same story — renames compile-break.
* **Verus's `ast_simplify` is a monotonic transformation w.r.t. what we care about.** Specifically: it adds the zero-arg dummy, it alpha-renames for unique locals, but it doesn't erase information we depend on. If it starts dropping fields we read, we break.
* **`simplified_krate()` is populated before `verify_bucket` runs** on the same code path. Encoded as `Option<&Krate>`; the `None` case reports a pipeline-ordering error. Unreachable today by design of `verify_crate_inner`, but a new code path could hit it. `verifier.rs` line 1727 handles it gracefully.
* **Mathlib's `omega` / `simp_all` behaviour on the goal shapes we emit.** `tactus_auto`'s closure depends on these tactics handling `∧`-conjoined hypotheses, implications over linear arithmetic, and the let-reduction behaviour we rely on. A Lean/Mathlib upgrade could shift these in subtle ways; we'd likely see test regressions in bulk across a version bump.
* **The `arch_word_bits` / `usize_hi` / `isize_hi` prelude names.** Our codegen emits bare `Var` references to these; the prelude provides the axioms/defs. If the prelude is swapped for a different environment, the references break. Kept in sync via `sanity.rs`'s allowlist.
* **Verus's `StmX` destructures are `..`-free** in our code. Any field addition to `StmX::Assign` / `Return` / `Loop` / `Call` causes a compile error that forces audit. This is the compile-time defence in the upstream-robustness triangle.
* **Verus lowers `while cond { … break; … }` to `cond: None` + an inserted `if !cond { break; }` prelude in the body.** Our `Wp::Loop` accepts both `cond: Some(_)` (no break) and `cond: None` (break-lowered) shapes; `walk_loop` only emits a `cond` gate when `Some`. If Verus changes to keep `cond: Some` with the break preserved in the body, our encoding still produces valid goals but with a spurious `∧ cond` gate that may over-constrain the invariant proof. **No shape-drift test today** — speculative, would surface as a regression in `test_exec_loop_with_break` if Verus's lowering changes.
* **Verus's `auto_proof_block` pass always wraps non-empty content.** The pass synthesises `proof { ... }` blocks around every `assert(P)` / `assert(P) by { tac }` site so they're parsed as proof-mode. We distinguish user-written `proof { }` (semantically meaningful, routed to `Wp::AssertByTactus` with `cond: None`) from auto-wrapped ones via HIR-body emptiness in `rust_to_vir_expr.rs` — auto-wrapped blocks have non-empty HIR bodies, user-written empty blocks don't. **Guarded by `test_exec_auto_proof_block_not_tactus`** which exercises the auto-wrap path and confirms it doesn't trigger Tactus mode.
* **`get_ghost_block_opt` returns `Some(GhostBlockAttr::Proof)` for user-written `proof { }` blocks.** Our `enclosing_fn_is_tactus_auto` + ghost-block-attr detection in `fn_call_to_vir.rs` relies on this attribute classification. If Verus changes how it tags ghost blocks (e.g., a new `GhostBlockAttr::TactusProof` variant, or distinguishing wrapped vs unwrapped at this layer), we'd silently stop detecting user-written proof blocks and route them to the wrong path. **No shape-drift test** — would manifest as `test_exec_proof_block_user_tactic` regressing.
* **`TypX::Boxed` / `TypX::Decorate` are the canonical transparent wrappers for self-referential datatype fields.** Shared via `peel_typ_wrappers` (in `to_lean_sst_expr.rs`), used by `is_int_height`, `decrease_height_datatype`, and `field_is_self_recursive`. Mirrors `typ_to_expr`'s rendering (which peels both to produce Lean-level types). If Verus adds a new transparent wrapper for Rust `&Self` / `Box<Self>` / `Arc<Self>` / etc., one edit to `peel_typ_wrappers` updates all three call sites — without it, recursive-field detection would fail silently (field treated as non-recursive → `height = 1` for the variant → false termination obligation → recursion verifies where it shouldn't). **No shape-drift test** — would manifest as `test_exec_call_recursive_datatype_termination` regressing past the current "match-case-split" gap into a verified-but-wrong state.

### `Wp` — WP DSL (landed)

The earlier `BodyItem` hand-rolled enum + `build_goal_with_terminator(items, rest, terminator, ctx)` positional recursion was replaced by a proper WP algebra. `Wp<'a>` in `sst_to_lean.rs`:

```rust
enum Wp<'a> {
    Done(LExpr),                                              // terminator
    Let(&'a str, &'a Exp, Box<Wp<'a>>),                      // continuation wrappers
    Assert(&'a Exp, Box<Wp<'a>>),
    Assume(&'a Exp, Box<Wp<'a>>),
    AssertByTactus { cond: Option<&'a Exp>, tactic_text: String, body: Box<Wp<'a>> },
    Branch { cond: &'a Exp, then_branch: Box<Wp<'a>>, else_branch: Box<Wp<'a>> },
    Loop {
        cond: Option<&'a Exp>, invs, decrease, modified_vars,
        body: Box<Wp<'a>>, after: Box<Wp<'a>>,
    },
    Call {
        callee, args: &'a [Exp], typ_args: &'a [Typ],
        dest: Option<&'a VarIdent>, call_span: &'a Span,
        after: Box<Wp<'a>>,
    },
}
```

`args: &'a [Exp]` borrows directly from the SST's
`Arc<Vec<Exp>>` — no intermediate `Vec<&Exp>`. `dest` is just the
var name (the destination's type was dead weight, dropped). The
rest of the `Box` uses are forced by Rust's self-referential-enum
rules; see "Known codegen-complexity trade-offs" for the Rc/arena
trade-off discussion.

Each compound node carries its own continuation by construction —
no separate "rest" parameter, no separate "terminator" parameter.
`Done(LExpr)` is the only terminator and has no continuation slot,
so `Return` writing to `Done(let <ret> := e; ctx.ensures_goal)`
(discarding whatever `after` was at that point) is type-level.

Two structural wins over the prior shape:

* **Continuation is type-level.** Can't accidentally compose after
  a `Return` because the type system forbids it.
* **`Return` is cleanly fn-exit.** Previously Return wrote to
  whatever terminator was being threaded through (loop's local
  `I ∧ D < d_old` inside a loop body; fn's ensures at top). Now it
  always writes `ctx.ensures_goal`. The DSL shape gets this right
  for free, and `test_exec_return_inside_loop` /
  `test_exec_return_inside_loop_with_break` pin the semantics.

`build_wp(stm, after, ctx) -> Result<Wp, String>` folds right-to-
left over a `Block`, so each statement's `after` is the already-
built Wp for the rest of the block. The walker
(`walk_obligations(wp, ctx, obl, emitter)` and friends) interprets
the tree, emitting one Lean theorem per obligation site (D,
2026-04-26).

Adding a new WP form means one constructor + one arm each in
`build_wp` and `walk_obligations`. The old flat enum required
editing a central dispatcher; the DSL shape makes composition
obvious.

### Per-obligation theorem emission (D, 2026-04-26)

Replaces the earlier single-theorem emission (`_tactus_body_<fn>`
with a goal that conjoins all obligations) with one Lean theorem
per obligation site. The motivation was an imperfection in the
#51 source-mapping work: with one mega-theorem, Lean's diagnostic
`pos.line` always pointed at the same closing-tactic line
regardless of which obligation failed, so `find_span_mark` had
to use a "closest preceding mark" heuristic that could be off by
one when the failing obligation wasn't the latest mark in the
theorem (e.g., a Termination check on a recursive call followed
by a CallPrecondition mark — the heuristic returned the
CallPrecondition mark instead).

**Architecture.** A walker (`walk_obligations` + per-variant
helpers) descends the `Wp` tree, accumulating an `OblCtx`
(`Let` / `Hyp` / `Binder` frames) at scope-introducing points.
At each obligation site (Assert, Done leaf, loop invariant init,
loop maintain conjunct, call precondition, assert-by) the walker
emits a separate Lean `Theorem`. The obligation goal is
`OblCtx::wrap(obligation_lexpr)` — frames folded outermost-first
to preserve source-order scoping (lets bind names visible to
later hypotheses).

**`AssertKind` split.** SpanMark kinds fall into two roles:
*obligation kinds* (Plain / Postcondition / LoopInvariant /
LoopDecrease / CallPrecondition / Termination) wrap the
expression that IS the proof goal, and *hypothesis kinds*
(LoopCondition / BranchCondition) wrap expressions used as
hypothesis frames (loop cond, branch cond). `find_span_mark`
filters to obligation kinds only — hypothesis SpanMarks
provide `/- @rust:LOC -/` debug comments in the generated
`.lean` but never appear as error labels. The split is
enforced by `AssertKind::is_obligation_kind`.

**Postcondition wrapping.** Each fn-ensures clause is wrapped
in a `Postcondition` SpanMark at `WpCtx::new` time. Without
this, a fn-ensures failure inside an if-branch would surface
the BranchCondition hypothesis mark (closest preceding) and
produce a `(branch condition)` error label; with it, the
Postcondition mark always shadows hypothesis-side marks, and
`emit_done_or_split` splits the wrapped-conjunction Done leaf
into one theorem per ensures clause.

**Done leaf walker.** `emit_done_or_split` recursively peels
two structural shapes: top-level `Let` (push to OblCtx and
recurse on body, so the SpanMark wrapped inside the let
becomes visible) and top-level `BinOp::And` (split into per-
conjunct theorems). Other shapes emit one theorem with kind /
loc from the leaf's outermost SpanMark, falling back to
`"ensures"` / empty loc when the leaf is unwrapped (only
reachable when the fn has zero ensures clauses).

**Tactic-prefix stack.** `Wp::AssertByTactus { cond: None,
tactic }` (i.e., `proof { tactic }`) pushes `tactic` onto
`ObligationEmitter::tactic_prefix` and walks body. Every
theorem emitted in body's scope gets `(tactic) <;> closer`
prepended via `e.emit()`. The `<;>` combinator (rather than
`;`) handles goal-modifying user tactics correctly: a
`simp_all` that closes the goal entirely yields zero remaining
subgoals, and `<;> closer` is a no-op rather than failing
with "no goals".

**Trade-off: theorem count.** Lean now sees ~3-5x more theorems
per fn on average. Each is small (single obligation + frames),
so omega/simp_all are fast on each. Total verification time
is roughly the same. Generated `.lean` files are bigger but
still tractable for inspection. The user-visible win is
exact AssertKind labels and structurally meaningful theorem
names (`_tactus_loop_invariant_count_down_at_test_21_19_3`
vs the prior `_tactus_body_count_down`).

### Upstream-robustness patterns

Tactus is a fork; every Verus rebase is a potential source of
silent breakage. A systematic "what breaks if Verus changes X?"
audit surfaced three complementary defences, which we apply uniformly:

**Explicit field destructures.** We never use `..` in `StmX::_`
patterns — every field is listed with `_` for ones we intentionally
ignore. A Verus-side field addition causes a compile error that
forces audit. This currently applies to `StmX::Call` (all 9 fields),
`StmX::Assign` / `Dest` (both fields), `StmX::Return` (all 4 fields),
and `StmX::Loop` (all 11 fields). The extra lines pay for themselves
the first time Verus adds a field.

**Shared helpers for implicit shape assumptions.** Logic that depends
on a specific SST/VIR shape lives in one named helper, not
duplicated across consumers:

* `peel_transparent(&Exp) -> &Exp` — the Box/Unbox/CoerceMode/
  Trigger wrapper set. Used by `contains_loc`, `lift_if_value`, and
  `render_checked_decrease_arg`. Adding a new transparent wrapper =
  one edit to this helper + compile errors if we missed a site.
* `renders_as_lean_int(&IntRange) -> bool` — the Int-vs-Nat rendering
  decision. Shared between the VIR-AST renderer (proof fns) and
  SST renderer (exec fns) so Clip coercions stay consistent.
* `type_bound_predicate` / `integer_type_bound_node` — shared bound
  rendering.
* `is_int_height` — the int-typed-decrease check for
  `CheckDecreaseHeight`.

**Shape-drift detection tests.** For implicit shape invariants we
depend on but can't enforce with types, a test constructs the
expected shape and asserts the lowering. If Verus's shape drifts,
the test's assertion message points at the exact fix site.

Canonical example: `full_check_decrease_height_shape_pinned` in
`sst_to_lean::tests`. It constructs a synthetic
`CheckDecreaseHeight(Box(Let([(n, tmp)], n)), Box(n_old), False)` —
the shape Verus's `recursion::check_decrease_call` produces — and
asserts that lowering yields the substituted form (`tmp < n_old`)
rather than the shadowing `let n := tmp; n < n_old`. If Verus
changes how `CheckDecreaseHeight` encodes its param-substitution,
this test fails with a message that says:

> Verus's CheckDecreaseHeight `cur` shape has drifted; update
> `render_checked_decrease_arg` in to_lean_sst_expr.rs.

— turning a future mystery (why do my recursive fns suddenly fail
verification?) into a focused test failure with a named fix site.

The triangle these form:
* Explicit destructures catch *field additions* at compile time.
* Shared helpers catch *divergence across consumers* at edit time.
* Shape-drift tests catch *semantic shifts* at test time.

Each closes a different hole.

### Code review strategy

When landing non-trivial work, run five review lenses against the
diff before calling it done. Each catches a different class of
issue; a single "read it over" pass misses most of them.

**1. Linus hat.** Role-play a grumpy maintainer. Look for clever
abstractions that make code harder to understand, defensive code
for scenarios that can't happen, flag soup (`Option<_>` + `bool`
fields that can never take independent values), bad naming,
orphaned docstrings, functions whose signature lies about what
they do.

**2. FP lens.** What's mutable that could be immutable? What's
stateful that could be a parameter? Common hits: `RefCell` on
supposedly-pure functions, shared mutable state across module
boundaries, accumulators that could be folds.

**3. Comprehensive coverage.** What code paths have no test?
Variants of a new enum that aren't exercised, edge cases at the
boundaries, negative tests for claimed-rejections, interactions
between two features.

**4. Upstream-brittleness.** What breaks silently if Verus
changes X? See § "Upstream-robustness patterns" above for the
triangle of defences; the review asks "have we used them?"

**5. Documentation / deferrals.** What's landed but not
documented? Counterintuitive behaviour that needs a caveat?
Deferrals in code comments that aren't in this document's
deferrals catalogue? Stale comments asserting rejected features
that are now accepted?

**Process.** Land the work with tests passing, run the five lenses,
triage each finding (fix now / file follow-up / skip), do the
"fix now" list in a follow-up commit labelled "review cleanup".
Update this document for any caveat or deferral that surfaced.
Typical cleanup pass: 10-30 minutes, catches 3-5 real issues even
on code that looked fine.

Canonical examples from the #50 landing's two cleanup passes:
* *Linus hat* caught `typ_inv_exps` smuggling the asserted condition
  (field's name didn't match its content) and `WpCtx::tactus_asserts:
  RefCell<_>` making `walk_obligations` lie about its purity.
* *FP lens* motivated the two-pass `collect_tactus_haves` rewrite.
* *Coverage* caught missing regression tests for labeled-break
  rejected, nested-loop inner-break, return-inside-loop-with-break.
* *Upstream-brittleness* led to `test_exec_auto_proof_block_not_tactus`,
  which guards against Verus's `auto_proof_block` ever generating
  empty synthetic blocks (which would mis-classify as Tactus).
* *Documentation* surfaced the proof-block goal-modifying-tactic
  semantics worth pinning with a test and a DESIGN.md caveat.

### Two parallel expression renderers — and why we didn't fully unify them

Tactus has two expression renderers:

* `to_lean_expr.rs` (~500 lines) — operates on VIR-AST's `Expr` /
  `ExprX`. Used for spec fn bodies, proof fn requires / ensures /
  goals, decreases clauses, and the **callee spec inlining** on
  exec-fn call sites (the one spot where the exec-fn pipeline reaches
  back into VIR-AST, because `FunctionX` holds specs in VIR-AST form).
* `to_lean_sst_expr.rs` (~560 lines) — operates on SST's `Exp` /
  `ExpX`. Used for exec fn bodies (via the WP pipeline) and the
  `CheckDecreaseHeight` termination obligation specifically.

~200 lines of the per-variant dispatch is structurally parallel: the
four arithmetic binops, the comparison operators, `Var` / `VarLoc`
rendering, `Clip` coercion, constant rendering for the non-float
arms, the quantifier / lambda / choose binder construction.

We investigated three approaches to eliminating the parallel work.

**Approach 1: `trait SourceExpr` over both enum types.** Define a
trait that both `vir::ast::Expr` and `vir::sst::Exp` implement,
exposing methods like `is_var(&self) -> Option<&VarIdent>` or a
normalized variant enum. One renderer dispatches on the trait.

**Rejected.** Roughly half the variants don't cross the VIR-AST/SST
boundary: VIR-AST has `Block` / `Match` / `Ctor` / `PatternX` /
`PlaceX`; SST has `CheckDecreaseHeight` / `CallFun::InternalFun` /
an already-flattened statement sequence. A shared trait would still
need per-impl case-splits for the asymmetric half, net-rearranging
boilerplate without eliminating it. Plus the trait methods would
need to decide on a common representation of `ExprX::Call` (which
has `CallTarget`) vs `ExpX::Call` (which has `CallFun`), and those
are genuinely different shapes — the trait becomes a lossy
compression layer that makes the asymmetric cases harder to reason
about.

**Approach 2: Route callee-spec inlining through SST.** Retire
`to_lean_expr.rs` from the exec-fn path entirely. Before inlining a
callee's `require` / `ensure` at a call site, run `ast_to_sst_func`
(or a subset) on those clauses so they reach the inlining point as
SST expressions.

**Rejected.** `FuncCheckSst` is built per-fn during verification via
`ast_to_sst_func::sst_for_function`, not prebuilt in the krate. So
when verifying caller `A` we don't have callee `B`'s SST — we'd
need to either invoke `ast_to_sst_func` on `B`'s spec on demand
(invasive into Verus's verification entry points, with its own
setup-context dependencies), or pre-SSTify every function in the
krate upfront before verification begins (wasted work if only a
subset of fns are verified). Also: this only removes the ONE shared
site (call-site inlining). Proof fn bodies and spec fn bodies stay
VIR-AST, so `to_lean_expr.rs` still exists — we'd trade
"two renderers with a shared-helper layer" for "two renderers with
an invasive SST-promotion step." Not an improvement.

**Approach 3 (chosen): Shared leaves in `expr_shared.rs`.** Extract
the rules that BOTH renderers must apply identically into a new
module:

* `binop_to_ast` — the VIR `BinaryOp` → Lean `BinOp` table.
  Previously duplicated 33 lines × 2 with identical content.
* `non_binop_head` — head identifier for binops without a structural
  Lean equivalent (`Xor` → `"xor"`, `HeightCompare` →
  `"Tactus.heightLt"`, etc.).
* `const_to_node_common` — the non-float arms of `Constant`
  (`Bool` / `Int` / `StrSlice` / `Char`). Returns `None` for floats;
  each renderer handles floats locally (VIR-AST emits a
  type-annotated literal; SST rejects as unsupported).
* `clip_coercion_head` / `apply_clip_coercion` — resolve `(src_int,
  dst_int)` to the Lean coercion wrapper name (`Int.toNat` /
  `Int.ofNat` / passthrough).

Plus the SST path now calls `to_lean_expr::vir_var_binders_to_ast`
directly for `BndX::Quant` / `Lambda` / `Choose` binders (both sides
use `VarBinders<Typ>`).

Why this is the right level of unification:

* Every rule that could silently diverge — op tables, coercion
  wrappers, constant rendering, binder construction — is now in one
  place. Editing one side would be a compile error at the other.
* The asymmetric variants stay separate because they *are* separate
  — pretending otherwise via a trait would be type-level
  indirection without semantic win.
* No invasive changes to Verus's pipeline. The new module imports
  only `vir::ast` types and `lean_ast` types, so it's orthogonal to
  both renderers' per-variant dispatch.

Residual trade-off worth naming: each renderer still has its own
recursive `exp_to_node` / `expr_to_node` walker, because the
walker's dispatch is on the source-enum variant (which is
asymmetric). Adding a new variant still requires editing both files
*if* that variant corresponds to a shape that appears in both
trees — in practice most new SST variants are exec-specific and
don't touch the VIR-AST path, and vice versa.

### Scope and difficulty

Implementing `sst_to_lean` with full WP is the most significant engineering effort — comparable to `sst_to_air` (~3000 lines). It handles mutation as SSA, control flow, pattern matching, closures, borrow semantics. **Estimated: 3-6 months.**

## Error experience

### Successful check
```
$ tactus check src/algebra.rs
  ✓ double                    (spec fn)
  ✓ triangle                  (spec fn)
  ✓ lemma_double_pos          (0.3s, 42k heartbeats)
  ✓ lemma_norm_nonneg         (0.5s, 118k heartbeats)

4 items checked, 0 errors
```

### Failed tactic
```
$ tactus check src/quad_ext.rs

error: unsolved goal
  --> src/quad_ext.rs:42:1 (norm_nonneg)

  re im d : Int
  h₀ : d ≤ 0
  ⊢ re * re - d * (im * im) ≥ 0

  try: nlinarith [sq_nonneg re, sq_nonneg im]
```

### Auto obligation failure (Phase 2)
```
$ tactus check src/search.rs

error: tactus: auto-tactic failed (overflow check)
  --> src/search.rs:15:25

  lo hi n : Nat
  h₀ : lo < hi
  h₁ : hi ≤ n
  ⊢ lo + (hi - lo) / 2 < 2^64

  add `proof { omega }` at src/search.rs:15
```

### Assumption warning
```
$ tactus check src/wip.rs

warning: unproved assumption
  --> src/wip.rs:28:5

  assume(hard_lemma(x, y))
  ^^^^^^^^^^^^^^^^^^^^^^^ backed by sorry — prove or remove before release
```

## Crate structure in tactus/source/

### New crate: `lean_verify/`
```
lean_verify/
  Cargo.toml
  src/
    lib.rs
    lean_process.rs       — lean subprocess via `lake env lean`
    diagnostics.rs        — parse Lean JSON diagnostics
    source_map.rs         — Lean positions → .rs positions
    prelude.rs            — TactusPrelude.lean content
    project.rs            — manage ~/.tactus/lean-project/ setup
    builtin_paths.rs      — VIR path → Lean name lookup table (Track C)
```

### New files in `vir/`
```
vir/src/
  sst_to_lean.rs       — Track B: WP-based VC generation from SST
  to_lean_expr.rs      — VIR/SST expressions → Lean expression text
  to_lean_type.rs      — VIR types → Lean type text
  to_lean_fn.rs        — spec fn → @[irreducible] def, proof fn → theorem
  to_lean_datatype.rs  — Track D: struct → structure, enum → inductive
```

### Modified files
| File | Change |
|------|--------|
| `builtin_macros/src/syntax.rs` | Tactic mode: capture `by {}`/`proof {}` as TokenStream + span, suspend Verus keywords |
| `vir/src/ast.rs` | Add `TacticBlock(Span)` variant to function body (span, not string) |
| `rust_verify/src/verifier.rs` | Route proof fns to `lean_verify` + install TactusFileLoader |
| `rust_verify/src/file_loader.rs` | TactusFileLoader: sanitizes tactic blocks before rustc lexer |
| `rust_verify/src/config.rs` | Add `--heartbeats`, `--lean-path` flags |

### tree-sitter-tactus (separate repo)
```
tree-sitter-tactus/
  grammar.js              — Tactus grammar: Rust + Lean tactic block rules
  src/scanner.c           — external scanner (strings, raw strings, block comments)
  test/corpus/
    tactic_blocks.txt     — 36 tactic-specific tests
    declarations.txt      — Rust declaration tests (attribute fixes)
    ...                   — other inherited tree-sitter-rust tests
```

No `rustc_lexer` modification needed. Unicode and Lean syntax are handled by the FileLoader sanitization.

### Removed (after Track B completes)
- `air/` crate — Z3 interface
- `sst_to_air.rs`, `sst_to_air_func.rs` — replaced by `sst_to_lean`

Kept during Track B development for reference and differential testing.

## Trait mapping (Phase 3)

| Tactus Trait | Lean/Mathlib Class |
|---|---|
| `Ring` | `CommRing` |
| `OrderedRing` | `LinearOrderedCommRing` |
| `Field` | `Field` |
| `OrderedField` | `LinearOrderedField` |
| `AdditiveGroup` | `AddCommGroup` |
| `PartialOrder` | `PartialOrder` |

## Implementation plan

Work proceeds in parallel across three tracks. No sequential gating — all tracks start immediately.

### Track A: Proof fn pipeline (the core loop)

Gets a proof fn from `.rs` all the way to a verified Lean theorem. This is the foundation everything else builds on.

1. Modify `builtin_macros/` — tactic mode (TokenStream capture + span recording), keyword suspension
2. Integrate tree-sitter-tactus — extract tactic block text (Unicode-aware) by source span
3. Add `import` keyword to grammar and proc macro
4. Add `mutual ... end mutual` syntax to grammar and proc macro
5. Thread `TacticBlock(span)` through VIR
6. Create `lean_verify/` crate — Lake project management, precompiled Mathlib (`lake exe cache get`), Lean subprocess
7. Implement `to_lean_type.rs` and `to_lean_expr.rs`
8. Implement `to_lean_fn.rs` — spec fn → `@[irreducible] noncomputable def`, proof fn → `theorem`
9. Implement definition ordering (topological sort from VIR call graph)
10. Implement namespacing (VIR Path → Lean namespace)
11. Source map + error mapping
12. Modify `verifier.rs` — route proof fns to Lean

**Milestone**: spec fns + proof fns with `by { ring }`, `by { omega }`, `by { nlinarith [...] }` verify end-to-end.

### Track B: Exec fn VC generation (`sst_to_lean`)

Implements weakest-precondition VC generation from SST targeting Lean. This is the largest single effort. Runs in parallel with Track A — shares `to_lean_expr.rs` and `to_lean_type.rs`.

1. Implement `sst_to_lean.rs` — WP-based VC generation from SST
2. Simple straight-line code first (let, if/else, return)
3. Mutation as SSA (variable versioning)
4. Loop obligations (init/maintain/use)
5. Control flow (break, continue, early return)
6. Overflow checking for fixed-width types
7. `proof { }` results threaded into VC context
8. `assert(P) by { tactics }` → `have h : P := by <tactics>` in VC
9. `assert forall|x| P by { tactics }` → auto-intro + tactics
10. `assume(P)` → sorry + warning
11. `tactus_auto` macro for auto obligations
12. Pattern matching, closures, borrow semantics (mutable refs as functional updates)
13. Ghost/Tracked parameter unwrapping, `@` view operator

**Milestone**: exec fns with loops, mutation, and overflow checks verify through Lean.

Once Track B is complete, `air/` crate and `sst_to_air` are removed.

### Track C: vstd translation + built-in path mapping

Translates Verus's standard library to Lean. Ongoing, incremental.

1. Write `TactusPrelude.lean` — Seq (opaque index), Set, clip fns, arch_word_bits axiom
2. Build VIR path → Lean name lookup table (start with core Seq/Set/Map operations)
3. Translate `vstd::seq` spec fns to Lean
4. Translate `vstd::set` spec fns
5. Translate `vstd::map` spec fns
6. Translate `vstd::arithmetic` lemmas (many map to Mathlib)
7. Expand coverage incrementally as users hit "unsupported vstd function" errors

**Milestone**: Programs using basic Seq/Set/Map operations verify.

### Track D: Types, traits, multi-crate (starts after A+B have milestones)

1. Struct → `structure`, Enum → `inductive`
2. Trait → `class`, Impl → `instance`
3. Map to Mathlib hierarchy (Ring → CommRing, etc.)
4. Cross-crate declaration files (`CrateDecls.lean`)
5. `mutual ... end mutual` → Lean `mutual ... end`

### Ongoing: Polish

1. Per-module Lean generation with imports
2. IDE integration (show goal states)
3. Better error messages with tactic suggestions
4. Performance profiling
5. Differential testing (Verus vs Tactus on same specs)

## Setup and testing

### Prerequisites

- **Lean 4**: via [elan](https://github.com/leanprover/elan) or `nix-shell -p lean4`
- **Rust 1.94+**: Verus pins a specific stable version (uses `RUSTC_BOOTSTRAP=1` for nightly features)

### First-time build

```bash
cd tactus

# Build vargo (Tactus's custom cargo wrapper)
cd tools/vargo && cargo build --release && cd ../../source

# Build Tactus + vstd (expected: "1530 verified, 0 errors")
PATH="../tools/vargo/target/release:$PATH" vargo build --release
```

### Mathlib setup (for ring/nlinarith/linarith)

Tactus downloads precompiled Mathlib oleans (~2 GB) from Mathlib's CI cache. No compilation needed — takes 2-5 minutes.

```bash
# Option 1: Use the setup script
cd tactus/source/lean_verify
./scripts/setup-mathlib.sh

# Option 2: With nix
nix-shell -p lean4 --run ./scripts/setup-mathlib.sh

# Option 3: Custom project directory
TACTUS_PROJECT_DIR=/path/to/project ./scripts/setup-mathlib.sh
```

This creates `~/.tactus/lean-project/` with:
- `lakefile.lean` — imports Mathlib
- `lean-toolchain` — pins Lean version
- `.lake/` — precompiled Mathlib oleans (downloaded, not compiled)

**Without Mathlib**: Core tactics still work (`omega`, `simp`, `decide`, `exact`, `apply`, `intro`, `induction`, `cases`, `rfl`, `unfold`). Mathlib tactics (`ring`, `nlinarith`, `linarith`, `norm_num`, `positivity`, `field_simp`) require the Lake project.

### Running tests

```bash
cd tactus/source

# Quick compile check (no special toolchain):
cargo check -p lean_verify

# Full compile check (needs RUSTC_BOOTSTRAP for rustc_private):
RUSTC_BOOTSTRAP=1 cargo check -p rust_verify

# Unit tests for lean_verify (needs Lean 4 on PATH):
cargo test -p lean_verify

# End-to-end tests (63 tests):
# - 57 tests need Lean 4
# - 6 tests also need Mathlib (setup-mathlib.sh)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Run a single test:
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_mathlib_ring

# vstd verification (1530 functions):
PATH="../tools/vargo/target/release:$PATH" vargo build --release
```

### Test categories

| Category | Count | Requirements |
|----------|-------|---|
| Core tactics (omega/simp/decide) | 47 | Lean 4 |
| Mathlib tactics (ring/nlinarith) | 6 | Lean 4 + Mathlib |
| Error reporting | 4 | Lean 4 |
| Datatypes + traits | 6 | Lean 4 |
| **Total** | **63** | |

### How the verifier routes to Lean

When Tactus encounters a `proof fn` with a `by { }` block:

1. The proc macro captures the tactic body as a raw `TokenStream` and emits `#[verus::internal(tactic_body("..."))]` plus `#[verus::internal(lean_import("..."))]` for each import
2. `rust_to_vir_func.rs` threads these to `FunctionAttrsX.tactic_body` and `FunctionAttrsX.lean_imports`
3. `verifier.rs` detects `tactic_body.is_some()`, collects all VIR functions, and calls `generate_lean_file`
4. `generate_lean_file` emits imports, prelude, topologically-sorted spec fns (with mutual recursion groups), and the theorem with tactic body; returns a source map
5. The verifier invokes `lake env lean --stdin --json` (if `~/.tactus/lean-project/` exists) or `lean --stdin --json` (fallback)
6. Lean's JSON diagnostics are parsed, source map translates line numbers, and errors are reported through Verus's standard diagnostic system

## Open questions

1. **Recursive termination**: Simple `decreases n` → `termination_by n`. Complex `decreases` with `via` clauses → `termination_by` + `decreasing_by`. Design when we encounter real examples.

2. **Broadcast lemmas**: `broadcast proof fn` + `use broadcast` → require users to invoke lemmas explicitly in tactics (per transparency principle). No automatic ambient facts.

3. **Bitwise operations**: VIR's `BitwiseOp` → Lean/Mathlib `BitVec`. Needs design for bitvector-heavy proofs.

4. **Spec closures**: `FnSpec` type → Lean function type `A → B`. Behavioral differences TBD.

5. **Multiple ensures**: Currently conjunction `E₁ ∧ E₂`. Users split with `constructor` or `refine ⟨?_, ?_⟩`. Consider alternative: separate theorems per ensures clause.

6. **Lean project path for distribution**: The Lean project path (`tactus/lean-project/`) is currently resolved via `CARGO_MANIFEST_DIR` at compile time. This works for development but breaks if the binary is moved. For distribution, need a runtime discovery strategy (e.g., relative to executable, or `TACTUS_LEAN_PROJECT` env var which is already supported).
