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
  first | omega | simp_all | decide | norm_num | linarith | nlinarith |
    (fail "tactus: auto-tactic failed — add explicit proof block"))
```

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
while cond invariant I decreases D { body }
```

Generates three theorems:
1. **Init**: `requires ∧ setup → I`
2. **Maintain**: `I ∧ cond → wp(body, I) ∧ D_decreases`
3. **Use**: `I ∧ ¬cond → ensures`

Each is a separate Lean `theorem`. Auto-checked by `tactus_auto`. On failure, user adds `proof { }` blocks.

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

`sst_to_lean::build_goal` handles `if c { s1 } else { s2 }` by cloning the continuation `rest` into both branches syntactically: `wp(s1 ++ rest) ∧ wp(s2 ++ rest)`. `BodyItem::IfThenElse` carries `Vec<BodyItem>` per branch, so cloning is recursive. N sequential ifs at the same level produce 2^N copies of the innermost continuation in the goal AST. For realistic exec fn bodies (few-level nesting) this is fine; for pathological cases it could bloat codegen time and the generated `.lean` file.

Alternative: introduce a `let _goal_k := <rest_goal>` binding at each if and have both branches refer to `_goal_k`. This preserves logical equivalence with linear size. Not implemented — the cost hasn't shown up yet — but noted here so the trade-off is explicit when someone hits it.

### `StmX::Call` — landed (slice 7)

Exec fns can now call other exec/proof/spec fns. The WP rule for
`let y = foo(a1, a2)`:

```
(let p1 := a1; let p2 := a2; requires_conj)
∧ ∀ (ret : RetT), h_ret_bound(ret) →
    (let p1 := a1; let p2 := a2; ensures_conj_using_ret) →
    let y := ret; wp(rest, terminator)
```

Param substitution is done via Lean `let`-bindings rather than
rewriting the callee's spec at the SST level — same trick as
`_tactus_d_old` for loops, cheap and obviously correct. The callee
does NOT need its own Lean definition; we inline its
requires/ensures using `vir_expr_to_ast` at each call site.

`build_fn_map` constructs the `Fun → &FunctionX` lookup once per
fn-verification and threads it through `check_stm` / `walk` /
`build_goal_with_terminator`. A new `BodyItem::Call { callee, args,
dest }` variant captures the relevant shape; `build_call_conjunction`
emits the WP.

**Restrictions (rejected by `check_call`):**

* **Trait-method calls** — `resolved_method: Some(_)` rejected.
  Dynamic-dispatch resolution requires plumbing the concrete impl
  through from VIR; deferred.
* **Generic calls** (`typ_args` non-empty) — rejected. Generics
  complicate both the callee signature lookup (monomorphization
  needed) and the Lean-level type substitution.
* **`&mut` args** — rejected (`ExpX::Loc` in arg position). Would
  need "havoc mutated args after call" semantics, parallel to loop
  modified-var quantification.
* **Split-assertion calls** (`split: Some(_)`) — rejected. Verus's
  split-mode error reporting that we don't replicate.
* **Cross-crate callees** — rejected. The `Fun → FunctionX` map only
  covers the current crate; cross-crate needs a `CrateDecls.lean`
  scheme (Phase 3 work).

**Known gap: no termination obligation on recursive calls.**
A fn that recursively calls itself with the same arguments will
verify even though it doesn't terminate. Fixing this needs a
decreasing-measure comparison across the call — similar to loops'
`decreases` but per-fn. Callee's own termination check handles
well-foundedness *within* the callee body, but the caller's
obligation to decrease when recursing isn't emitted.

### `_tactus_d_old` aliasing across nested loops

`sst_to_lean::build_loop_conjunction` emits `let _tactus_d_old := D; …` inside every loop's maintain clause to capture the decrease measure pre-body. The name is literal, not gensym'd, so nested loops' `let _tactus_d_old` bindings shadow each other in Lean.

This is correct for the current architecture: the inner loop's shadow is confined to the inner's maintain conjunct, and the outer's `_tactus_d_old` reference lives in the outer's maintain conjunct (a sibling, not a descendant), so they never clash in scope. A gensym'd `_tactus_d_old_<loop_id>` would make the independence syntactically obvious but doesn't change semantics. Worth threading a counter through `build_loop_conjunction` if we ever refactor loops into a structure where scoping IS ambiguous — until then, the literal name is fine and keeps the generated Lean readable.

### Tactic-string interning (minor TODO)

`sst_to_lean::loop_tactic()` allocates the same `"tactus_peel; all_goals tactus_auto"` String on every call. For a crate with hundreds of exec fns with loops this adds up. Options: `const` static slice + a `Tactic::Static(&'static str)` variant, or define the composite as a single macro in `TactusPrelude.lean` (e.g., `tactus_auto_loop`) and emit `Tactic::Named("tactus_auto_loop")`. Not urgent — current cost is negligible — but worth nudging on any next prelude pass.

### Known deferrals, rejected cases, and untested edges

A flat catalogue of things that don't work yet, organized by where in the pipeline they're rejected or where the gap lives. Updated as of the post-slice-5 FP pass. If a gap has its own detailed section elsewhere in this doc, it's cross-referenced rather than duplicated.

#### Documentation debt

* **HANDOFF.md is out of date.** Reflects the 109-test / pre-loop baseline. Missing: the unified `build_goal_with_terminator` story, `tactus_peel` recursive macro, u-types-as-Int soundness fix, `lift_if_value` for tail / let-bound if-expressions, early-return support, the shape-specific-tactics-at-emit-time principle, `arch_word_bits` wiring, usize/isize status. Top priority for the next session.

#### Statement-level forms rejected by `check_stm`

Each one returns `Err("… not yet supported")`; users get a clean rejection instead of silent pass.

* **`StmX::BreakOrContinue`** — `break` / `continue` inside loops. Blocks `while`-with-exit patterns. Enabling this also requires relaxing `cond: Some` (loops that break compile to `cond: None`) and accepting `invariant_except_break` invariants (at-entry but not at-exit).
* **`StmX::AssertBitVector`** — `assert by(bit_vector)`. Bitvector reasoning backend.
* **`StmX::AssertQuery`** — `assert by(…)` with specific tactics / queries. Would need to translate the `AssertQueryMode` into a Lean tactic choice.
* **`StmX::DeadEnd`** — markers Verus uses for unreachable code. Usually harmless to skip, but we reject rather than silently strip in case a future pipeline relies on them.
* **`StmX::OpenInvariant`** — atomic invariant opening for concurrent verification. Out of scope until concurrency support lands.
* **`StmX::ClosureInner`** — exec closure bodies. Depends on `ExpX::CallLambda` support.

#### Expression-level forms rejected by `check_exp`

* **`UnaryOp` variants beyond `Not` / `Clip` / `CoerceMode` / `Trigger`** — the spec-fn path (`to_lean_expr`) handles more (BitNot, IntToReal, etc.) but `check_exp` on exec bodies is conservative; add as needed.
* **`BinaryOp::HeightCompare { … }`** — VIR's termination-height comparison.
* **`BinaryOp::Index(_, _)`** — array / slice indexing with bounds check.
* **`BinaryOp::StrGetChar`** — string character lookup.
* **`BinaryOp::IeeeFloat(_)`** — IEEE float comparisons. Verus doesn't support `f32`/`f64` at all; this branch exists for completeness.
* **`ExpX::Ctor(..)`** — datatype constructors in exec fns. Blocks any exec code that constructs enum/struct values.
* **`ExpX::CallLambda(..)`** — closure calls. Blocks fns that invoke stored closures.
* **`ExpX::ArrayLiteral(_)`** — `[a, b, c]` literals.
* **`ExpX::Old(..)`** — `old(x)` (pre-state). Relevant for `ensures` that compare post-state to pre-state; untested even for supported features because we don't handle it anywhere.
* **`ExpX::Interp(_)`** — only appears inside Verus's interpreter; an internal-bug rejection rather than a feature gap.
* **`ExpX::FuelConst(_)`** — fuel-reveal constants. Blocks `reveal_with_fuel` in exec fns.
* **`CallFun::InternalFun(_)`** — Verus's internal fns (distinct from user fns).

#### Loop-shape restrictions (rejected by `check_loop`)

Only the simplest `while` shape is accepted. All other loop shapes return `Err`.

* **`loop_isolation: false`** — non-isolated loops (body sees outer context directly rather than via the invariant).
* **`cond: None`** — loops without a simple `while` condition. Includes anything with `break`, any `for` loop, any `loop { … }` with manual exit.
* **Non-empty condition setup block** — `while` conditions that desugar into a small statement prelude (complex expressions that aren't pure).
* **Lexicographic `decreases`** — multi-expression measures (`decreases (a, b)`). Only single-expression is accepted.
* **`invariant_except_break` / `ensures` loop invariants** — any invariant with `at_entry: false` or `at_exit: false`. Only "true at entry AND exit" variants accepted.

#### Soundness trade-offs accepted (not pure bugs, but worth knowing)

* **Usize subtraction truncates silently** — see the usize/isize section above.
* **Usize arithmetic rarely verifies automatically** — bounds are emitted but `tactus_auto` can't discharge symbolic `< usize_hi`; users need custom `proof { … }` with `arch_word_bits_valid` case-split.
* **Char bound admits surrogates** — `c < 0x110000` covers U+0000..U+10FFFF but includes the UTF-16 surrogate range U+D800..U+DFFF. Verus / Rust's `char` also don't distinguish, so our bound matches their semantics. No downstream soundness impact within the same system.
* **`BodyItem` clone cost is exponential in nested if/lift depth** — documented under "Known codegen-complexity trade-offs". Fine for realistic code.
* **`_tactus_d_old` shadows in nested loops** — relies on scope to disambiguate; documented in its own section.

#### User-facing features not tested (or possibly broken)

* **`proof { … }` blocks inside exec fns** — DESIGN.md describes them as supported, but we never exercised them against the slice-1-through-5 WP pipeline. The `have h : P := by <tactics>` plumbing likely needs explicit support in `walk` / `build_goal_with_terminator` for hypothesis threading. Untested.
* **`assert(P) by { tactics }`** — user-written tactic bodies for asserts inside exec fns. Currently `StmX::Assert` treats the assert as a leaf obligation closed by `tactus_auto`; user-provided tactic bodies are not plumbed through.
* **`assume(P)` warnings** — DESIGN.md promises a "unproved assumption" warning. Not wired; `StmX::Assume` emits the hypothesis silently.
* **Return in the `else` branch of an if** (where `then` falls through) — inverse of `test_exec_early_return`. Untested.
* **Loops modifying multiple variables** — `quantify_mod_vars` handles arbitrary-arity modified sets, but every loop test modifies exactly one var.
* **Nested if where each branch contains a different loop** — combinatorial coverage gap.
* **Loop body ending in an early return** — `while c { if p { return 0; } … }`. Should work in principle (early return handling composes), untested.
* **Bit-width coverage** — only `u8`, `u32`, `i8` tested end-to-end. `u16` / `u64` / `u128` / `i16` / `i32` / `i64` / `i128` go through the same codegen path but lack regression tests.

#### Tactic / automation limitations

* **`tactus_auto`'s toolbox is `rfl | decide | omega | simp_all`.** Exec-fn obligations needing `nlinarith`, `ring`, `polyrith`, `aesop`, `positivity`, etc. fall through to the `fail` branch. Proof fns *can* use any Mathlib tactic in their `by { … }` block; exec fns can't.
* **No per-fn tactic override.** A user who wants `ring` for a specific exec fn has no way to request it. A `#[verifier::tactus_tactic("ring")]` attribute plumbed into `FunctionAttrs` would fix it.
* **Mathlib auto-tactics unused for exec fns.** Exec-fn `tactus_auto` is intentionally minimal to keep verification predictable; extending it is a design call, not a straight addition.

#### Architecture debts (working-but-not-ideal)

* **Two-pass over loop bodies.** `walk`'s Loop arm calls both `collect_modifications` and `walk` on the body; fusing would save a pass but entangles modifications with WP-item collection. Documented; left alone.
* **`walk` allocates 1-element `Vec`s per non-Block statement.** Keeps the pure-fn signature simple at the cost of heap traffic. `SmallVec` would help; not worth a new dep yet.
* **Sanity-check allowlist maintained by hand.** Adding a prelude def (like `usize_hi`) requires remembering to update `sanity.rs`. No automated sync; compiler error on mismatch (panic in debug builds).
* **`_tactus_d_old` not gensym'd** — see its dedicated section.
* **`loop_tactic()` allocates its tactic string on every call** — tiny TODO, see its dedicated section.

#### Phase-3 work (explicit non-goals for current scope)

These are deferred by design — the current slice is single-crate exec+proof-fn verification.

* **Cross-crate verification** — `CrateDecls.lean` files holding signatures for downstream crates. DESIGN.md "Cross-crate spec fn availability".
* **`#[verifier::heartbeats(N)]` attribute** — per-fn Lean `maxHeartbeats` override. DESIGN.md mentions; not wired through `vir::ast::FunctionAttrsX`.
* **Lean version pinning / CI matrix.** `lean-toolchain` is pinned to `v4.25.0`; tactic behaviour could shift on upgrade. No automated regression against multiple Lean versions.
* **Per-module `.lean` file generation.** Current design emits one file per fn (`target/tactus-lean/{crate}/{fn}.lean`). At scale, per-module would amortize preamble and olean caching; HANDOFF notes it as future work.

### `BodyItem` as a future WP DSL

`sst_to_lean::BodyItem` is currently a hand-rolled enum whose variants (Let, Assert, Assume, Return, IfThenElse) each represent one weakest-precondition-transforming step. It works, but conflates two shapes:

* **Continuation transformers** — `Let`, `Assert`, `Assume` each take a "rest of body" goal and wrap it, producing an outer goal. They compose as a right-fold over a flat list.
* **Control flow** — `Return` discards the continuation; `IfThenElse` splits into two sub-continuations.

When loops land (which bring `Init` / `Maintain` / `Use` theorems with their own quantifier structure) and `assert(P) by { … }` gains a tactic-block form, this flat enum will probably want to graduate to something more principled — e.g., a small algebra whose constructors are explicit about whether they wrap, branch, or terminate, or a free-monad-ish "WP DSL" where each node carries its continuation by construction. Premature to refactor now. Worth keeping in mind so the next handful of slices don't accidentally keep piling onto the flat-enum shape past its natural limits.

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
