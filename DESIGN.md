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

### reveal_with_fuel and unfold in Tactus

Verus's `reveal_with_fuel(f, n)` controls Z3's recursion-unrolling depth — telling the SMT solver it may unfold `f` up to `n` times when discharging the surrounding obligation. Lean's deterministic kernel has no analog: unfolding is requested explicitly with `unfold f` (one step) or `simp [f]` (full unfolding under simp-rewrite control), and the kernel evaluates termination structurally rather than via fuel-bounded unrolling.

In a `tactus_auto` exec fn, `proof { ... }` blocks hold raw Lean tactic text (the FileLoader sanitizes the brace body to spaces; the original bytes are read off disk at codegen time and emitted verbatim). So a user who would write `proof { reveal_with_fuel(fact, 3); }` in a Verus fn writes `proof { unfold fact }` in a Tactus fn. The latter exposes `fact`'s body to subsequent obligations via the theorem-level tactic-prefix mechanism (see `Wp::AssertByTactus { cond: None, .. }`).

For proof fns (`by { ... }` syntax), the entire body is Lean tactic text by construction — `unfold f` works directly there too, and `reveal_with_fuel` doesn't apply.

The `ExpX::FuelConst(_)` SST variant is a separate, internal Verus construct: produced only by `vir::recursion::rewrite_rec_call_with_fuel_const`, and only called from `vir::expand_errors` (the Z3 SMT-error-expansion pipeline). Tactus doesn't traverse that pipeline, so `FuelConst` is structurally unreachable in our path. The catch-all `Err` arm in `to_lean_sst_expr.rs` is defensive — hitting it would mean a Verus-side pipeline change worth investigating.

### Type-system-enforced invariants

Several runtime contracts in the codebase have been promoted to type-level enforcement. The pattern: identify a property the code *should* hold (a runtime check, panic, or convention), then introduce a newtype whose constructors are the only path to producing values that satisfy the property. The compiler enforces the invariant at every site that touches the type — half-done refactors fail to compile rather than producing silent miscompilations.

**`LeanName` (#99) — VarIdent → Lean-name conversion is disambiguator-aware.** Pre-#99, our renderer projected `VarIdent` to `String` via `sanitize(&v.0)`, dropping the disambiguator. Two distinct VarIdents with the same base name (e.g., `tmp%%` synthetic temps from `ast_simplify::temp_var`) collapsed to the same Lean string, and Lean's let-shadowing silently lowered chained `0 <= i <= 10` to `True`. Post-#99: `LeanName` is a newtype with no `From<String>`/`From<&str>` impl, only constructable via explicit constructors (`from_var_ident` / `from_path` / `from_field` / `lit` / `synthetic`). `ExprNode::Var(LeanName)`, `ExprNode::Let { name: LeanName, .. }`, `Binder { name: Option<LeanName>, .. }`, `Pattern::Var(LeanName)` enforce at compile time that any name flowing into the AST came from one of the explicit constructors. A new contributor can't accidentally write `ExprNode::Var(sanitize(&v.0))` — that's a type error. See `lean_name.rs` module docs for the soundness story.

**`Validated<'a>` (#100) — Exp lowering is panic-free by construction.** Pre-#100, `sst_exp_to_ast(&Exp) -> LExpr` was an "infallible" rendering function whose contract was "caller has already validated via `sst_exp_to_ast_checked`." The contract was a runtime-checked panic; nothing prevented a caller from passing an unvalidated `&Exp`. Post-#100: `Validated<'a>` is a newtype `{ inner: &'a Exp }` constructable only via `Validated::check(&Exp) -> Result<Validated, String>`. The lowering function `lower(&Validated) -> LExpr` cannot panic — the type guarantees the input was already validated. `Wp<'a>` variants (`Let`, `Assert`, `Assume`, `AssertByTactus.cond`, `Branch.cond`, `Loop.cond`/`validated_invs`/`decrease`, `Call.args`) hold `Validated<'a>` so the inside of every walker is panic-free by construction. `build_wp` / `build_wp_loop` / `build_wp_call` are where validation happens — the construction sites call `Validated::check(...)?` and propagate the `Err` to callers. The migration shim was removed via #115 (sites use either the typed pipeline or `sst_exp_to_ast_checked(...).expect("<contract>")`). **Validated stays borrow-only.** An earlier #114 attempt dropped the `'a` to enable synthesizing fresh `¬cond_exp` Exps inside `build_wp_loop` for the non-empty cond_setup transform; that change traded the borrow contract for an `Arc<Exp>` clone in every Validated. Reverted in favour of `Wp::Hyp { hyp: LExpr, body }` — synthesized hypotheses go through an LExpr-level node instead of being shoehorned through Validated, keeping the validation contract scoped to genuine SST borrows.

**`HashMap<LeanName, Expr>` for substitution maps (#101) — keys are typed.** Follows naturally from #99: now that names in the AST are `LeanName`, the substitution map (`lean_ast::substitute`'s `subst` parameter) accepts `HashMap<LeanName, Expr>` instead of `HashMap<String, Expr>`. A caller can't accidentally insert a string key that doesn't correspond to a real name source — every key has to come from one of the explicit `LeanName` constructors. Closes the same class of "string-typed name escapes" bug as #99 did at the AST level, just one layer up at the call-site inlining pipeline.

**`AssertKind` sum-type split (#102) — obligation/hypothesis is structural.** Pre-#102, `AssertKind` was a flat enum with eight variants and a runtime `is_obligation_kind()` method discriminating Obligation-side from Hypothesis-side variants. Adding a new variant required remembering to update the discriminator; forgetting silently miscategorized the new variant. Post-#102: `enum AssertKind = Obligation(ObligationKind) | Hypothesis(HypothesisKind)`. Adding a new variant means picking which arm it lives in. Filtering becomes `matches!(kind, AssertKind::Obligation(_))` — structural and complete.

**`LoopInvKind` enum replaces `(at_entry, at_exit)` bool pair (#103).** Verus's `LoopInv` carries two booleans encoding three meaningful states + one nonsensical `(false, false)` we'd silently filter to no contribution. Pre-#103 our code consulted `i.at_entry` / `i.at_exit` directly. Post-#103: at the `build_wp_loop` boundary, `LoopInvKind::from_loop_inv(&LoopInv) -> Result<LoopInvKind, String>` rejects `(false, false)` with a clear error and produces one of three named states (`Invariant`, `InvariantExceptBreak`, `Ensures`). Downstream sites pattern-match via `kind.at_entry()` / `kind.at_exit()` (each implemented as exhaustive match — adding a variant compile-errors at every consumer).

**`MutArgInfo` struct fuses parallel arrays (#105).** Pre-#105, `mut_args: Vec<(usize, &VarIdent)>` and `mut_idx_to_fresh: HashMap<usize, LeanName>` were parallel structures keyed on the same `usize`, with `.expect("fresh name should exist for every &mut param idx")` on every consumer-side lookup. Post-#105: `Vec<MutArgInfo { param_idx, caller_var, fresh }>` bundles the three fields together. The `expect()` is gone; the type guarantees the fresh name is present alongside the rest of the entry. `push_post_call_frames` no longer takes a separate `mut_args` parameter — it iterates `subst.mut_args` directly.

**`DecreaseLevel` struct fuses parallel arrays (#114 review-pass).** Pre-fix (introduced by #110 lex decreases), `Wp::Loop` held `decrease: Vec<Validated<'a>>` and `d_old_names: Vec<String>` as parallel arrays with a `debug_assert_eq!(decrease.len(), d_old_names.len())` and per-level indexing into both. Same anti-pattern #105 already retired for `MutArgInfo`. Post-fix: `Vec<DecreaseLevel { value: Validated<'a>, d_old_name: String }>` bundles the level's measure and its snapshot name. `walk_loop` and `lex_decrease_obligation` take `&[DecreaseLevel<'a>]`; the `debug_assert_eq!` is gone — the "same length" invariant is structural. Surfaced by the 14-lens review pass (lens #13, typed-invariant) on the same day #110 + #114 landed; same-day review caught the regression of the just-retired pattern before it shipped.

**`build_wp_call` / `build_wp_loop` take destructured fields directly (#104).** Pre-#104, both helpers took a `&'a Stm` and immediately re-destructured with `let StmX::Call { … } = &stm.x else { unreachable!("build_wp_call called on non-Call statement"); };` — a runtime panic if the dispatcher ever called them on the wrong variant. Post-#104: `build_wp_call(fun, resolved_method, is_trait_default, typ_args, args, split, dest, call_span, after, ctx)` and `build_wp_loop(loop_isolation, id, label, cond, body, invs, decrease, after, ctx, outer_loop_stack)` take the fields directly. The destructure happens at the `build_wp` dispatch site (an explicit `StmX::Call { … }` / `StmX::Loop { … }` match arm with no `..`), where any Verus-side field addition still causes a compile error — the upstream-robustness defence stays intact, just lifted from inside the helpers to the dispatcher. The wrong-variant case is now structurally unrepresentable: there's no `Stm` parameter to mismatch against.

**The pattern, named.** When a value's type doesn't carry the property the code requires of it, and the requirement is checked at runtime via panic or assertion: introduce a newtype, make its constructors the only path that satisfies the property, and let the type system enforce the rest. Reviewer-visible at every call site (the constructor name documents the source); refactor-resistant (half-finished migrations don't compile); future-proof (new code added in years can't accidentally break the invariant). The cost is a typed wrapper. The benefit is a soundness hole that's structurally unrepresentable.

### Potential future applications of the typed-invariant pattern

Candidates noted from prior audits but not yet promoted. Each is a runtime-checked invariant that could be lifted to the type system; each was judged below the cost/benefit threshold *for now*. If a related bug surfaces — or if the codebase grows to where the runtime check becomes load-bearing — they're the natural next applications.

* **`OblCtx` frame ordering invariant.** `OblCtx::with_frame` accepts any `CtxFrame` in any order; `wrap` folds outermost-first to preserve source-scoping. The "outermost-first" invariant is a documented contract on the API, not enforced by the type. A typed builder pattern (e.g., separate `OblCtxOuter` / `OblCtxInner` typestates with constructors that allow only consistent additions) would make wrong-order use a compile error. Cost: more types, more transitions. Current cost of the runtime convention: zero bugs to date.

* **`Tactic::Raw` vs `Tactic::Named`.** The `Tactic` enum has a single `Raw(String)` variant covering both arbitrary-text closer tactics (`tactus_auto`, user overrides) and structurally-meaningful names. A split (`Raw(String)` for free-form text, `Named(LeanName)` for known prelude tactics) would let the pp / sanity layers treat them differently without parsing the string. Today everything goes through string equality; no bug has surfaced from the conflation.

* **`format_rust_loc` returning typed `RustLoc`.** The function returns a `String` formatted as `path:line:col`. Downstream `find_span_mark` parses it back to extract the line. A typed `RustLoc { path, line, col }` struct would eliminate the parse-format roundtrip. Bounded mechanical work; the current shape is small enough that the round-trip cost isn't visible.

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
and `otherwise` is the lexicographic-tail marker — `False` for
single-expression decreases, the inner level's CheckDecreaseHeight
call for lex `decreases a, b, …` (Verus's `recursion::check_decrease`
builds the recursive structure, so the lex shape composes through
our existing arm — pinned by `test_exec_call_recursive_lex_decreases`).
See `to_lean_sst_expr.rs`'s `CheckDecreaseHeight` arm for the
lowering; `render_checked_decrease_arg` handles the Bind(Let)
param-substitution wrapper Verus puts on `cur`.

Mutual recursion across an SCC works by construction — Verus's
recursion pass covers all cross-fn calls in the cycle the same way.

**Restrictions (rejected by `build_wp_call`):**

* **Trait-default-impl calls** — `is_trait_default: Some(true)`
  rejected (#56 follow-up). `Some(false)` is accepted (concrete
  impl on a trait that has a default).
* **Split-assertion calls** (`split: Some(_)`) — rejected.
* **Cross-crate callees** — rejected (fn_map is single-crate).
* **Cross-crate trait method decls** — when the resolved impl is
  `TraitMethodImpl { method, .. }` and `method` isn't in fn_map,
  rejected with a clear error.

**Accepted forms (with restrictions):**

* **Generic calls** (`typ_args` non-empty) — LANDED. `walk_call`
  composes value-param + type-param substitution.
* **Trait-method calls** — LANDED for `DynamicResolved` and
  `Static`/`Dynamic` paths that resolve to a same-crate trait or
  impl (#56). `build_wp_call` redirects the callee lookup to the
  resolved impl when `resolved_method` is `Some`; `pick_spec_source`
  uses the trait method decl's `require` (the impl's is empty —
  Verus rejects impl-side requires). For `ensure`, callers see the
  conjunction of trait's AND impl's ensures (#86 — impl-specific
  strengthening): the trait's spec is the weakest contract, the
  impl's spec is at-least-as-strong (Verus enforces impl ⇒ trait),
  and conjoining gives the caller the strongest available
  guarantee. `build_call_substitutions` builds substitution maps
  keyed on BOTH callee.params (impl) and spec_callee.params (trait)
  so either side's clauses substitute correctly even when trait
  and impl have textually different param names.
* **`&mut` args** — caller-side LANDED (#55, slice 1). `walk_call`
  introduces fresh existentials per `&mut` arg, substitutes
  pre-/post-state separately in the inlined ensures, and rebinds
  caller locals via `Let` frames after the ensures `Hyp`. Subset:
  - **`Loc(VarLoc(_))` and `Loc(Field(VarLoc(_)))` for single-
    variant structs.** `&mut x` (LANDED slice 1) and `&mut x.f`
    (LANDED #87) are accepted; the field case rebinds via Lean's
    structure-update syntax `let x := { x with f := <fresh> }`
    (no havoc-base + assume-other-fields-unchanged dance — Lean's
    type system enforces other-fields-unchanged structurally).
    `&mut v[i]` (Index L-value), deeper field paths (`&mut a.b.c`),
    multi-variant enum field mutation, and tuple field mutation
    (`&mut t.0`) remain deferred. Tuple specifically: Lean's
    structure-update syntax doesn't compose with `Prod` types
    ("expected structure" elaboration error), so a different
    encoding is needed (explicit ctor rebuild, e.g.
    `let t := (v, t.1)`).
  - **Legacy-mode `VarAt(p, Pre)` AND new-mut-ref-mode
    `MutRefCurrent`/`MutRefFuture` UnaryOps both handled.**
    New-mut-ref shapes are normalized back to the legacy shape
    via `normalize_mut_ref_in_{exp,stm}` (#95) before this slice's
    rewrite runs, so the same `VarAt(p, Pre) → Var(<p>_at_pre_tactus)`
    machinery handles both. Caller-side new-mut-ref (synthetic
    MutRef-typed local around the call) still deferred — see the
    Tier 3 entry below.
  - **Caller side LANDED in slice 1; callee side LANDED via #94.**
    Fns taking `&mut` params can have their OWN bodies verified
    by `tactus_auto`. Encoding (`exec_fn_theorems_to_ast` in
    `sst_to_lean.rs`):
    1. **SST-level rewrite of body + ensures**: at fn entry,
       `rewrite_varat_for_mut_params_in_stm` / `_in_exp` walks
       the body and ensures, replacing `ExpX::VarAt(x, Pre)` with
       `ExpX::Var(<x>_at_pre_tactus)` for every `&mut` param x.
       This disambiguates pre-state references (`*old(x)`) from
       post-state ones (`*x`) — the body's `*x = expr` lowers to
       `let x := expr` (Lean shadowing), so without the rewrite
       both would collapse to `Var(x)` and the let-shadow would
       silently make them equal (bug demonstrated in dev: ensures
       `*x == *old(x) + 1` reduced to `(x+1) = (x+1)+1`, false).
    2. **Initial OblCtx Let frame** per `&mut` param:
       `Let(<x>_at_pre_tactus, Var(x))` — captures the pre-state
       BEFORE any body modification can shadow `x`. The frame
       wraps the goal at theorem-emission time via `OblCtx::wrap`
       (outermost-first), so the body's WP sees `<x>_at_pre_tactus`
       in scope for any post-rewrite reference.
    3. **Requires NOT rewritten**: at fn entry, x IS the pre-state,
       so `*old(x) ≡ x` for requires evaluation; the natural
       `VarAt → Var` collapse in the SST renderer is correct
       there. Requires hypotheses go to theorem-level binders
       (`build_req_binders`) which are emitted before the body.
    4. **Symmetry with caller-side (#55)**: both paths use
       `varat_pre_name` from `expr_shared.rs` to produce the
       synthetic `<p>_at_pre_tactus` name — the rewrite-side and
       Let-binding-side stay in sync via shared helper, so a future
       contributor can't accidentally pick a different name in
       one place.
    5. **Upstream change**: `vir/src/lib.rs` promoted the
       `sst_visitor` module from `mod` to `pub mod` so we can use
       `vir::sst_visitor::map_exp_visitor` /
       `map_exps_in_stm_visitor` for the rewrite walkers (these
       in turn went from `pub(crate)` to `pub`). Comment at the
       module-promotion site cross-references #94.

    **Pinned by**: `test_exec_callee_mut_simple`,
    `test_exec_callee_mut_wrong_body` (negative — wrong body
    assignment fails postcondition), `test_exec_callee_mut_multiple_writes`
    (multiple `*x = ...` writes thread through Lean let-shadowing),
    `test_exec_callee_two_mut_params` (per-param Let frames don't
    collide), `test_exec_callee_mut_and_caller_both_tactus_auto`
    (end-to-end with both #55 caller-side and #94 callee-side
    active in the same crate — pins the shared `varat_pre_name`
    contract).

    **Still deferred**: `&mut v[i]` (Index L-value), deeper paths
    `&mut a.b.c`, multi-variant enum field mutation (Lean's
    structure-update syntax doesn't compose with multi-variant
    inductives), tuple field mutation `&mut t.0` (structure update
    doesn't work for `Prod` either — needs ctor rebuild instead).
    `&mut x.f` for single-variant structs LANDED via #87 using
    Lean's structure update — the encoding doesn't need havoc-base
    + assume-other-fields-unchanged because Lean's `{ x with f := … }`
    syntax structurally preserves all other fields.

    **New-mut-ref mode `MutRefCurrent` / `MutRefFuture` LANDED
    callee-side via #95** through a pre-rewrite normalization step
    that maps new-mut-ref SST shapes back to the legacy shape so
    #94's existing rewrite handles them. **Caller-side new-mut-ref
    still deferred** — synthetic MutRef-typed locals around exec
    calls don't go through param-set normalization. See the
    "&mut args on calls" Tier 3 entry for details.
* **Non-int decreases** — datatype-typed decreases via emitted
  `T.height` companion fn (see #54 in Tier 2). Int decreases work
  via the transparent-identity `height` for ints.

### `_tactus_d_old` aliasing across nested loops

`sst_to_lean::walk_loop` emits `let _tactus_d_old := D; …` inside every loop's maintain clause to capture the decrease measure pre-body. The name is literal, not gensym'd, so nested loops' `let _tactus_d_old` bindings shadow each other in Lean.

This is correct for the current architecture: the inner loop's shadow is confined to the inner's maintain conjunct, and the outer's `_tactus_d_old` reference lives in the outer's maintain conjunct (a sibling, not a descendant), so they never clash in scope. A gensym'd `_tactus_d_old_<loop_id>` would make the independence syntactically obvious but doesn't change semantics. Worth threading a counter through `walk_loop` if we ever refactor loops into a structure where scoping IS ambiguous — until then, the literal name is fine and keeps the generated Lean readable.

### Ret-substitution at call sites (#128)

`push_post_call_frames` in `sst_to_lean.rs` builds the post-call obligation context. The default ∀-path emits:

```text
∀ ret, ret_bound → ensures(ret) → let dest := ret; <continuation>
```

When the substituted ensures contains a top-level conjunct of the form `Eq(Var(fresh_ret), E)` or `Eq(E, Var(fresh_ret))` — i.e., `r == E` after applying caller-arg substitution — Tactus replaces the ∀-path with:

```text
E_bound → (ensures with ret := E, eq clause dropped) → let dest := E; <continuation>
```

The detection helper `extract_top_level_eq_for(conj, target)` walks the **top-level And-tree only** (peels SpanMark transparently; never recurses into Or, Implies, Forall, Exists, If, Let, Match — those don't uniquely determine the return value). On match it returns `(E, rest_conjunction)` where rest is the And of all OTHER conjuncts. Self-referential `r == r + 0` patterns are filtered via `expr_mentions_var(E, target)`.

**Why this matters.** Pre-#128, cond_setup goals (function-call-in-loop-cond from #114) had `∀ (_tactus_ret_N : Prop), _tactus_ret_N = (x > 0) → let tmp := _tactus_ret_N; tmp → …` shapes that `tactus_auto` couldn't close natively — `omega` rejects ∀-Prop, `simp_all` doesn't intro outer ∀s. The user-side override `intros; simp_all; omega` worked partially. Post-#128 the goal becomes `let tmp := (x > 0); tmp → …` (after Phase 5's let-zeta), which omega handles directly. Pinned by `test_exec_loop_cond_with_setup` (was Err with override; now Ok without).

**Beyond cond_setup.** Many existing tests have callees with `ensures r == E` shapes — those now go through the substitution path too, producing simpler generated Lean. All 267 pre-#128 tests still verify; the substituted goal shape is strictly more amenable to omega/simp_all than the ∀-shape was.

**Bound preservation.** `type_bound_predicate(callee.ret.typ, E)` is emitted as a Hyp in the substitution path, mirroring the `ret_bound` Hyp from the ∀-path. Numeric ret types (u8/i32/etc.) need this for downstream arithmetic; non-numeric (Bool, Prop, structs) get `None` and the Hyp is elided. So omega gets the same factual content — just expressed in terms of E rather than a fresh variable.

**Trait-method (#86) ordering.** When the conjunction is `(spec_ensures) ∧ (impl_ensures)` (impl-strengthened), the And-tree walk picks the first match in source order. `push_post_call_frames` orders spec first then impl, so the spec's `r == E_spec` wins; the impl's `r == E_impl` becomes part of `rest` and substitutes to `E_impl == E_spec` which Verus guarantees is consistent (`impl ⇒ trait`). simp_all closes the redundant equality.

**Conservative fallback.** When no `r == E` clause exists at the top level (e.g., ensures is `r > 0` only, or buried inside `Or(r == E, Q)`, or the ensures is empty), the function falls through to the original ∀-path. Pinned by `test_exec_call_no_ret_eq_falls_through` (callee with `ensures r > 0, r < 10` — still verifies via ∀).

**Tests** (4 new for the substitution path): `test_exec_call_ret_eq_substitution` (baseline `r == x + 1` ensures), `test_exec_call_ret_eq_with_extra_conjunct` (`r == E ∧ Q(r)` — Q(E) makes it into the rest_ensures Hyp), `test_exec_call_ret_eq_substitution_wrong_post` (negative — substitution doesn't make caller more permissive), `test_exec_call_no_ret_eq_falls_through` (no `r == E` → ∀-path stays).

### Known deferrals, rejected cases, and untested edges

A flat catalogue of things that don't work yet, organized by where in the pipeline they're rejected or where the gap lives. If a gap has its own detailed section elsewhere in this doc, it's cross-referenced rather than duplicated.

#### Statement-level forms rejected by `build_wp`

Each one returns `Err("… not yet supported")`; users get a clean rejection instead of silent pass.

* **`StmX::BreakOrContinue`** — `break` / `continue` inside loops. Blocks `while`-with-exit patterns. Enabling this also requires relaxing `cond: Some` (loops that break compile to `cond: None`) and accepting `invariant_except_break` invariants (at-entry but not at-exit).
* **`StmX::AssertBitVector`** — `assert by(bit_vector)`. Bitvector reasoning backend.
* **`StmX::AssertQuery`** — `assert by(…)` with specific tactics / queries. Would need to translate the `AssertQueryMode` into a Lean tactic choice.
* **`StmX::DeadEnd`** — markers Verus uses for unreachable code. Usually harmless to skip, but we reject rather than silently strip in case a future pipeline relies on them.
* **`StmX::OpenInvariant`** — atomic invariant opening for concurrent verification. Out of scope until concurrency support lands.
* **`StmX::ClosureInner`** — LANDED (#93). The `StmX::ClosureInner` variant gained a `ast_body: Expr` field populated by `ast_to_sst` (see `vir/src/sst.rs`), and Tactus reads it to render the closure as a first-class Lean lambda. The closure body's own verification scope (overflow checks etc.) emits as a separate set of theorems via `Wp::ClosureBody`'s walker, which pushes `∀ p : T, h_p_bound → ...` binders for each closure param. Pinned by `test_exec_closure_decl`, `test_exec_closure_decl_wrong_ensures`, `test_exec_closure_body_overflow_caught` (negative — soundness probe), `test_exec_closure_body_safe_arithmetic`.

#### Expression-level forms rejected by `sst_exp_to_ast_checked`

`sst_exp_to_ast_checked` is the primary validator+renderer for SST expressions; `check_exp` is a thin wrapper (`.map(|_| ())`). Single case analysis for both validation and rendering.

* **`UnaryOp` variants beyond `Not` / `Clip` / `CoerceMode` / `Trigger`** — the spec-fn path (`to_lean_expr`) handles more (BitNot, IntToReal, etc.) but the SST path on exec bodies is conservative; add as needed.
* **`BinaryOp::HeightCompare { … }`** — VIR's termination-height comparison (the fn-level wrapper; `CheckDecreaseHeight` below is the per-call-site SST form we DO lower).
* **`BinaryOp::Index(_, _)`** — LANDED (#91 closed). SST guarantees `BoundsCheck::Allow` (the bounds obligation is discharged by Verus's mode pass before SST). Tactus emits `lhs[Int.toNat rhs]!` (Lean's `getElem!`-based indexing — total in the type system, panics out-of-bounds; observationally fine because Tactus only verifies the goal and never executes the generated Lean). Requires `[Inhabited α]` for the element type, which holds for primitives and for non-generic user datatypes (we already emit `deriving Inhabited`). Side-effect fix: `Primitive::Array` type rendering drops the const-length argument (Lean's `Array α` is unary). Reachable from spec-mode `array_index(a, i)` (Verus builtin) and from exec-mode `a[i]` after Verus's bounds-check pass lowers `PlaceX::Index(_, _, _, BoundsCheck::Allow)` to `BinaryOp::Index(_, BoundsCheck::Allow)`. **Caveat**: exec-mode `a[i]` for slices/arrays in Rust desugars to `vstd::array::array_index_get` / `vstd::slice::slice_index_get`, which Tactus can't yet inline (cross-crate); user code that wants exec-mode array access through `tactus_auto` either needs vstd routing or a synthetic same-crate exec wrapper.
* **`BinaryOp::StrGetChar`** — string character lookup.
* **`BinaryOp::IeeeFloat(_)`** — IEEE float comparisons. Verus doesn't support `f32`/`f64` at all; this branch exists for completeness.
* **`ExpX::Ctor(..)`** — datatype constructors in exec fns. Blocks any exec code that constructs enum/struct values. Regression test: `test_exec_ctor_rejected`.
* **`ExpX::CallLambda(..)`** — LANDED (#93) for spec-closure calls (`f(x)` where `f: spec_fn(_) -> _`). Renders as `App(f, args)` since Lean's `spec_fn(int) -> int` already maps to `Int → Int` via `typ_to_expr`'s Lambda arm. Mirrors the proof-fn path's `CallTarget::FnSpec` handling. Pinned by `test_exec_spec_closure_in_ensures`, `test_exec_spec_closure_in_requires`, `test_exec_spec_closure_in_ensures_wrong_body` (negative). Exec-mode closure calls (`identity(5)` for `let identity = |x: u8| x;`) are upstream-blocked — see "Upstream-blocked deferrals" below.
* **`ExpX::ArrayLiteral(_)`** — `[a, b, c]` literals. Verus rejects these upstream when slice indexing isn't wired, so the Err arm is unreached in practice.
* **`ExpX::Old(..)`** — `old(x)` (pre-state). Relevant for `ensures` that compare post-state to pre-state.
* **`ExpX::Interp(_)`** — only appears inside Verus's interpreter; an internal-bug rejection rather than a feature gap.
* **`ExpX::FuelConst(_)`** — internal-bug rejection (#84 closed). Produced exclusively by `vir::recursion::rewrite_rec_call_with_fuel_const`, which is only called from `vir::expand_errors` (Verus's Z3 SMT-error-expansion pipeline). Tactus doesn't traverse that pipeline, so this arm is structurally unreachable. Hitting it means Verus's pipeline drifted; the message points the reader at filing an issue. **Note**: `reveal_with_fuel(f, n)` (the user-facing Verus syntax) is *not* blocked by this arm — it lowers to `StmX::Fuel(..)`, which `build_wp` already passes through transparently. The Lean side has no fuel concept (spec fns are `@[irreducible] noncomputable def`); the Tactus equivalent of reveal-for-unfolding is `proof { unfold f }`. See "reveal_with_fuel and unfold in Tactus" below.
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
* **`lift_if_value` chain-lifts through multi-binder `Bind(Let)` (#119).** Multi-binder lets (`let (a, b) = expr; …`) unfold to a single-binder chain via `unfold_multi_binder_let` (#92), and `lift_if_value` recurses through the chain when each binder's `inner_body` is itself a `Bind(Let, …)` — lifting any if-in-rhs along the way. The recursion is gated on `inner_is_let_chain` for soundness: when `inner_body` is `If` at top level (e.g., the match-compilation shape `let _disc := proj(k); if _disc = 0 then …`), lifting would move the if's condition outside the let scope and produce an unbound reference. The case-split tactic handles those match-style ifs at the obligation level instead.

#### Loop-shape restrictions (rejected by `build_wp_loop`)

* **`loop_isolation: false`** — non-isolated loops (body sees outer context directly rather than via the invariant). Different verification semantics — would need a new `Wp::NonIsolatedLoop` variant or a havoc-based encoding mirroring Verus's outer-query shape (sst_to_air.rs:2701-2715). Out of session scope; #114 sub-feature 2.
* **Non-empty condition setup block — LANDED via #114 sub-feature 1.** Pre-#114 the rejection blocked `while` conditions that Verus's `expr_to_stm_opt` decomposed into setup-stmts + pure expr (notably function calls in cond, which need a temp for the call result). Post-#114, the cond_setup walks as a wp prefix in BOTH the maintain ctx (under `assume cond_exp` via `Wp::Assume`) AND the use ctx (under `assume ¬cond_exp` via `Wp::Hyp`), mirroring Verus's two-query encoding (sst_to_air.rs:2789-2797 + 2730-2737). Setup obligations (e.g., precondition checks for calls inside the cond) emit twice — correct per Verus. **Implementation note**: the negated cond goes through a new `Wp::Hyp { hyp: LExpr, body }` variant for already-rendered hypotheses, rather than synthesizing a fresh `¬cond_exp` Exp. The Wp::Hyp variant is the right shape because the negation is derived (not borrowed from the input SST); building it at LExpr level avoids the lifetime/Arc juggling that synthesizing an SST Exp would require. The Validated/Wp::Assume contract stays scoped to genuine SST borrows. **Closed via #128 (ret-substitution).** Pre-#128 the cond_setup encoding produced `∀ (_tactus_ret_N : Prop), _tactus_ret_N = (x > 0) → let tmp := _tactus_ret_N; tmp → …` shapes that `tactus_auto`'s default closer couldn't discharge — `omega` rejects ∀-Prop, `simp_all` doesn't intro outer ∀s. Users had a partial-workaround override `#[verifier::tactus_tactic("intros; simp_all; omega")]`, but even that left some obligations unsolved. Post-#128: when the callee's ensures uniquely determines the return value via `r == E`, codegen substitutes E for r directly in `push_post_call_frames`, eliminating the ∀-quantifier. The cond_setup goal becomes `let tmp := (x > 0); tmp → …` which omega closes natively. See "Ret-substitution at call sites (#128)" below for the full encoding. Pinned by `test_exec_loop_cond_with_setup` (now `Ok(())`, no override needed).
* **Lexicographic `decreases` — LANDED via #110.** Loop-level multi-expression measures (`decreases D1, D2, ...`) build the lex disjunction in `lex_decrease_obligation` (`sst_to_lean.rs`):
  ```
  (0 ≤ D1' ∧ D1' < D1_old)
    ∨ (D1' = D1_old ∧ ((0 ≤ D2' ∧ D2' < D2_old)
        ∨ (D2' = D2_old ∧ ... (0 ≤ Dn' ∧ Dn' < Dn_old))))
  ```
  which generalises the single-expression case (the eq tail collapses against an absent next level). The `0 ≤ Di'` lower bound on each level mirrors the fn-level `CheckDecreaseHeight` int fast-path; #129 closed the prior gap where loop-level emitted just `Di' < Di_old`. Per-loop, per-level d_old gensyms (`_tactus_d_old_<id>_<i>`) keep nested loops AND lex tiers structurally distinct. Pinned by `test_exec_loop_lex_decreases`, `test_exec_loop_lex_decreases_nondecreasing`, `test_exec_loop_decrease_int_expression_can_go_negative` (regression for #129). Fn-level lex decreases works through Verus's own `recursion::check_decrease` recursion (the `otherwise` field of CheckDecreaseHeight wraps the next level), pinned by `test_exec_call_recursive_lex_decreases`, `test_exec_call_recursive_lex_nondecreasing`.
* **`invariant_except_break` / `ensures` loop invariants** — LANDED via #89. `build_wp_loop` splits invariants by their `at_entry` / `at_exit` flags into entry-side (init theorems + maintain ctx hyp + body's continue_leaf) and exit-side (break_leaf + use ctx hyp) groups. `walk_loop` filters init emission to `at_entry = true` invariants and uses the corresponding entry/exit conjunctions in maintain/use frames. For `cond: Some(_)` loops (`while c { ... }`), Verus's lowering forces at_entry = at_exit = true so behavior is unchanged from the pre-#89 state; the split actually matters for `cond: None` (break-lowered) loops. Pinned by `test_exec_loop_invariant_except_break`, `test_exec_loop_invariant_except_break_init_fails`, `test_exec_loop_ensures_only`, `test_exec_loop_ensures_fails`.
* **Labeled `break`** — LANDED via #88. `WpLoopCtx` carries `label: Option<String>`; `build_wp` threads a `&[&WpLoopCtx]` stack (innermost-first) instead of `Option<&WpLoopCtx>`. `StmX::BreakOrContinue { label: Some(target), .. }` searches the stack by matching label. Pinned by `test_exec_loop_labeled_break` + `test_exec_loop_labeled_break_three_deep`. Labeled `continue 'outer;` is rejected by Verus upstream without `loop_isolation(false)` (which Tactus also doesn't support); the label-stack handles it in principle.

Accepted via #57: **`cond: None`** loops (the form Verus produces when lowering `while c { … break; … }` or `loop { … break; … }`). Maintain/use clauses drop the cond-gate in this case; break/continue in the body thread through `WpLoopCtx`.

#### Soundness trade-offs accepted (not pure bugs, but worth knowing)

* **Usize subtraction truncates silently** — see the usize/isize section above.
* **Usize arithmetic rarely verifies automatically** — bounds are emitted but `tactus_auto` can't discharge symbolic `< usize_hi`; users need custom `proof { … }` with `arch_word_bits_valid` case-split.
* **Char bound admits surrogates** — `c < 0x110000` covers U+0000..U+10FFFF but includes the UTF-16 surrogate range U+D800..U+DFFF. Verus / Rust's `char` also don't distinguish, so our bound matches their semantics. No downstream soundness impact within the same system.
* **`Wp` clone cost is exponential in nested if-branch depth** — both branches of `Wp::Branch` clone the outer `after` continuation. Same behaviour as the prior `BodyItem` shape; the DSL refactor didn't fix this. Fine for realistic code.
* **`_tactus_d_old` shadows in nested loops** — relies on scope to disambiguate; documented in its own section.
* **`substitute` alpha-renames on capture (#116, LANDED).** When the per-scope capture check finds a colliding binder (a free var of an active substitution value matching a binder name), `substitute` now generates a fresh name (`<base>_α<N>`), rewrites the binder + body in lockstep, then proceeds with the main substitution. Pre-#116 this case panicked with a "would capture a free variable" message; post-#116 it renames cleanly. Fresh names avoid every name appearing anywhere in body (free or bound), every free var of active substitution values, and every sibling binder name (multi-binder shapes). For dependent types like `∀ (x : Nat) (h : x > 0), …`, the rename also threads through subsequent binder types — the second binder's `x > 0` becomes `x_α1 > 0` when `x` renames. Pinned per binder kind: Let, Lambda, Forall, Exists, Match (both `Var` and `Ctor` patterns), plus dependent-type, sibling-preservation, freshness-collision-avoidance, and multi-binder-collision tests.
* **`Classical.propDecidable` opens all Props.** Added to `TactusPrelude.lean` so accessor-derived Props (from `datatype_to_cmds`'s synthesized `Type.isVariant`) decide in `if <prop> then … else …` contexts. Side effect: `decide` can't reduce through classical-only Props — `decide` loses some reducibility relative to a prelude without this. `tactus_auto` uses `omega` / `simp_all`, not `decide` directly, so no current impact. A future tactic relying on `decide` to compute through Prop formulas would need to be aware.
* **Tactus tactic-text prepending runs at theorem level, not locally.** When a user writes `assert(P) by { tac }` or `proof { have h := by tac }` inside a loop body (or any nested construct), the `have` is prepended to the THEOREM's tactic at theorem-start — before any `intro` of modified-var quantifiers. Variable references in the tactic resolve to the OUTER scope (fn param, not loop-local). For simple cases (e.g., `assert(x < 256) by { omega }` where `x` is a u8 fn param and the tactic only uses fn-level bounds) this works. For tactics that would need a loop invariant as a hypothesis, the invariant isn't in scope at theorem-tactic prefix. Known design limitation; a per-loop-scoped `have` would require per-loop tactic emission, which we don't have. Not tested end-to-end with tactics that depend on loop-local state.
* **Proof-block goal-modifying tactics affect the outer goal.** `proof { simp_all }` simplifies the entire theorem goal, not just a local sub-proof. Users coming from Verus's self-contained proof blocks may be surprised. Pinned by `test_exec_proof_block_goal_modifying_tactic`; the alternative (wrapping in a local `have _ : True := by <tac>`) breaks the common `have h : P := by tac` propagation case — which is the primary reason users write proof blocks.
* **`tactus_case_split` tries each user-datatype local in turn.** Takes a `closer` tactic argument and commits the first split where the closer closes ALL subgoals; restores state and tries the next candidate otherwise. Means a fn with multiple datatype locals — e.g., `(a: Foo, b: Bar)` — works regardless of which is the right scrutinee. Cost is O(n_candidates × closer_cost), bounded by the locals in scope. The `.height`-existence gate filters out `Int`/`Nat`/etc. so we don't case-split on primitives. Pinned by `test_exec_match_enum_with_int_args` (mixed enum + int locals).

#### User-facing features not tested (or possibly broken)

* **`proof { … }` blocks inside exec fns — LANDED (#49).** Covered by `test_exec_proof_block_user_tactic`. Caveats: tactic runs at theorem level (see Soundness trade-offs); goal-modifying tactics affect the whole goal.
* **`assert(P) by { tactics }` — LANDED (#50).** Covered by `test_exec_assert_by_user_tactic`.
* **`assume(P)` warnings** — DESIGN.md promises a "unproved assumption" warning. Not wired; `StmX::Assume` emits the hypothesis silently.
* **Return in the `else` branch of an if** (where `then` falls through) — ✅ covered by `test_exec_return_in_else_branch` (#121 partial).
* **Return inside a loop body** — ✅ covered by `test_exec_return_inside_loop` and `test_exec_return_inside_loop_with_break`. Pins the Wp DSL's fn-exit semantics (Return writes `ctx.ensures_goal` regardless of nesting or `loop_ctx`).
* **Loops modifying multiple variables** — ✅ covered by `test_exec_loop_three_modified_vars` (#121 partial). `quantify_mod_vars` handles arbitrary-arity modified sets; tested with 3 modified vars.
* **Nested if where each branch contains a different loop** — ✅ covered by `test_exec_nested_if_with_loops_in_both_branches` (#121 partial). Pins that distinct loop ctxs in distinct branches walk independently.
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
* **Generic datatype with uninhabited type param** (#108 edge). `Datatype.derives` is now unconditionally `["Inhabited"]`; for a user instantiation like `List<Empty>`, Lean would reject the auto-derived `Inhabited (List Empty)` synthesis at the call site (Empty has no Inhabited instance). The accessor's `[Inhabited A]` typeclass bound also wouldn't resolve. No realistic test exercises this; documented as a known limitation. If it comes up, the fix is conditional `deriving` based on whether each variant has at least one Inhabited-friendly construction.
* **Generic datatype with trait-bounded type params** (#108 edge). `enum Tree<A: Ord> { … }` declares a trait bound on `A`. `height_fn_for_datatype` and `multi_variant_accessor_defs` ignore `dt.typ_bounds` — bounds aren't threaded to the generated `T.height` / accessor defs. For datatypes whose height fn doesn't actually USE the bound (the common case — height is structural), this is fine. For datatypes where the bound matters at the Lean level, calls would fail typeclass synthesis. Untested.
* **Generic recursive datatype with cross-instantiation recursion** (#108 edge). `enum Mut<A> { Plain(A), Recurse(Mut<u8>) }` — the recursive arm has type `Mut<u8>`, not `Mut<A>`. `field_is_self_recursive` matches on `path == self_path` regardless of args, so it correctly identifies the recursion; `T.height` is generic over the type-arg, so `Mut.height rest` (with `rest : Mut u8`) elaborates via Lean's implicit inference. Should work but no test exercises this specific shape.
* **`Pattern::Or` with cross-branch capture in alpha-rename** (#116 edge). For a match arm with `(Var(x) | Ctor(y))` where one alt binds `x` and another `y`, and substitution would capture `x` only on the first alt, our `rename_in_pattern` walks both alternatives uniformly. The Lean spec for `Or`-patterns requires each side to bind the same variable set; a rename that touches one side's binder must touch the other's matching binder too. Our walker handles this correctly because the rename map is shared across the walk, but a degenerate `Or` with truly disjoint bindings (e.g., `(Var(x) | Wildcard)`) followed by a body that references `x` is well-formed Lean only when both alts bind `x`. Realistic Verus output doesn't produce this shape; we'd handle it correctly if it arrived.
* **Multi-line `def` signatures in `TactusPrelude.lean`** (#118 edge). `extract_prelude_names` is line-based — it expects `axiom NAME` / `def NAME` / `syntax "NAME"` etc. on a single line. A future prelude addition with `def name\n  : LongType := body` would not register the name. The pinned tests (`extract_prelude_names_recognises_current_prelude` etc.) catch the regression for currently-allowlisted names; a brand-new multi-line def would silently fail to be recognised until it surfaces as a sanity-check unresolved reference. Worth a parser robustness pass if the prelude grows.
* **Stale `LEAN_PATH` after `lake update`** (lake-bypass edge). `cached_lean_path_for_lake_project()` resolves once per test-binary process via `OnceLock`. If the user updates the lake project (adds/removes Mathlib packages) and re-runs tests in the same process, the cached `LEAN_PATH` won't reflect the new packages. Restart the test binary to clear. Documented in the harness's docstring.
* **`lift_if_value` chain-lift only fires for let chains** (#119 edge). When `inner_body` is `Match`, plain `Var`, or any non-`Bind(Let)` shape (other than top-level `If`, which is the rejected unsafe case), `lift_if_value` falls through to render-as-is. Conservative: can miss lift opportunities but never produces a wrong-scoped reference. The chain-lift gate `inner_is_let_chain` is the structural distinguisher.
* **Closures with user-written `requires` / `ensures`** — `|x: u8| requires x < 100 -> u8 { x + 1 }`. Verus's surface syntax for closure specs is finicky; we didn't manage to write a clean test. The body verification scope (Slice C of #93) DOES process inner closure specs via `exec_closure_body_stms` in principle, but no test pins this end-to-end.

#### Tactic / automation limitations

* **`tactus_auto`'s default toolbox is `rfl | decide | omega | simp_all | tactus_case_split`.** Exec-fn obligations needing `nlinarith`, `ring`, `polyrith`, `aesop`, `positivity`, etc. fall through to the `fail` branch — unless a per-fn override is set (see below). Proof fns *can* use any Mathlib tactic in their `by { … }` block.
* **Per-fn tactic override (LANDED, #81).** `#[verifier::tactus_tactic("…")]` replaces `tactus_auto` as the default closer for the marked fn's emitted theorems. The argument is any Lean tactic string (e.g., `"ring"`, `"nlinarith"`, `"first | tactus_auto | tactus_usize_bound"`). Doesn't affect `assert(P) by { user_tac }` sites — those always use the user-supplied tactic. Empty strings rejected at parse time.
* **`tactus_usize_bound` tactic (LANDED, #82).** Discharges goals over `usize_hi` / `isize_hi` (`2 ^ arch_word_bits` / `2 ^ (arch_word_bits - 1)`) by `rcases arch_word_bits_valid; subst; simp only [usize_hi, isize_hi]; first | decide | omega`. Composes via `tactus_first` so users can layer it: `#[verifier::tactus_tactic("first | tactus_auto | tactus_usize_bound")]`. Without this, USize/ISize arithmetic obligations needed manual `cases arch_word_bits_valid` blocks.
* **Mathlib auto-tactics unused by default for exec fns.** Exec-fn `tactus_auto` is intentionally minimal to keep verification predictable; extending the default toolbox is a design call. Per-fn override is the per-fn opt-in.

#### Architecture debts (working-but-not-ideal)

* **Two parallel expression renderers — shared leaves extracted, deeper unification rejected.** `to_lean_expr.rs` (~495 lines, proof fn / callee spec inlining) and `to_lean_sst_expr.rs` (~565 lines, exec fn bodies) render structurally different trees: VIR-AST's `Block`/`Match`/`Ctor`/`PatternX`/`PlaceX` don't cross to SST; SST's `CheckDecreaseHeight`/`CallFun::InternalFun`/flattened statement sequence don't cross to VIR-AST. The shared rules — op tables, constant rendering, `Clip` coercion direction, binder construction — live in `expr_shared.rs` so divergence is a compile error. Full unification (trait over source-expression type, or routing callee specs through SST) was investigated and rejected; see the dedicated § "Two parallel expression renderers" above for the analysis.
* **Two-pass over loop bodies.** `build_wp_loop` calls both `collect_modifications` and `build_wp` on the body; fusing would save a pass but entangles modifications with WP construction. Documented; left alone.
* **Sanity-check allowlist auto-derived from `TactusPrelude.lean` (#118).** `extract_prelude_names` parses the prelude text at first call and caches the result via `OnceLock`. Adding a new `axiom NAME` / `def NAME` / `noncomputable def NAME` / `syntax "NAME"` / `macro "NAME"` / `elab "NAME"` to `TactusPrelude.lean` automatically updates the sanity allowlist — no `sanity.rs` edit required. Pre-#118 the list was a hardcoded `matches!` arm prone to drift. Pinned by `extract_prelude_names_recognises_current_prelude` (the auto-derived set still contains every name the legacy hardcoded arm did) and `extract_prelude_names_handles_each_form` (each prelude declaration form is recognised).
* **Expected VIR variant list for coverage is hand-maintained.** `tactus_coverage.rs` lists variants we expect to see. Macro-deriving from the enum would need Verus-upstream `strum` derives — not feasible without vendoring changes.
* **`_tactus_d_old` not gensym'd** — see its dedicated section.
* **`OblCtx::with_frame` clones the whole `frames` Vec per call** — O(N²) memory across deeply-nested recursion (asserts inside branches inside loops). Realistic exec fns don't go deep enough for this to matter; switching to `Rc<im::Vector<_>>` (structural sharing) would fix it without changing the API. Documented inline at the function site.
* **`substitute` boilerplate (#98) — evidence is mounting.** Per-variant dispatch now duplicated across **five** ExprNode walkers (`substitute_impl`, `collect_free_vars`, `collect_all_names` (#116), `strip_span_marks`, plus `mentions_free_var` as a thin wrapper) and **two** Pattern walkers (`pattern_bound_names_impl`, `rename_in_pattern` (#116)). Each new walker reinforces the case: by 2026-05-04 we'd hit the duplication 3 times in a single session (#116's `collect_all_names` + `rename_in_pattern`, plus the earlier-day simplify pass that exposed `mentions_free_var`). The first time it was "worth flagging." The third time in a session is "the pattern is now load-bearing." A `walk_children` helper or visitor-pattern abstraction would collapse ~300 lines to ~50, AND make adding an ExprNode variant a single-edit operation. Still flagged as #98; the cost/benefit threshold has shifted toward "do it" — likely the right pick for a session focused on internal cleanup rather than features.
* **CheckDecreaseHeight Assert-before-Call ordering — covered structurally** (`build_wp_block_preserves_assert_before_assume_ordering`, `build_wp_block_preserves_three_stmt_ordering`). The pass-ordering invariant reduces to "`build_wp` preserves `StmX::Block` source order in the Wp tree's left-to-right shape" — pinned with simple Assert/Assume stmts (no fn_map dependency). The CheckDecreaseHeight `cur` arg shape is separately pinned by `full_check_decrease_height_shape_pinned`.
* **No test that `WpCtx::new` rejects an Err-form req/ensure cleanly.** We have `test_exec_ctor_rejected` for body-path Ctor, but no direct test that a `requires Ctor(...)` clause produces the WpCtx::new Err path (vs. panicking or passing through). Low risk — the validation logic is shared with the body — but a regression guard would be cheap.
* **`lift_if_value` chain-recursion landed via #119.** Multi-binder lets (`let (a, b) = …; …`) unfold via `unfold_multi_binder_let` (#92) to a single-binder chain, and `lift_if_value` now recurses through the chain (gated on `inner_is_let_chain` for safety) so ifs in any binder's rhs lift to goal level. The match-compilation shape (`let _disc := proj(k); if _disc = 0 then …`) intentionally falls through to render-as-is — its if condition references the let-bound var, so lifting would break scoping. Pinned by `lift_if_value_multi_binder_let_with_if_rhs`.
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

  **Generic datatypes (#108, LANDED).** `enum List<A> { Nil,
     Cons(A, Box<List<A>>) }` and similar shapes now work end-to-
     end. `decrease_height_datatype` accepts any `Datatype(Path,
     args, _)` regardless of `args` length; `field_is_self_recursive`
     matches when the field's path equals the parent's regardless
     of args (recursion is on the structure of the datatype, not
     on A). `height_fn_for_datatype` emits `def T.height {A : Type}
     : T A → Nat | …` — implicit type-param binders go BEFORE the
     `:` (via `DefCurried.binders`, new field) so Lean's equation
     compiler infers A from the value pattern. Wrapping `∀ {A},`
     INSIDE the type expression breaks elaboration: equations would
     try to match the implicit slot and `List.Nil` would be typed
     as `A : Type` instead of `List A`.
     Accessor defs gain `[Inhabited A]` instance binders per type
     param so the unreachable-arm `default` fallback resolves;
     `deriving Inhabited` on the datatype itself becomes
     unconditional (Lean auto-derives `[Inhabited A] → Inhabited
     (List A)`). Pinned by `test_exec_call_recursive_generic_datatype`
     and `test_exec_call_recursive_generic_datatype_nondecreasing`.

  **Explicit deferrals (still rejected with clear message):**
  - **Mutually recursive datatype SCCs.** Height fns would need
    a `mutual` block; currently emitted standalone, which Lean
    rejects for cross-type recursion. Defer until a real user
    case motivates the plumbing.
  - **Recursive function fields** (`struct S { f: FnSpec(int) →
    Option<S> }`). Verus has a special axiom
    (`recursive_function_field` in `datatype_height_axioms`) for
    this; we don't mirror it.
  - **Lexicographic `decreases a, b` — LANDED via #110.** See
    "Loop-shape restrictions" entry above for the encoding.

##### Tier 3 — bigger slices (~1 week each)

* **`&mut` args on calls (#55) — caller-side LANDED.**
  `walk_call` introduces a fresh existential `_tactus_mut_post_<id>`
  per `&mut` arg (the post-call value), substitutes
  `varat_pre_name(p) ↦ caller_arg` (pre-state) and `p ↦ Var(fresh)`
  (post-state) in the inlined ensures, then rebinds the caller's
  local to the fresh value via a `Let` frame placed AFTER the
  ensures `Hyp` so subsequent obligations see the post-call value.

  **VarAt rewrite via local visitor.** `*old(x)` syntax → VIR-AST
  `VarAt(p, Pre)` for `&mut` params. The renderer collapses
  `VarAt(_, _) → Var(_)` globally — correct for non-mut params and
  loop ensures' at-entry refs, but it would break `&mut`
  substitution by aliasing pre-state with post-state. Fix:
  `rewrite_varat_for_mut_params` walks the VIR-AST `Expr` BEFORE
  rendering and renames `VarAt(p, Pre)` to `Var(<p>_at_pre_tactus)`
  scoped to the `&mut` param name set. The renderer stays
  unchanged for everything else. (Initial attempt to make the
  renderer distinguish `VarAt` globally failed 54 tests because
  loop ensures rely on the collapse.)

  **Aliasing**: two `&mut` args to the same call must be distinct.
  Rust's borrow checker guarantees this upstream, so we don't
  check.

  **Tests** (all positive except where noted):
  - `test_exec_call_mut_arg`: single `&mut` arg from tactus_auto
    caller into Verus-Z3-verified callee.
  - `test_exec_call_mut_arg_wrong_post`: caller's ensures has +2
    instead of +1 → `(postcondition)` failure. Pins that
    substitution doesn't alias pre/post.
  - `test_exec_call_mut_arg_requires_violated`: caller's `< 200`
    weaker than callee's `*old(x) < 100` → `(precondition)`
    failure. Exercises CallPrecondition theorem path.
  - `test_exec_call_mut_arg_field_rejected` (Err): `&mut h.val`
    rejected with pointed error (extract_simple_var_ident-fail
    path).
  - `test_exec_call_two_mut_args`: two `&mut` args at the same
    call site exercise the stacked-frames encoding.

  **Callee-side body verification LANDED via #94.** Implementation
  details are in the bullet at the top of the §"Tier 3 — `&mut`
  args on calls" block above (the slice 1 description was updated
  in place). High-level summary: SST-level rewrite of body+ensures
  to rename `VarAt(x, Pre)` → `Var(<x>_at_pre_tactus)` for &mut
  params; initial OblCtx Let frame `let <x>_at_pre_tactus := x`
  binds the pre-state at fn entry. Mirrors the caller-side
  encoding (#55) and shares the synthetic name via
  `varat_pre_name` in `expr_shared.rs`.

  **`&mut x.f` LANDED via #87.** `extract_mut_target` recognises
  the field shape `Loc(UnaryOpr(Field, base))` (with transparent
  Box/Unbox/CoerceMode wrappers peeled around `base`) for single-
  variant structs. The post-call rebind uses Lean's structure-update
  syntax: `let x := { x with field := <fresh_post> }`. The "all
  other fields unchanged" property is automatic from the syntax —
  no separate havoc-base + assume-other-fields-unchanged dance.
  `MutTargetRaw::{Var, Field}` discriminates the shapes;
  `MutArgInfo.field_path: Option<String>` carries the field name
  through to `push_post_call_frames` Phase 4.

  **Explicit deferrals (still rejected in `build_wp_call`):**
  - **`&mut v[i]`** (Index L-value), **deeper paths** (`&mut a.b.c`),
    **multi-variant enum field mutation**. The single-variant gate
    in `extract_mut_target` catches the multi-variant case
    explicitly (Lean's structure-update syntax doesn't compose with
    multi-variant inductives). Deeper paths and Index need separate
    encodings (Index in particular needs a way to express the array
    "one-element-changed" property).
  - **New-mut-ref mode (`UnaryOp::MutRefCurrent` /
    `MutRefFuture`) — LANDED via #95 (callee-side body
    verification).** A pre-rewrite normalization step
    (`normalize_mut_ref_in_{exp,stm}` in `sst_to_lean.rs`) maps
    new-mut-ref SST shapes back to the legacy shape (`Var` /
    `VarLoc` / `VarAt(_, Pre)`) at fn entry, then #94's existing
    `rewrite_varat_for_mut_params` step handles the rest unchanged.
    Rewrite table (for `x` in mut_param_names):
    | Phase | Op | Becomes |
    |---|---|---|
    | body | `MutRefCurrent(Var(x))` | `Var(x)` |
    | body | `MutRefCurrent(VarLoc(x))` | `VarLoc(x)` |
    | ensures | `MutRefCurrent(Var(x))` | `VarAt(x, Pre)` |
    | both | `MutRefFuture/Final(Var(x))` | `Var(x)` |
    `peel_to_var` strips Box/Unbox/MustBeFinalized/CoerceMode/Trigger
    to find an inner `Var`/`VarLoc`/`VarAt(Pre)`. The
    `is_mut_ref_par(p)` predicate covers BOTH legacy
    (`is_mut: true`, plain T typ) and new-mut-ref-migrated
    (`is_mut: false`, `MutRef<T>` typ) param shapes. Plus
    `type_bound_predicate` peels `TypX::MutRef` so the binder's
    bound comes from the inner T. Plus the synthetic
    `Assume(HasResolved(...))` injections from
    `resolution_inference` are dropped via
    `is_synthetic_assume_to_drop`. Pinned by
    `test_exec_callee_mut_simple_new_mut_ref`,
    `test_exec_callee_mut_noop_new_mut_ref`.

    **Caller-side new-mut-ref still deferred.** When `bump(&mut y)`
    is in a `tactus_auto` caller, Verus's encoding produces a
    synthetic MutRef-typed *local* (not a fn param) plus an assume-
    pre + assign-post wrapper around the call: `let mut_ref =
    ...; assume(MutRefCurrent(mut_ref) == y); bump(mut_ref);
    y = MutRefFuture(mut_ref);`. The MutRef* ops then wrap synthetic
    locals, not fn params, so the param-set normalization doesn't
    reach them. Pinned as Err by
    `test_exec_call_mut_arg_new_mut_ref_rejected`. Forward path:
    extend the "MutRef-typed name set" beyond fn params to include
    synthetic locals of MutRef type; or render `MutRef<T>` as a
    Lean structure (the "what would Lean do?" angle).

  **Why `varat_pre_name` lives in `expr_shared.rs`.** Both the
  rewrite (which produces the synthetic name) and the
  substitution-map key (which targets it) must agree on the
  string format. Centralizing in `expr_shared.rs` makes
  divergence a compile error rather than a runtime mismatch.

* **Trait-method calls (#56) — DynamicResolved LANDED.**
  When `StmX::Call::resolved_method = Some((resolved_fun, resolved_typs))`
  (Verus's `CallTargetKind::DynamicResolved`), `build_wp_call`
  redirects the callee lookup from `fun` (the trait method decl) to
  `resolved_fun` (the resolved concrete impl). `resolved_typs`
  becomes the type-args slice (Self is already filled in by Verus's
  resolution).

  **Spec source via `pick_spec_source`.** For
  `FunctionKind::TraitMethodImpl` callees, Tactus uses the TRAIT
  method decl's `require`. Verus rejects impl-side `requires`
  declarations (impl inherits trait's requires), so the impl's
  require is always empty.

  **Impl-strengthening of `ensures` LANDED via #86.** When the
  resolved impl strengthens the trait's `ensures` (e.g., trait says
  `r < 100`, impl says `r == 5`), the call site now sees the
  conjunction `(trait_ensures) ∧ (impl_ensures)`. Verus enforces
  `impl ⇒ trait` via its trait-impl-checking pass, so the
  conjunction is satisfiable and caller never proves something
  inconsistent. `build_call_substitutions` builds substitution maps
  keyed on BOTH `callee.params` (impl) and `spec_callee.params`
  (trait) — same arg values for both spellings of each param's
  name, so either side's clauses substitute correctly even when
  trait and impl have textually different param names (Rust allows
  this; the names are positionally aligned but textually
  independent). `push_post_call_frames`'s Phase 3 conjoins
  `spec_callee.ensure.0` with `callee.ensure.0` (when the resolved
  impl differs from the trait method decl, detected via
  `Arc::ptr_eq` on the `Fun` field). Pinned by
  `test_exec_call_trait_method_impl_strengthens` (caller relies on
  the impl-specific `r == 5`, not just the trait's `r < 100`) and
  `test_exec_call_trait_method_wrong_impl_strengthening` (caller
  asserts the wrong impl's value — fails postcondition, pins that
  the strengthening comes from the resolved impl, not some other
  impl of the same trait).

  **Aesthetic note (not a correctness issue).** When trait and
  impl have identical `ensures` (a common case — impl just repeats
  the trait), the conjunction duplicates the clause:
  `(r == x) ∧ (r == x)`. `omega`/`simp_all` handle this fine; the
  generated Lean is slightly verbose but unambiguous. A future
  refinement could detect equivalent clauses and dedup, but the
  cost (syntactic comparison on VIR-AST expressions) outweighs the
  current readability cost.

  **Cross-crate traits rejected at build time.** If the resolved
  impl is `TraitMethodImpl { method, .. }` and `method` (the trait
  method decl Fun) isn't in `fn_map`, `build_wp_call` fails with a
  pointed error naming `#56` deferrals. The lookup itself is in
  `pick_spec_source` (called from `walk_call`); the validation is
  hoisted into `build_wp_call` so failures surface at codegen
  time, not as a panic.

  **`is_trait_default = Some(true)` LANDED via #96.** When the
  call resolves to the trait's default body (impl doesn't override),
  `resolve_callee` redirects to use `fun` (the trait method decl,
  which holds the default body and its specs) and `typ_args` (the
  call site's typ args, including the concrete Self) directly,
  rather than the synthesized `<impl>%default%<method>` wrapper
  that Verus's resolution produces. `Self` then resolves through
  the existing typ_args / typ_subst machinery — no Self-specific
  substitution needed. `pick_spec_source` returns the trait method
  decl (its `FunctionKind::TraitMethodDecl` arm gives `Ok(callee)`),
  so `callee == spec_callee` and #86's impl-strengthening path is a
  no-op (there's no separate impl — the default IS the body). Pinned
  by `test_exec_call_trait_default` (basic), `test_exec_call_trait_default_wrong_ensures`
  (negative), `test_exec_call_trait_default_with_args` (default with
  precondition + non-self params), `test_exec_call_trait_default_overridden`
  (impl OVERRIDES the default; pins that we still go through the
  concrete-impl path with #86 strengthening when an override exists).

  **Explicit deferrals (still rejected with clear messages):**
  - **`CallTargetKind::Dynamic`** (truly dynamic dispatch through
    `dyn Trait`) is indistinguishable from `Static` at the SST
    level — both have `resolved_method: None`. Currently falls
    through to the existing fn_map lookup of `fun`; if the trait
    method decl is in the same crate, the lookup succeeds and
    substitution proceeds via the trait's spec. For cross-crate
    `dyn Trait` calls, the lookup fails with the cross-crate
    error.
  - **`CallTargetKind::ExternalTraitDefault`** also falls through
    to the existing path.

  Tests: `test_exec_call_trait_method` (basic, was rejected),
  `test_exec_call_trait_method_requires_violated` (negative —
  trait's requires becomes the precondition obligation),
  `test_exec_call_trait_method_two_impls` (same trait, two impls;
  caller relies on trait-level contract),
  `test_exec_call_trait_method_with_args` (trait method with
  non-self args; param-name alignment between trait decl and
  impl).

* **`break` / `continue` — LANDED.** Unlabeled break/continue
  via #57; labeled `break 'outer;` via #88. `Wp::Loop::cond` is
  `Option<&Exp>` — `Some` for simple `while c { … }`, `None` for
  Verus's break-lowered form (`while c { … break; … }` → `loop
  { if !c { break; } … }`).
  `WpLoopCtx { label, break_leaf, continue_leaf }` threads through
  `build_wp` as a `&[&WpLoopCtx]` stack (innermost-first). Each
  loop body extends the stack with its own ctx.
  `StmX::BreakOrContinue { label, is_break }` emits `Wp::Done(leaf)`:
  unlabeled resolves to `stack[0]`; labeled searches the stack
  by `label`. Tests: `test_exec_loop_with_break`,
  `test_exec_loop_with_continue`,
  `test_exec_loop_labeled_break`,
  `test_exec_loop_labeled_break_three_deep`.
  Still rejected: labeled `continue 'outer;` (Verus upstream
  needs `loop_isolation(false)` — which we don't support either;
  the label-stack handles it in principle if the Verus
  restriction is lifted); `invariant_except_break` / `ensures`
  invariant classifications (#89; only `at_entry = at_exit = true`
  accepted, which matches what `invariant x <= n;` produces by
  default).

* **Closures (#93) — LANDED.** Three slices delivered:

  **Slice A — Spec-closure calls (`ExpX::CallLambda`).** When a
  `tactus_auto` exec fn applies a spec-closure parameter
  (`f(x)` for `f: spec_fn(_) -> _`), the call lowers to Lean
  `App(f, args)`. Lean's `Int → Int` (the `typ_to_expr` rendering
  of `spec_fn(int) -> int`) is a first-class function type, so
  no special encoding needed beyond a normal application. Mirrors
  the proof-fn path's `CallTarget::FnSpec` handling. Pinned by
  `test_exec_spec_closure_in_ensures`,
  `test_exec_spec_closure_in_requires`,
  `test_exec_spec_closure_in_ensures_wrong_body` (negative).

  **Slice B — Closure declarations via preserved AST body.**
  Verus's SST normally throws away the closure's `ExprX::NonSpecClosure`
  body (replacing it with `StmX::ClosureInner.body: Stm` plus a
  synthetic `Assume(forall|x| ClosureReq(cid, x) ↔ ... ∧
  ClosureEns(cid, x, body(x)) ↔ ...)`). For Lean we want a
  first-class function value, so we extended `StmX::ClosureInner`
  with an `ast_body: Expr` field populated by `ast_to_sst`. Tactus
  reads it via `closure_lambda_from_ast` and emits a `Wp::LetRaw(cid,
  fun (p : T) => body, after)` (built via the `closure_decl_wp`
  helper to assemble the nested Wp shape clearly). The synthetic
  spec assume is dropped via `is_synthetic_assume_to_drop`'s
  closure-spec recognizer (`contains_closure_internal_fn`).
  Synthesized `anonymous_closure%` datatypes are skipped in
  `generate.rs` — Z3 needs them as opaque types for predicate
  identities, but Lean uses first-class function types and a
  zero-variant inductive fails `deriving Inhabited`. Pinned by
  `test_exec_closure_decl`, `test_exec_closure_decl_wrong_ensures`
  (negative), `test_exec_closure_zero_args`, `test_exec_closure_nested`,
  `test_exec_closure_captures_local`, `test_exec_closure_inside_loop`,
  `test_exec_closure_inside_if`.

  **Slice C — Closure body verification scope.** The closure
  body's own verification (overflow checks etc. inside the
  closure body's arithmetic) emits as theorems via `Wp::ClosureBody
  { closure_params, body, after }`. Walker pushes
  `∀ p : T, h_p_bound → ...` for each closure param via
  `push_mod_var_frames` (same helper used for loop modified-vars),
  then walks `body`'s Wp. Without this slice, `let f = |x: u8|
  x + 200; ...` was silently accepted even though `x + 200`
  overflows for `x ≥ 56` — a real soundness gap that's now caught.
  Pinned by `test_exec_closure_body_overflow_caught` (negative —
  catches the previously-silent gap), `test_exec_closure_body_safe_arithmetic`
  (positive — `|x: u8| x / 2` is generically sound),
  `test_exec_closure_multi_arg_overflow` (negative — `|x, y| x + y`
  overflows for u8).

  **Why this is structural and not SMT-shaped.** Z3's encoding
  uses `cid` as an opaque function symbol + axiomatized via
  `forall|x| ClosureReq(cid, x) ↔ ...` + `ClosureEns(cid, x,
  body(x)) ↔ ...`. The body's structure isn't visible at call
  sites — only the predicates. Lean's first-class function types
  let us bind `cid := lambda` directly, and the predicates
  collapse: `ClosureReq(cid, x)` becomes "the lambda's requires
  applied to x"; `ClosureEns(cid, x, output)` becomes
  `output = cid x`. Same fact, structural rather than asserted.
  See § "What doesn't have to mirror Verus's encoding".

  **Still deferred (closure follow-ups):**
  - **Exec-mode closure CALLS (`add_one(5)` for an exec closure)**
    — Verus translates `f(x)` to
    `vstd::pervasive::exec_nonstatic_call(f, (x,))`, which Verus's
    resolution rejects. Even with vstd, the inlined ensures use
    `BuiltinSpecFun::ClosureReq` / `ClosureEns` in spec position,
    which Tactus currently treats as synthetic-to-drop (correct
    for closure-decl scope, would need lifting for call sites).
    See § "Upstream-blocked deferrals". Pinned by
    `test_exec_closure_call_unsupported_upstream`.
  - **Closures with user-written `requires` / `ensures`
    (`|x: u8| requires x < 100 -> u8 { x + 1 }`).** The body
    verification scope COULD pick these up via
    `exec_closure_body_stms` (which already processes them into
    inner asserts), but no test pins this — the Verus surface
    syntax is finicky and we didn't get it to parse cleanly in
    a tactus_auto fn. Untested.
  - **`StmX::ClosureInner.ast_body` shape-drift — pinned** by
    `closure_lambda_from_ast_rejects_non_closure_ast_body`. The
    helper rejects a non-`ExprX::NonSpecClosure` ast_body with a
    documented error naming `ast_to_sst` as the fix site. If a
    future rebase changes the population path (e.g., stores `body`
    alone instead of the full closure expr, or forgets the field),
    the unit test fires before e2e regressions surface.

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

#### Upstream-blocked deferrals

These are deferred not by Tactus design choice but by upstream Verus pipeline state. Lifting any of them depends on Verus-side work first; pinned tests document the current rejection so a future rebase that lifts the upstream limitation surfaces here as a flippable Err.

* **Exec-mode closure calls (`identity(5)` for an exec closure)** — Verus translates `f(x)` to `vstd::pervasive::exec_nonstatic_call(f, (x,))`. Without vstd imported, the call is rejected at Verus's resolution level with `vstd::pervasive::exec_nonstatic_call is not supported`. Even with vstd, `exec_nonstatic_call` is `external_body` with `requires`/`ensures` that use `call_requires` / `call_ensures` builtins, lowering to `BuiltinSpecFun::ClosureReq` / `ClosureEns` — the same shapes Tactus drops as synthetic in closure-decl scope. To verify call sites, those builtins would need a *spec-position* resolution (currently they only appear inside synthetic spec assumes that we drop): `ClosureReq(f, args)` → `True` (or the closure's actual requires applied to args), `ClosureEns(f, args, output)` → `output = f args` for the renderer's purpose. Pinned by `test_exec_closure_call_unsupported_upstream`.
* **Cross-crate trait method decls** — when `walk_call`'s `pick_spec_source` resolves to a `TraitMethodImpl { method, .. }` and `method` (the trait's decl `Fun`) isn't in `fn_map`, Tactus rejects with a pointed error. This is technically Phase-3 (`CrateDecls.lean`) work, but we list it here too because the user-facing symptom is the same shape: the limitation isn't in Tactus's encoding, it's in the cross-crate inlining infrastructure.
* **Cross-crate `dyn Trait`** — the `Dynamic` `CallTargetKind` (truly dynamic dispatch) falls through to the existing fn_map lookup; same-crate works, cross-crate hits the cross-crate rejection.

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
* **The `arch_word_bits` / `usize_hi` / `isize_hi` prelude names.** Our codegen emits bare `Var` references to these; the prelude provides the axioms/defs. If the prelude is swapped for a different environment, the references break. Kept in sync via `sanity.rs`'s `cached_prelude_names()` helper, which auto-derives the allowlist from `TactusPrelude.lean` (#118) — adding new prelude defs no longer requires a separate sanity-allowlist edit.
* **Verus's `StmX` destructures are `..`-free** in our code. Any field addition to `StmX::Assign` / `Return` / `Loop` / `Call` causes a compile error that forces audit. This is the compile-time defence in the upstream-robustness triangle.
* **Verus lowers `while cond { … break; … }` to `cond: None` + an inserted `if !cond { break; }` prelude in the body.** Our `Wp::Loop` accepts both `cond: Some(_)` (no break) and `cond: None` (break-lowered) shapes; `walk_loop` only emits a `cond` gate when `Some`. If Verus changes to keep `cond: Some` with the break preserved in the body, our encoding still produces valid goals but with a spurious `∧ cond` gate that may over-constrain the invariant proof. **No shape-drift test today** — speculative, would surface as a regression in `test_exec_loop_with_break` if Verus's lowering changes.
* **Verus's `auto_proof_block` pass always wraps non-empty content.** The pass synthesises `proof { ... }` blocks around every `assert(P)` / `assert(P) by { tac }` site so they're parsed as proof-mode. We distinguish user-written `proof { }` (semantically meaningful, routed to `Wp::AssertByTactus` with `cond: None`) from auto-wrapped ones via HIR-body emptiness in `rust_to_vir_expr.rs` — auto-wrapped blocks have non-empty HIR bodies, user-written empty blocks don't. **Guarded by `test_exec_auto_proof_block_not_tactus`** which exercises the auto-wrap path and confirms it doesn't trigger Tactus mode.
* **`get_ghost_block_opt` returns `Some(GhostBlockAttr::Proof)` for user-written `proof { }` blocks.** Our `enclosing_fn_is_tactus_auto` + ghost-block-attr detection in `fn_call_to_vir.rs` relies on this attribute classification. If Verus changes how it tags ghost blocks (e.g., a new `GhostBlockAttr::TactusProof` variant, or distinguishing wrapped vs unwrapped at this layer), we'd silently stop detecting user-written proof blocks and route them to the wrong path. **No shape-drift test** — would manifest as `test_exec_proof_block_user_tactic` regressing.
* **`TypX::Boxed` / `TypX::Decorate` are the canonical transparent wrappers for self-referential datatype fields.** Shared via `peel_typ_wrappers` (in `to_lean_sst_expr.rs`), used by `is_int_height`, `decrease_height_datatype`, and `field_is_self_recursive`. Mirrors `typ_to_expr`'s rendering (which peels both to produce Lean-level types). If Verus adds a new transparent wrapper for Rust `&Self` / `Box<Self>` / `Arc<Self>` / etc., one edit to `peel_typ_wrappers` updates all three call sites — without it, recursive-field detection would fail silently (field treated as non-recursive → `height = 1` for the variant → false termination obligation → recursion verifies where it shouldn't). **No shape-drift test** — would manifest as `test_exec_call_recursive_datatype_termination` regressing past the current "match-case-split" gap into a verified-but-wrong state.

### `Wp` — WP DSL (landed)

The earlier `BodyItem` hand-rolled enum + `build_goal_with_terminator(items, rest, terminator, ctx)` positional recursion was replaced by a proper WP algebra. `Wp<'a>` in `sst_to_lean.rs`:

```rust
enum Wp<'a> {
    Done(LExpr),                                       // terminator
    Let(LeanName, Validated<'a>, Box<Wp<'a>>),         // continuation wrappers
    LetRaw { name, value: LExpr, body },               // (closure cid := lambda)
    ClosureBody { closure_params, body, after },       // closure body verification scope
    Assert(Validated<'a>, Box<Wp<'a>>),
    Assume(Validated<'a>, Box<Wp<'a>>),
    Hyp { hyp: LExpr, body: Box<Wp<'a>> },             // already-rendered hypothesis
    AssertByTactus { cond: Option<Validated<'a>>, tactic_text, body },
    Branch { cond: Validated<'a>, then_branch, else_branch },
    Loop {
        cond: Option<Validated<'a>>, invs, validated_invs, inv_kinds,
        decrease: Vec<DecreaseLevel<'a>>, modified_vars, body, after,
    },
    Call {
        callee, spec_callee, args: Vec<Validated<'a>>, typ_args,
        dest, call_span, mut_args, after,
    },
}
```

**`Wp::Assume` vs `Wp::Hyp`** — both walk into a `CtxFrame::Hyp` push, but differ in the source of the LExpr:

* `Wp::Assume(Validated<'a>, _)` carries a validated SST `Exp` (a borrow into the input SST). The walker calls `lower(v)` to render. Used by `StmX::Assume`, the cond hyp inside `build_wp_loop`'s body wrap, etc. — anywhere the hypothesis is *derived from an SST node*.
* `Wp::Hyp { hyp: LExpr, _ }` carries an already-rendered LExpr. Used for *synthesized* hypotheses with no SST origin — the canonical case is the negated cond_exp from #114's cond_setup transform, which is built via `LExpr::not(lower(cond_validated))` rather than synthesizing a fresh `¬cond_exp` SST `Exp`. Keeping the two variants distinct preserves `Validated`'s borrow contract: the type guarantees its `&'a Exp` came from the input SST, not from a fresh allocation.

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

When landing non-trivial work, run review lenses against the diff
before calling it done. Each lens is a different *question*; each
question is non-redundant; each catches a class of issue the others
miss. A single "read it over" pass catches almost none of them.

The list below grew lens-by-lens across sessions — new lenses get
added when an existing review pass surfaces something the named
lenses didn't ask about. Run as many as feel useful; the typical
cleanup pass uses the first 5 and runs 10-30 minutes per landing,
catching 3-5 real issues even on code that looked fine.

#### Core lenses

**1. Linus hat.** Role-play a grumpy maintainer. Look for clever
abstractions that make code harder to understand, defensive code
for scenarios that can't happen, flag soup (`Option<_>` + `bool`
fields that can never take independent values), bad naming,
orphaned docstrings, functions whose signature lies about what
they do. *Canonical hits*: `typ_inv_exps` smuggling the asserted
condition (field's name didn't match its content); `MutArgInfo`'s
`(caller_var, field_path: Option<String>)` flag-soup before
embedding `MutTargetRaw`.

**2. FP lens.** What's mutable that could be immutable? What's
stateful that could be a parameter? Common hits: `RefCell` on
supposedly-pure functions, shared mutable state across module
boundaries, accumulators that could be folds. *Canonical hit*:
`WpCtx::tactus_asserts: RefCell<_>` making `walk_obligations` lie
about its purity → replaced with `collect_tactus_haves` two-pass
walk.

**3. Comprehensive coverage.** What code paths have no test?
Variants of a new enum that aren't exercised, edge cases at the
boundaries, negative tests for claimed-rejections, interactions
between two features. *Canonical hit*: missing regression tests
for labeled-break-rejected, nested-loop inner-break, return-
inside-loop-with-break after #57 landed.

**4. Upstream-brittleness.** What breaks silently if Verus changes
X? See § "Upstream-robustness patterns" above for the triangle of
defences (explicit field destructures, shared helpers for implicit
shapes, shape-drift tests); the review asks "have we used them?"
*Canonical hit*: `test_exec_auto_proof_block_not_tactus` guards
against Verus's `auto_proof_block` ever generating empty synthetic
blocks (which would mis-classify as Tactus).

**5. Documentation / deferrals.** What's landed but not documented?
Counterintuitive behaviour that needs a caveat? Deferrals in code
comments that aren't in this document's deferrals catalogue? Stale
comments asserting rejected features that are now accepted?
*Canonical hit*: proof-block goal-modifying-tactic semantics worth
pinning with a test and a DESIGN.md caveat after #49 landed.

#### Additional lenses (each surfaced findings the core five missed)

**6. Reasoning-clarity lens.** *If I came back in a month, what
would slow me down?* Different from Linus-hat — not bugs or smells,
just code that worked but was hard to read. *Canonical hits*:
`walk_call`-as-200-line-mixed-phases (split into 3 named helpers);
the `pick_spec_source` `_ =>` catch-all that worked but encoded a
brittle assumption (made exhaustive).

**7. Error-message quality lens.** Every `Err(...)` message reviewed
for the convention *"answer (a) what did the user write?, (b) is
there a workaround?, (c) is this tracked?"* *Canonical hit*: 13
messages using internal type names (`FuelConst`, `OpenInvariant`)
instead of surface syntax (`reveal_with_fuel`, `open_atomic_invariant!`).
Convention now applied uniformly.

**8. Identifier-conventions lens.** Reserved-name and gensym
conventions tend to grow across sessions with no single source of
truth. The lens asks: *what naming patterns has the codebase
accreted? are they documented?* Surfaced four conventions
(`_tactus_<role>_<id>` prefix, `<x>_at_pre_tactus` suffix,
`tactus_<name>` for user-visible tactics, bare names in
TactusPrelude) and two gensym mechanisms (`StmX::Loop::id` vs
`next_id()`). Documented in `expr_shared.rs` § "Reserved identifier
conventions".

**9. Simplify lens (reuse / quality / efficiency).** Cross-check for
newly-written code that could use existing helpers, hidden-state
smells, and missed early-return short-circuits. *Canonical hits*:
pure-rename `let warnings = assume_warnings;` (removed); over-broad
`pub` visibility on `WpLoopCtx` (narrowed); efficiency issue —
`rewrite_varat_for_mut_params` walked the entire AST even when its
set was empty.

**10. Right-way lens.** *This works — but is there a "right way" to
do it?* Different from Linus-hat (which catches bad shape) and
Simplify (which catches missed reuse). Catches code that's correct
and idiomatic-enough, but uses a low-level or Verus-mirroring shape
where a more meaningful or target-native shape would express the
same thing better. The question: *what does this code MEAN, and is
the shape it takes the most direct expression of that meaning?*
Two flavours:
- *Implementation level.* `Arc::ptr_eq(&callee.name,
  &spec_callee.name)` works as a "this is a trait-method-impl
  call" check, but it's pointer-identity proxying for a structural
  property. Right way: `matches!(callee.kind,
  FunctionKind::TraitMethodImpl { .. })` — the discriminant IS the
  meaning.
- *Encoding level.* See § "What doesn't have to mirror Verus's
  encoding". When Verus uses an SMT-style encoding (havoc-base,
  fresh existentials, conjoined preservation hypotheses), ask
  whether Lean's type system can make the property structural
  rather than asserted. #87's `{ x with f := v }` was this lens
  applied at design time.

**11. Rust-antipattern lens.** *Are we using `Arc`/`RefCell`/clones/
`Box<dyn>` where direct references or simpler ownership would work?
Are we storing pre-rendered output where a structural reference
would defer the work?* The lens has a high false-positive rate —
many `Arc` uses are required by upstream type design — but the
true positives are real. *Canonical hit*: `MutTargetRaw::Field`
stored a pre-rendered Lean field name (`String`) where a structural
`&FieldOpr` reference works. Asymmetric with `Var(&VarIdent)` which
already stored a structural ref. Changed to match.

**12. Edge-case lens.** *Anywhere we've deferred handling without
either tracking it explicitly or rejecting it explicitly?* Implicit
edge cases — silent acceptances of cases the implementation doesn't
actually handle — are the dangerous class. *Canonical hit*: the
single-variant gate for `&mut x.f` had `Dt::Tuple(_) => true`
(silently accept). Probe surfaced that Lean's structure-update
syntax doesn't compose with `Prod` — would have produced
elaboration errors at every tuple-field mutation. Gate flipped to
explicit rejection; documented in deferrals; rejection test added.

**13. Typed-invariant lens.** *Anywhere we're enforcing an invariant
via runtime check (`expect`, `unwrap`, `assert`, panic, runtime
discriminator) where the type system could carry the proof
structurally?* The audit batch (#99–#105) named this pattern; this
lens applies it as a review pass. *Canonical hits*: `walk_call`'s
`pick_spec_source(callee, &fn_map).expect(...)` where the lookup
was already validated upstream — moved to `Wp::Call` as a structural
field, removing both the runtime check and the dead `pick_spec_source`
helper.

**14. Regression-test lens.** *For every fix in this diff, is there
a test that would catch a similar bug class in the future?* Distinct
from the "Coverage" lens — Coverage asks about untested CODE PATHS,
this asks about untested BUG CLASSES. *Canonical hit*: `&mut` +
trait/impl differing-param-names interaction wasn't tested after
#86's union-key landing — added `test_exec_call_trait_mut_differing_param_names`.

#### Process

Land the work with tests passing, then run lenses 1–5 minimum.
Triage each finding (fix now / file follow-up / skip), do the
"fix now" list in a follow-up commit labelled "review (lens-name)".
Update this document for any caveat, deferral, or new lens that
surfaced.

When time allows, also run lenses 6–14. Even on code that passed
the core 5, additional lenses surface findings (today's session:
6 lenses run, 6 cleanup commits, 1 real bug found by the
edge-case lens). The lens list isn't exhaustive — when a review
pass surfaces a finding that doesn't fit any existing lens, the
question that surfaced it is itself a candidate new lens.

The pattern: each new lens is a new *question*, not a new *place
to look*. Review passes never reach a fixed point because the
questions are unbounded; what you do is run enough lenses that
the *known unknowns* are small.

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

### What doesn't have to mirror Verus's encoding

Tactus inherits Verus's pipeline through SST, but the *encoding* of obligations on the Lean side doesn't always have to mirror Verus's Z3-targeted encoding. Verus introduces specific patterns — havoc-base + assume-other-fields-unchanged for `&mut x.f`, fresh existentials for return values, explicit pre/post-state hypotheses — *because SMT needs them*. SMT solvers can't natively express "this struct's post-state has these specific fields and others unchanged"; the property has to be asserted as a conjunction of clauses.

When the target is Lean's dependent type theory, some of these encodings collapse. The canonical example is **`&mut x.f` (#87)**: DESIGN.md initially planned a havoc-base + assume-other-fields-unchanged encoding mirroring Verus's Z3 path. The actual implementation turned out to be one Lean expression: `let x := { x with f := <fresh> }`. Lean's structure-update syntax IS "all other fields unchanged" — the property is structural, not asserted. Ten lines of hypothesis become one line of syntax, enforced by elaboration rather than by proof.

**The discipline.** When designing a Tactus encoding, ask both:
1. *How does Verus do this?* — establishes correctness of the obligation shape.
2. *What would Lean do?* — establishes whether the SMT-style encoding is the only option, or if Lean's type system can make some hypotheses structurally true.

When the answers differ, the Lean-native shape is usually shorter, tighter, and reduces the unverified surface between Verus and Tactus. The translation table (DESIGN.md § "Expression mapping") leans heavily on this: `=~=` (extensional equality) maps to `=` not because we encode extensionality, but because Lean 4's `=` already IS extensional on functions via funext.

**Where this discipline applies in the deferred queue.**
* **Deeper field paths** (`&mut a.b.c`) extend #87's structure-update pattern recursively: `let a := { a with b := { a.b with c := <fresh> } }`. No havoc encoding.
* **Multi-variant enum field mutation** is the one case Lean's structure-update syntax doesn't compose with — it'd need a match-and-rebuild encoding. But that's a specific Lean idiom (`match a with | Variant fs => Variant { fs with f := <fresh> }`), not a havoc.
* **Closures (#93)** target Lean's first-class function types directly rather than encoding the FnOnce/Fn/FnMut hierarchy as Z3 axioms. Closure declarations bind `cid` to a real Lean lambda (`fun (x : T) => body`) via `Wp::LetRaw`; calls to spec closures lower to `App(f, args)`. Verus's synthesized `Assume(forall|x| ClosureReq(cid, x) ↔ ... ∧ ClosureEns(cid, x, body(x)) ↔ ...)` is dropped because the lambda binding IS the same fact structurally — no axiomatization needed. The only piece this encoding doesn't yet cover is exec-mode closure CALLS (Verus's `exec_nonstatic_call` desugar), which is upstream-blocked rather than encoding-shaped.
* **Indexed L-values (`&mut v[i]`)** need a `Vector.set i v` style encoding — Lean has it, no havoc needed.
* **Ret-substitution at call sites (#128)** — when a callee's ensures contains `r == E` (uniquely determining the return value), the caller's post-call frames *don't* need a `∀ ret, ret_bound → ensures(ret) → let dest := ret;` chain. Tactus replaces it with `let dest := E; (E_bound) → (ensures with ret := E) → …`, eliminating the ∀-quantifier entirely. Verus's Z3 path emits the ∀ because SMT can't natively substitute a logical variable with a witnessing expression — the ensures clause acts as the substitution glue. Lean substitutes definitionally via `let`. Same fact, structural rather than asserted. Beyond aesthetics: the ∀-Prop shape blocked `tactus_auto`'s default closer (omega rejects ∀-Prop). #128's substitution path makes cond_setup goals (function-call-in-loop-cond) close under the default closer with no override needed — see "Ret-substitution at call sites (#128)" below for the full encoding details.

**When the discipline doesn't apply.** Some obligations are inherently shaped by the source semantics, not the target. Termination via `CheckDecreaseHeight`, fixed-width integer overflow checks, and SSA mutation as let-shadowing are all encodings the SMT path uses that translate cleanly because the property at hand IS first-order arithmetic (or first-order shadowing). The discipline matters most when the property is *higher-order* or *structural* — where Lean's expressivity exceeds SMT's.

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

#### Putting Lean on PATH

The test commands below pass `PATH="../tools/vargo/target/release:$PATH"` to inject vargo. The same `$PATH` must include `lake` / `lean` so the test subprocess can spawn Lean.

If `elan` is fully installed, `~/.elan/bin/` is typically on `$PATH` already and `lake` resolves through the elan proxy. Confirm with `which lake`.

If only the toolchain dirs exist (e.g., a partial install where `~/.elan/toolchains/` is populated but `~/.elan/bin/` isn't), prepend the toolchain's bin dir directly. Tactus's pinned version is `v4.25.0` (see `lean-project/lean-toolchain`):

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:$PATH"
```

Or include it inline on the test command:

```bash
PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:../tools/vargo/target/release:$PATH" \
  vargo test -p rust_verify_test --test tactus
```

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
