# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Current state

**The end-to-end pipeline works.** A user can write:

```rust
verus! {
    spec fn double(x: nat) -> nat { x + x }

    proof fn lemma_double_pos(x: nat)
        requires x > 0
        ensures double(x) > x
    by {
        unfold double; omega
    }
}
```

And Tactus generates Lean, invokes `lean --stdin --json`, and reports the result through the standard Verus verification pipeline. Wrong proofs are correctly rejected with Lean's goal state shown in the error.

### What works today

- **`by { }` syntax**: verus-syn parser captures tactic block content as raw `TokenStream` before Rust parsing, preserving verbatim Lean syntax
- **Spec fn → Lean**: `spec fn` → `@[irreducible] noncomputable def`, `open spec fn` → `noncomputable def`
- **Proof fn → Lean**: `proof fn ... by { tactics }` → `theorem ... := by tactics`
- **Requires/ensures**: each `requires` → hypothesis `(hᵢ : clause)`, multiple `ensures` → conjunction with `∧`
- **Recursive spec fns**: `decreases` → `termination_by`, `as nat`/`as int` clips handled
- **Dependency ordering**: Tarjan's SCC detects mutual recursion, topological sort ensures callees before callers, only transitively referenced spec fns are included
- **Mutual recursion**: mutually recursive spec fns wrapped in Lean `mutual ... end`
- **Namespacing**: generated Lean uses VIR `owning_module` path as `namespace`
- **Error reporting**: Lean errors go through Verus's diagnostic system with source spans
- **Expression translation**: constants, variables, binary ops, unary ops, if/else, function calls, quantifiers, choose, extensional equality, ReadPlace, Field, Clip, CoerceMode, Trigger (dropped), Ghost/ProofInSpec (transparent)
- **Full vstd build**: `vargo build --release` → 1530 verified, 0 errors
- **10 end-to-end tests**: basic omega, wrong proof rejected, add_comm, multiple requires/ensures, implies, if-then-else spec fn, recursive spec fn, dependency ordering, mutual recursion, filtering

### Test summary

```bash
# lean_verify unit + integration tests (13 tests, needs Lean 4):
cargo test -p lean_verify

# End-to-end tests through full Verus pipeline (10 tests, needs Lean 4):
# Must use tactus's own vargo:
PATH="tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Full build (1530 vstd fns verified):
PATH="tools/vargo/target/release:$PATH" vargo build --release
```

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document
  HANDOFF.md                   ← this file
  dependencies/
    syn/src/
      verus.rs                 ← MODIFIED: tactic_by field on SignatureSpec, raw TokenStream capture
      item.rs                  ← MODIFIED: empty body when tactic_by consumed the block
      gen/clone.rs             ← MODIFIED: clone for tactic_by tuple
  source/
    lean_verify/               ← Lean generation + invocation (828 lines)
      TactusPrelude.lean       ← Lean prelude (real .lean file)
      src/
        dep_order.rs           ← dependency analysis: filtering, topo sort, Tarjan's SCC (164 lines)
        to_lean_type.rs        ← vir::ast::TypX → Lean type syntax (90 lines)
        to_lean_expr.rs        ← vir::ast::ExprX → Lean expr syntax (277 lines)
        to_lean_fn.rs          ← FunctionX → noncomputable def / theorem + mutual blocks (169 lines)
        lean_process.rs        ← invoke `lean --stdin --json`, parse JSON diagnostics (116 lines)
        prelude.rs             ← include_str! of TactusPrelude.lean
        lib.rs
      tests/
        integration.rs         ← 7 standalone Lean invocation tests
    builtin_macros/src/
      syntax.rs                ← MODIFIED: by {} detection, tactic body capture, apply_tactic_attrs
    rust_verify/src/
      attributes.rs            ← MODIFIED: TacticBody attr parsing in Internal prefix
      rust_to_vir_func.rs      ← MODIFIED: threads tactic_body to FunctionAttrsX
      verifier.rs              ← MODIFIED: routes tactic fns to Lean, error reporting
    rust_verify_test/tests/
      tactus.rs                ← 10 end-to-end tests (170 lines)
    vir/src/
      ast.rs                   ← MODIFIED: FunctionAttrsX.tactic_body: Option<String>
      ast_visitor.rs           ← MODIFIED: expr_visitor_walk made pub
      lib.rs                   ← MODIFIED: visitor module made pub
      visitor.rs               ← MODIFIED: VisitorControlFlow made pub
```

## Architecture

### Data flow

```
User writes:
  proof fn lemma(x: nat) requires x > 0 ensures double(x) > x
  by { unfold double; omega }

verus-syn parser:
  SignatureSpec.tactic_by = Some((by_token, TokenStream("unfold double ; omega")))
  ItemFn.block = empty (by {} consumed the block)

Proc macro (syntax.rs):
  Detects tactic_by.is_some() on proof fn
  Captures tactic body via TokenStream::to_string()
  Emits #[verus::internal(tactic_body("unfold double ; omega"))]
  Truncates body to just spec stmts (requires/ensures)

VIR construction (rust_to_vir_func.rs):
  FunctionAttrsX.tactic_body = Some("unfold double ; omega")

Verifier (verifier.rs):
  if let Some(tactic_body) = &function.x.attrs.tactic_body
  → Looks up VIR function from self.vir_crate
  → Collects all VIR functions, passes to generate_lean_file
  → dep_order filters to referenced spec fns, topologically sorts
  → Generates Lean with namespace, mutual blocks
  → Invokes lean --stdin --json
  → Reports success/failure through Verus diagnostics
```

### Key design decisions

1. **`tactic_body: Option<String>`** — single field on `FunctionAttrsX`. Its presence IS the tactic proof marker. No separate boolean.
2. **Verbatim capture** — verus-syn captures `by { }` content as raw `TokenStream` before Rust statement parsing. No string rewriting needed.
3. **VIR's expr_visitor_walk** — dependency analysis reuses VIR's built-in expression walker instead of hand-rolling one. Only the Fun-reference-collecting callback is custom.
4. **lean_verify depends on VIR directly** — no intermediate IR. Translators operate on VIR's `TypX`, `ExprX`, `FunctionX`.

## What needs to be done next

### Track A completion: Source map + error mapping

The one remaining Track A item. Currently, Lean errors show the proof fn's source span but don't pinpoint which tactic line failed. Need to map Lean's line/column positions in the generated `.lean` back to the user's `.rs` source positions.

Design from DESIGN.md:
```
$ tactus check src/quad_ext.rs

error: unsolved goal
  --> src/quad_ext.rs:42:1 (norm_nonneg)

  re im d : Int
  h₀ : d ≤ 0
  ⊢ re * re - d * (im * im) ≥ 0

  try: nlinarith [sq_nonneg re, sq_nonneg im]
```

### Track B: Exec fn VC generation (`sst_to_lean`)

The largest engineering effort. Implements weakest-precondition VC generation from VIR-SST targeting Lean. Each exec fn obligation becomes a Lean `theorem` with auto-tactics.

Key pieces:
- WP rules for let, if/else, return, loops, mutation (SSA), pattern matching
- `proof { }` blocks in exec fns thread tactic results into VC context
- `assert(P) by { tactics }` → `have h : P := by <tactics>` in VC
- `assume(P)` → `have h : P := sorry` with warning
- `tactus_auto` macro for auto obligations
- Overflow checking for fixed-width types

This is ~3000 lines (comparable to `sst_to_air`). Shares `to_lean_expr` and `to_lean_type` with Track A.

### Track C: vstd translation + path mapping

Makes Tactus work with real Verus programs that use `vstd::seq::Seq`, `vstd::set::Set`, etc.

1. **VIR path → Lean name table**: `vstd::seq::Seq::len` → `Seq.len`, etc. (see DESIGN.md for full table)
2. **TactusPrelude.lean expansion**: Add `Seq` (opaque index), `Set`, clip fns, `arch_word_bits` axiom
3. **Translate vstd spec fns** to Lean defs in `TactusStd.lean`
4. **Arithmetic lemmas** from `vstd::arithmetic::*` → map to Mathlib equivalents

Currently the prelude is minimal (just `set_option`). Programs using vstd types will get "unsupported" errors until this track progresses.

### Track D: Types, traits, multi-crate

- Struct → Lean `structure`, Enum → `inductive`
- Trait → `class`, Impl → `instance`
- Map to Mathlib hierarchy (Ring → CommRing, etc.)
- Cross-crate declaration files (`CrateDecls.lean`)

### Ongoing polish

- Per-module Lean generation (currently one file per proof fn)
- Heartbeat annotations (`#[verifier::heartbeats(N)]` → `set_option maxHeartbeats N in`)
- IDE integration (show goal states)
- Mathlib setup (`~/.tactus/lean-project/` with `lake exe cache get`)
- `import` keyword for explicit Mathlib imports

## Expression translation coverage

### Handled

| VIR Expression | Lean Output |
|---|---|
| `Const(Bool(true/false))` | `True` / `False` |
| `Const(Int(n))` | `n` (negative wrapped in parens) |
| `Var(ident)` | `ident` (keyword-escaped) |
| `ConstVar(fun)` | last path segment |
| `Binary(And/Or/Implies/Eq/Ne/Le/Lt/Ge/Gt/Add/Sub/Mul/Div/Mod)` | `∧`/`∨`/`→`/`=`/`≠`/`≤`/`<`/`≥`/`>`/`+`/`-`/`*`/`/`/`%` |
| `BinaryOpr(ExtEq)` | `=` (Lean's = is extensional) |
| `Unary(Not)` | `¬` |
| `Unary(Clip{Nat↔Int})` | `Int.toNat` or identity |
| `Unary(CoerceMode)` | transparent |
| `Unary(Trigger)` | transparent (SMT-specific, dropped) |
| `Call(Fun, args)` | `fun arg₁ arg₂` |
| `If(c, t, e)` | `if c then t else e` |
| `Quant(Forall/Exists)` | `∀ (x : T), body` / `∃ (x : T), body` |
| `Choose` | `Classical.choose` |
| `WithTriggers` | transparent (triggers dropped) |
| `Block(stmts, expr)` | sequential |
| `ReadPlace(Local)` | variable name |
| `UnaryOpr(Box/Unbox)` | transparent |
| `UnaryOpr(Field)` | `expr.field` |
| `UnaryOpr(IsVariant)` | `expr.isVariant` |
| `UnaryOpr(CustomErr)` | transparent |
| `Ghost/ProofInSpec` | transparent |
| `Header` | skipped |

### Not yet handled (returns `sorry /- TODO -/`)

| VIR Expression | Needed for |
|---|---|
| `Ctor` | struct/enum construction (Track D) |
| `Match` | pattern matching (Track B) |
| `Closure` | closures (Track B) |
| `Loop` | loops (Track B) |
| `Assign/AssignToPlace` | mutation (Track B) |
| `Return` | early return (Track B) |
| `BitNot/IntToReal/RealToInt` | specialized arithmetic |
| `NullaryOpr/Multi` | misc |

## How to build and test

```bash
cd tactus/source

# First time: build vargo from tactus's tools
cd ../tools/vargo && cargo build --release && cd ../../source

# Build everything including vstd:
PATH="../tools/vargo/target/release:$PATH" vargo build --release

# Run lean_verify unit tests (no special toolchain needed):
cargo test -p lean_verify

# Run end-to-end tests (needs Lean 4 on PATH):
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Build lean_verify only (no RUSTC_BOOTSTRAP needed):
cargo build -p lean_verify

# Build rust_verify only:
RUSTC_BOOTSTRAP=1 cargo build -p rust_verify
```

## Lessons learned this session

1. **Always run `visit_item_fn_mut`** — skipping the recursive visit for tactic proof fns broke `spec_fn` type transformations for ALL proof fns in vstd. The fix: always visit, then replace the body afterward.

2. **Attributes must be in the right match arm** — `verus::internal(...)` attributes are parsed in the `VerusPrefix::Internal` match arm, not the general `Verifier` arm. Putting `tactic_body` in the wrong arm caused "unrecognized internal attribute" for all vstd proof fns.

3. **VIR after `modes::check_crate` uses `ReadPlace` for variable references** — not `Var`. The `self.vir_crate` stores the post-modes VIR krate, so expression translators must handle `ReadPlace(PlaceX::Local(ident))`.

4. **Proc macro `unimplemented!()` bodies fail in Verus** — Verus rejects `panic!`. Use empty body `vec![]` or `truncate` to preserve only spec stmts.

5. **Verbatim capture beats string rewriting** — the proc-macro-tokenized body `unfold(double) ; omega()` requires fragile string-level conversion. Capturing the raw `TokenStream` before Rust parsing eliminates this entirely.

6. **Reuse VIR infrastructure** — `expr_visitor_walk` already handles all ExprX variants correctly. Hand-rolling a walker is 150 lines of code that will miss future variants. Making one function `pub` saved ~200 lines.

7. **Single field > boolean + option** — `tactic_proof: bool` + `tactic_body: Option<String>` always move together. Collapsing to just `tactic_body: Option<String>` (presence = tactic proof) removed code across 5 files.

## Git log

```
4c838bc Use VIR's built-in expr_visitor_walk instead of hand-rolled walker
c078d52 dep_order review fixes: exhaustive expr walking, combined pass, cleaner Tarjan's
bc751f6 Dependency ordering: topological sort, filtering, mutual recursion
081d62a Final cleanup: delete stale test file, handle Trigger, improve catch-all
aa46d15 Unify tactic_proof + tactic_body into single Option<String>
7dbe1d2 Verbatim tactic capture: eliminate string rewriting entirely
f85fff0 Code review fixes: move tactic cleanup, fix unsound UnaryOpr, dedup proc macro
d9e902d Wire Lean backend end-to-end: by {} syntax, error reporting, namespacing
e1b671f Initial progress
86de4a3 Initial tactus
a329300 Update HANDOFF.md after code review refactors
8b85c14 Second cleanup pass: dedup, zero-alloc names, consistent sorry
fdbbf5c Code review refactor: drop IR, use VIR directly, simplify everything
4aa9f07 HANDOFF.md: comprehensive handoff document for Tactus development
98f5f68 Tactus: verifier routing for tactic proof fns (stub)
ff06399 Thread tactic_proof through VIR: attribute flows from proc macro to FunctionAttrsX
284ac88 Tactus tactic_proof: proc macro + attribute detection
8a316ab lean_verify: end-to-end pipeline working — IR → Lean → verified
59b7db8 lean_verify: IR types + Lean type/expression translators
4ae01c2 lean_verify crate: Lean 4 subprocess invocation working
bb18bff DESIGN.md: comprehensive design after 4 critique rounds
7a8f5f7 Initial commit
```

## Key files to understand

| File | What it does |
|------|-------------|
| `lean_verify/src/to_lean_fn.rs` | Core: generates .lean files from VIR FunctionX, handles mutual blocks |
| `lean_verify/src/to_lean_expr.rs` | VIR ExprX → Lean expression text (precedence-based parens) |
| `lean_verify/src/to_lean_type.rs` | VIR TypX → Lean type text |
| `lean_verify/src/dep_order.rs` | Dependency filtering, topological sort, Tarjan's SCC |
| `lean_verify/src/lean_process.rs` | Invokes `lean --stdin --json`, parses JSON diagnostics |
| `lean_verify/TactusPrelude.lean` | Lean prelude (set_option only for now, will grow) |
| `dependencies/syn/src/verus.rs` | Where `by { }` is parsed (tactic_by on SignatureSpec) |
| `dependencies/syn/src/item.rs` | Where empty body is provided when tactic_by consumed the block |
| `builtin_macros/src/syntax.rs:~45` | Tactus helper fns: is_tactus_tactic_proof, get_tactic_body, apply_tactic_attrs |
| `builtin_macros/src/syntax.rs:~4090` | Where tactic fns are detected + tactic body captured |
| `rust_verify/src/attributes.rs` | Where `tactic_body` attr is parsed (Internal prefix) |
| `rust_verify/src/verifier.rs:~1580` | Where tactic fns are routed to Lean |
| `vir/src/ast.rs:~1498` | `FunctionAttrsX.tactic_body: Option<String>` |
| `DESIGN.md` | Full design: architecture, decisions, rationale |
