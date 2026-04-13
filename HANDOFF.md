# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs (`by { ring }`, `by { nlinarith [...] }`). The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document (read this first)
  HANDOFF.md                   ← this file
  source/
    lean_verify/               ← NEW: Lean generation + invocation (649 lines)
      TactusPrelude.lean       ← Lean prelude (real .lean file, editable)
      src/
        to_lean_type.rs        ← vir::ast::TypX → Lean type syntax
        to_lean_expr.rs        ← vir::ast::ExprX → Lean expr syntax (precedence-based parens)
        to_lean_fn.rs          ← FunctionX → noncomputable def / theorem
        lean_process.rs        ← invoke `lean --stdin --json`, parse JSON diagnostics
        prelude.rs             ← include_str! of TactusPrelude.lean
        lib.rs
      tests/
        integration.rs         ← 7 end-to-end tests (invoke Lean 4, verify/reject)
    builtin_macros/src/
      syntax.rs                ← MODIFIED: tactic mode for proof fns (lines ~4036-4085)
    rust_verify/src/
      attributes.rs            ← MODIFIED: Attr::TacticProof + VerifierAttrs.tactic_proof
      rust_to_vir_func.rs      ← MODIFIED: threads tactic_proof to FunctionAttrsX
      verifier.rs              ← MODIFIED: routing stub at OpKind::Query (skips Z3 for tactic fns)
    vir/src/
      ast.rs                   ← MODIFIED: FunctionAttrsX.tactic_proof: bool
    air/                       ← UNCHANGED (will be removed after Lean backend is complete)
    Cargo.toml                 ← MODIFIED: added lean_verify to workspace
  tree-sitter-tactus/          ← sibling dir in verus-cad/: tree-sitter grammar
```

## What works today

### Lean generation pipeline (fully tested)

`lean_verify` depends on `vir` directly — no intermediate IR. Translators operate on VIR's `TypX`, `ExprX`, `FunctionX` types.

```
vir::ast::FunctionX → to_lean_fn → Lean text → lean --stdin --json → parsed diagnostics
```

**11 tests pass** (4 unit + 7 integration). Integration tests invoke Lean 4 and verify:
- `double` spec fn + `lemma_double_pos` proof fn with `unfold double; omega`
- `add_comm` with `omega`
- Intentionally wrong proof (correctly rejected)
- Recursive `factorial` with `termination_by` + induction proof
- Multiple requires/ensures with conjunction
- Forall quantifier
- Implies with hypothesis

Run tests:
```bash
cd tactus/source
cargo test -p lean_verify                          # unit tests (no Lean needed)
nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"  # needs Lean 4
```

### Verus pipeline modifications (compiles, not yet end-to-end tested)

The tactic_proof attribute flows through the entire pipeline:

```
proof fn body detected in builtin_macros
  → #[verus::internal(tactic_proof)] attribute emitted
  → body replaced with unimplemented!() dummy
  → Attr::TacticProof parsed in attributes.rs
  → VerifierAttrs.tactic_proof = true
  → FunctionAttrsX.tactic_proof = true (in VIR)
  → verifier.rs intercepts at OpKind::Query dispatch
  → skips Z3, currently stubs as "verified" with eprintln
```

Build everything:
```bash
cd tactus/source
RUSTC_BOOTSTRAP=1 cargo build -p rust_verify    # needs RUSTC_BOOTSTRAP for rustc_private
cargo build -p lean_verify                       # builds without RUSTC_BOOTSTRAP
```

## What needs to be done next

### Immediate: Wire Lean into the verifier (the "last mile")

**The stub in `verifier.rs` (~line 1586) needs to call `lean_verify` instead of just printing and continuing.**

The function at that point is a `FunctionSst` (SST-level) which has `attrs: FunctionAttrs` (same type as VIR). The `FunctionSstX` also stores spec fn info from the `KrateSst`. To wire it up:

1. **Collect all spec fns** this proof fn references (from `krate.functions`)
2. **Pass VIR `FunctionX` data directly** to `lean_verify::to_lean_fn` — no conversion needed since lean_verify already operates on VIR types. The SST `FunctionSstX` has the function name, and the original VIR `Krate` (available in the verifier context) has the full `FunctionX` with body, requires, ensures.
3. **Extract tactic body** from the source file using tree-sitter-tactus (by source span), or for initial testing, extract from the source text by byte range
4. **Call `lean_verify::to_lean_fn::generate_lean_file()`** with the spec fns + proof fn + tactic text
5. **Call `lean_verify::lean_process::check_lean_stdin()`** with the generated Lean
6. **Convert `LeanResult` → `ValidityResult`**: success → `ValidityResult::Valid`, error → `ValidityResult::Invalid`
7. **Map Lean error positions** back to `.rs` source locations using the source map

### Immediate: Full Verus build environment

To test the full pipeline end-to-end:

```bash
cd tactus/source
./tools/get-z3.sh                    # downloads Z3 (still needed for non-tactic fns)
cargo install --path cargo-verus     # install vargo
vargo build                          # builds everything including vstd
./target-verus/release/verus test.rs # run verifier
```

### Short-term: Tree-sitter tactic extraction

The proc macro records the source span of the proof fn body. tree-sitter-tactus extracts the actual tactic text (handling Unicode):

```rust
// lean_verify/src/tactic_extractor.rs
pub fn extract_tactic_body(source: &str, start_line: usize, end_line: usize) -> Option<String> {
    let mut parser = tree_sitter::Parser::new();
    parser.set_language(&tree_sitter_tactus::LANGUAGE.into()).ok()?;
    let tree = parser.parse(source.as_bytes(), None)?;
    // find tactic_block or block node at the span, extract text between { and }
}
```

Requires adding `tree-sitter` + `tree-sitter-tactus` as deps. For initial testing, extract by byte range without tree-sitter.

### Short-term: The `by { }` syntax

Currently the proc macro treats ALL proof fn bodies as tactic blocks (detects `FnMode::Proof` + has body). The `by` keyword before the block is optional syntactic sugar. Both forms work:

```rust
proof fn lemma() ensures P by { omega }  // tree-sitter-tactus syntax
proof fn lemma() ensures P { omega }     // also works (proc macro doesn't care about `by`)
```

### Medium-term: vstd translation + path mapping

Verus programs depend on `vstd`. A VIR path → Lean name mapping table is needed:

```rust
// lean_verify/src/builtin_paths.rs
pub fn vir_path_to_lean(path: &str) -> Option<&str> {
    match path {
        "vstd::seq::Seq::len" => Some("Seq.len"),
        "vstd::seq::Seq::index" => Some("Seq.index"),
        // ...
        _ => None,
    }
}
```

### Long-term: Exec fn VC generation (`sst_to_lean`)

Implement weakest-precondition VC generation from SST targeting Lean. New module `vir/src/sst_to_lean.rs`. This is 3-6 months of work — see DESIGN.md for details.

### Long-term: Mathlib integration

Set up managed Lake project (`~/.tactus/lean-project/`), download precompiled Mathlib oleans via `lake exe cache get`, switch invocation to `lake env lean`. User specifies imports via `import` declarations.

## Key files to understand

| File | What it does |
|------|-------------|
| `lean_verify/src/to_lean_fn.rs` | Core: generates .lean files from VIR FunctionX |
| `lean_verify/src/to_lean_expr.rs` | VIR ExprX → Lean expression text (precedence-based parens) |
| `lean_verify/src/to_lean_type.rs` | VIR TypX → Lean type text. Also has `write_todo()` and `write_path_last()` helpers |
| `lean_verify/src/lean_process.rs` | Invokes `lean --stdin --json`, parses JSON diagnostics |
| `lean_verify/TactusPrelude.lean` | Lean prelude (set_option only for now, will grow) |
| `builtin_macros/src/syntax.rs:~4044` | Where proof fns are detected + marked as tactic_proof |
| `rust_verify/src/attributes.rs` | Where `tactic_proof` attr is parsed |
| `rust_verify/src/verifier.rs:~1586` | Where tactic fns are routed (currently stub) |
| `vir/src/ast.rs:~1498` | `FunctionAttrsX.tactic_proof` flag |
| `vir/src/ast.rs:1027` | `ExprX` enum — all expression types the translator handles |
| `vir/src/ast.rs:258` | `TypX` enum — all type variants the translator handles |
| `DESIGN.md` | Full design: architecture, decisions, rationale |

## How to build and test

```bash
cd tactus/source

# Build lean_verify (no special toolchain):
cargo build -p lean_verify

# Run unit tests:
cargo test -p lean_verify

# Run integration tests (needs Lean 4):
nix-shell -p lean4 --run "cargo test -p lean_verify --test integration"

# Build everything including rust_verify:
RUSTC_BOOTSTRAP=1 cargo build -p rust_verify

# Full Verus build (needs vargo + Z3):
./tools/get-z3.sh
cargo install --path cargo-verus
vargo build
```

## Architectural decisions (summary from DESIGN.md)

1. **No Z3** — Lean only, no dual backend
2. **Cut at SST** — fresh WP-based VC generation, not reusing AIR
3. **Dual parser** — tree-sitter-tactus for Unicode tactic extraction, rustc proc macro for VIR construction
4. **All spec fns `@[irreducible]`** by default, `open spec fn` for transparent
5. **Explicit imports** — user writes `import Mathlib.Tactic.Ring`, no auto-detection
6. **Precompiled Mathlib** — `lake exe cache get`, not compiled from source
7. **`Seq.index` is opaque** — out-of-bounds truly unspecified (matches Verus semantics)
8. **`tactus_auto` uses `fail`** not `sorry` — auto-tactic failures are real errors
9. **`arch_word_bits` is axiom** — sound for cross-compilation
10. **`proof { }` in exec fns** — keeps syntax, body is tactics, results thread into VC context
11. **lean_verify depends on VIR directly** — no intermediate IR, translators operate on VIR AST types

## Git log

```
8b85c14 Second cleanup pass: dedup, zero-alloc names, consistent sorry
fdbbf5c Code review refactor: drop IR, use VIR directly, simplify everything
98f5f68 Tactus: verifier routing for tactic proof fns (stub)
ff06399 Thread tactic_proof through VIR: attribute flows from proc macro to FunctionAttrsX
284ac88 Tactus tactic_proof: proc macro + attribute detection
8a316ab lean_verify: end-to-end pipeline working — IR → Lean → verified
59b7db8 lean_verify: IR types + Lean type/expression translators
4ae01c2 lean_verify crate: Lean 4 subprocess invocation working
bb18bff DESIGN.md: comprehensive design after 4 critique rounds
```

Plus in the parent `verus-cad/` repo:
```
0c14995 tree-sitter-tactus: initial grammar for Tactus language
```
