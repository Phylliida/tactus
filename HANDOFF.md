# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Current state

**100 end-to-end tests pass.** The pipeline works: user writes a proof fn with `by { }`, Tactus generates Lean, invokes Lean (with Mathlib if available), reports results through Verus's diagnostic system.

**FileLoader uses tree-sitter-tactus.** Parses source with tree-sitter to find `tactic_block` nodes inside `verus! { }` macro bodies, sanitizes their content before rustc lexes. Supports Unicode (`⟨⟩·∀∃`), Lean comments (`--`, `/- -/`), and all Lean syntax except `//`.

**tree-sitter-tactus grammar: 199 tests.** Brace macro bodies parsed as statements (sees inside `verus! { }`), Verus operators (`<==>`, `=~=`, `=~~=`, `&&&`, `|||`), `assert by(solver)`, `#[trigger]` attributed expressions.

**Track D complete.** Structs, enums, traits (with associated types via `outParam`), trait impls as instances (generic, bounded, with TypEquality), type projections — all working.

### What works

- **`by { }` syntax**: tactic bodies extracted verbatim from source file via byte range (preserves newlines, Unicode, Lean comments)
- **FileLoader**: tree-sitter-tactus query finds `tactic_block` nodes, sanitizes content. Installed in both compilation passes (verifier + erasure).
- **tree-sitter-tactus**: brace macro bodies parsed as statements, Lean-aware `_tactic_brace_body`, Verus operators, `#[trigger]`, `assert by(solver)`, `chained_conjunction`/`chained_disjunction`
- **`import` keyword**: `import Mathlib.Tactic.Ring` threaded through proc macro → VIR → Lean
- **Mathlib**: Lake project at `tactus/lean-project/` (repo-local), precompiled oleans
- **Structs/enums**: struct → `structure`, enum → `inductive`, generic type params, multi-field variants
- **Traits**: trait → `class` with method dispatch, associated types as `outParam` type params, trait bounds as `[TraitName T]` instance params
- **Trait impls**: `impl Trait for Type` → `noncomputable instance`, generic impls with `{T : Type}`, bounded impls with `[BoundTrait T]`, associated type assignments as type arguments, TypEquality bounds merged with Trait bounds
- **Type projections**: `Self::Item` → `Producer.Item (Self)` via `outParam` resolution
- **Generics**: type params, trait bounds, const generics, explicit type args
- **Dependency ordering**: Tarjan's SCC, topological sort, instances after spec fns, mutual recursion → `mutual ... end`
- **Namespace wrapper**: `namespace crate_name ... end crate_name` avoids Lean builtin collisions
- **`//` detection**: clear error at verification time ("use Nat.div/Int.div instead")
- **Source map**: tactic line numbers in error messages
- **Expression types**: `write_expr` takes full `&Expr` (with type info), proper integer constant handling
- **vstd builds**: `vargo build --release` → 1530 verified, 0 errors

### Architecture

```
User writes: proof fn lemma(x: nat) requires x > 0 ensures double(x) > x by { unfold double; omega }

FileLoader:  tree-sitter-tactus parses file, finds tactic_block nodes inside verus! { }
             replaces content between { } with spaces (same byte offsets)
             rustc sees: by {                              }
             installed in BOTH compilation passes

verus-syn:   captures `by { }` brace group, records Span::byte_range() → (start, end)
proc macro:  emits #[verus::internal(tactic_span(start, end))], truncates body
VIR:         tactic_span: Option<(String, usize, usize)> — file path + byte range
             file path resolved via SourceMap at VIR construction time
verifier:    reads ORIGINAL source file at byte range → verbatim tactic text
             dedents for Lean's indentation-sensitive parser
             checks for // → clear error
             calls lean_verify::check_proof_fn(krate, fn, tactic_text, imports, crate_name)
lean_verify:  generates .lean file:
               namespace crate_name
               imports, prelude, traits, datatypes, spec fns (topo sorted),
               trait impls (instances), theorem with tactic body
               end crate_name
             invokes `lake env lean` or `lean --stdin --json`
             parses JSON diagnostics, maps via source map
```

### Key design decisions

1. **tree-sitter FileLoader** — tree-sitter-tactus query finds `tactic_block` nodes. No custom byte scanner needed. Grammar handles `verus! { }` bodies as statements.
2. **`//` not allowed in tactic blocks** — tree-sitter's `line_comment` extra consumes `//` globally. Content after `//` is silently lost.
3. **Tactic body via byte range** — proc macro stores `tactic_span(file_path, start_byte, end_byte)`. File path resolved at VIR construction time via SourceMap. Works on any thread.
4. **Associated types as `outParam`** — `class Foo (Self : Type) (Item : outParam Type)`. Lean's instance synthesis automatically resolves associated types. No return type annotations needed on method calls.
5. **TypEquality bounds merged with Trait bounds** — `T: Producer<Item = int>` emits single `[Producer T Int]` (not separate `[Producer T]` + equality constraint).
6. **Namespace wrapper** — `namespace crate_name` avoids collisions with Lean builtins (Unit, Empty, etc.). Transparent to user — names in goal states match Rust source.
7. **Instances after spec fns** — trait impl method bodies may reference spec fns. Emitting instances after spec fns ensures Lean definitions exist.
8. **`lean_name` filters synthetic impl segments** — VIR paths like `["impl&%0", "value"]` have synthetic first segments filtered by content (`&`, `%` characters).
9. **Exhaustive pattern matches** — no catch-all `_ =>`. New VIR variants cause compile errors.
10. **Missing trait methods panic** — not sorry, not silent drop. Internal invariant violation = clear bug report message.

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document
  HANDOFF.md                   ← this file
  lean-project/                ← repo-local Lake project for Mathlib
    lakefile.lean              ← imports Mathlib
    lean-toolchain             ← pins Lean version
    .lake/                     ← precompiled oleans (gitignored)
  tree-sitter-tactus/          ← git submodule
    grammar.js                 ← Tactus grammar: brace macros as statements,
                                 Verus operators, #[trigger], assert by(solver)
    src/scanner.c              ← external scanner
    test/corpus/
      tactic_blocks.txt        ← 47 tactic-specific tests (incl. verus! macro tests)
      declarations.txt         ← Rust declaration tests
      macros.txt               ← macro invocation tests
  dependencies/
    syn/src/verus.rs           ← MODIFIED: tactic_by with byte_range()
  source/
    lean_verify/               ← Lean generation + invocation
      TactusPrelude.lean       ← Lean prelude (real .lean file)
      scripts/setup-mathlib.sh ← Mathlib setup script
      src/
        dep_order.rs           ← dependency analysis: topo sort, Tarjan's SCC, walk_expr
        generate.rs            ← orchestrates file gen + Lean invocation + namespace
        to_lean_type.rs        ← TypX → Lean type, lean_name(), Projection handling
        to_lean_expr.rs        ← Expr → Lean expr (type-aware), precedence, write_name()
        to_lean_fn.rs          ← FunctionX → def/theorem/class/instance, source map
        lean_process.rs        ← invoke lean, parse JSON diagnostics, format errors
        project.rs             ← tactus/lean-project/ detection (CARGO_MANIFEST_DIR)
        prelude.rs             ← include_str! of TactusPrelude.lean
      tests/integration.rs     ← 7 standalone Lean tests
    builtin_macros/src/
      syntax.rs                ← MODIFIED: by {} detection, byte range capture
    rust_verify/src/
      file_loader.rs           ← tree-sitter FileLoader + 36 unit tests
      driver.rs                ← MODIFIED: FileLoader in both compilation passes
      attributes.rs            ← MODIFIED: TacticSpan attr parsing
      rust_to_vir_func.rs      ← MODIFIED: tactic_span + file path resolution
      verifier.rs              ← MODIFIED: reads source, // detection, routes to Lean
      util.rs                  ← dedent() + 8 unit tests
    rust_verify_test/tests/
      tactus.rs                ← 100 end-to-end tests
    vir/src/
      ast.rs                   ← MODIFIED: tactic_span: Option<(String, usize, usize)>
```

## What remains to be done

### Track B: Exec fn VC generation

Implement `sst_to_lean.rs` — weakest-precondition VC generation from SST targeting Lean. See DESIGN.md for WP rules. This is the largest remaining work item.

### Track C: vstd translation

Build VIR path → Lean name lookup table for `vstd::seq::Seq`, `vstd::set::Set`, etc. Expand `TactusPrelude.lean` with Seq/Set/Map definitions.

### Track D remaining: ecosystem

- Map to Mathlib hierarchy (Ring → CommRing, OrderedField → LinearOrderedField)
- Cross-crate declaration files (`CrateDecls.lean`)
- Topologically sort trait impls with spec fns (currently separate; works because lambda bodies are lazy)

### Other

- Per-module Lean generation (currently one .lean per proof fn)
- IDE integration (goal states in editor)
- Lean project path for distribution (currently uses compile-time `CARGO_MANIFEST_DIR`)
- Cache original source in FileLoader (currently re-reads from disk)
- Only parse `.rs` files containing tactic blocks (currently parses all files)

## Setup and testing

```bash
cd tactus/source

# First-time build
cd ../tools/vargo && cargo build --release && cd ../../source
PATH="../tools/vargo/target/release:$PATH" vargo build --release

# Mathlib setup (~5 min download, ~2 GB)
cd lean_verify && ./scripts/setup-mathlib.sh && cd ..
# Or with env override:
TACTUS_LEAN_PROJECT=/custom/path ./scripts/setup-mathlib.sh

# Run end-to-end tests (100 tests)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Quick compile check
RUSTC_BOOTSTRAP=1 cargo check -p rust_verify

# FileLoader + dedent unit tests (44 tests)
RUSTC_BOOTSTRAP=1 cargo test -p rust_verify --lib -- file_loader dedent

# tree-sitter-tactus tests (199 tests)
cd ../tree-sitter-tactus
nix-shell -p tree-sitter nodejs --run "tree-sitter generate && tree-sitter test"

# Single e2e test
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_add_comm
```
