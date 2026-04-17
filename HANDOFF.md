# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Current state

**63 end-to-end tests pass.** The pipeline works: user writes a proof fn with `by { }`, Tactus generates Lean, invokes Lean (with Mathlib if available), reports results through Verus's diagnostic system.

**FileLoader implemented.** Tactic blocks are sanitized before rustc's lexer sees them, enabling Unicode (`⟨⟩·∀∃`) and Lean syntax (`--`, `/- -/`) in tactic bodies.

**tree-sitter-tactus grammar done.** 184 tests passing: Lean-aware tactic body rules plus all inherited Rust tests.

### What works

- **`by { }` syntax**: tactic bodies extracted verbatim from source file via byte range (preserves newlines, Unicode)
- **FileLoader sanitization**: `TactusFileLoader` intercepts `read_file()`, replaces tactic block content with spaces before rustc lexes. Byte offsets preserved. Handles `--`, `/- -/` (nestable), `"..."`, nested `{ }`.
- **tree-sitter-tactus**: Lean-aware grammar for tactic blocks. `_tactic_brace_body` handles all Lean syntax. `line_comment` stays in `extras` so `//` comments work everywhere in Rust.
- **`import` keyword**: `import Mathlib.Tactic.Ring` threaded through proc macro → VIR → Lean
- **Mathlib**: Lake project at `~/.tactus/lean-project/`, precompiled oleans via `lake exe cache get`
- **All VIR spec-mode features**: exhaustive match on TypX and ExprX — no sorry, panics on invariant violations
- **Structs/enums/traits**: struct → `structure`, enum → `inductive`, trait → `class` with method dispatch
- **Generics**: type params, trait bounds, const generics, explicit type args in calls
- **Dependency ordering**: Tarjan's SCC, topological sort, mutual recursion → `mutual ... end`
- **Fully qualified names**: `lean_name(path)` prevents collisions, no namespace wrapper needed
- **Source map**: tactic line numbers in error messages
- **vstd builds**: `vargo build --release` → 1530 verified, 0 errors

### Architecture

```
User writes: proof fn lemma(x: nat) requires x > 0 ensures double(x) > x by { unfold double; omega }

FileLoader:  TactusFileLoader.read_file() sanitizes tactic block content → spaces
             rustc sees: by {                              }
             byte offsets preserved — proc macro's Span::byte_range() still correct

verus-syn:   captures `by { }` brace group, records Span::byte_range() → (start, end)
proc macro:  emits #[verus::internal(tactic_span(start, end))], truncates body
VIR:         tactic_span: Option<(usize, usize)> on FunctionAttrsX
verifier:    reads ORIGINAL source file at byte range → verbatim tactic text
             calls lean_verify::check_proof_fn(krate, fn, tactic_text, imports)
lean_verify:  generates .lean file (imports, prelude, spec fns, theorem)
             invokes `lake env lean` or `lean --stdin --json`
             parses JSON diagnostics, maps via source map
             reports through Verus diagnostic system
```

### Key design decisions

1. **FileLoader for Unicode/Lean syntax** — `TactusFileLoader` sanitizes tactic blocks before rustc's lexer. Same-length replacement preserves byte offsets. No rustc fork needed.
2. **`//` not allowed in tactic blocks** — Lean's `//` (integer division) must be written as `Nat.div`/`Int.div`. This avoids an unresolvable conflict: tree-sitter's `extras` are global and `line_comment` can't be context-disabled. Explored extensively: `prec(100)`, `prec.dynamic`, removing from extras — none work cleanly.
3. **Tactic body via byte range, not string literal** — proc macro stores `tactic_span(start_byte, end_byte)` as integers in the attribute. Verifier reads source file directly. No string escaping/unescaping.
4. **lean_verify depends on VIR directly** — no intermediate IR. Translators operate on VIR types.
5. **Zero-allocation dependency analysis** — lifetime-preserving `walk_expr` borrows from the krate AST. `HashSet<&str>` for references. No Arc clones.
6. **Fully qualified Lean names** — `lean_name(path)` skips crate prefix, joins segments with `.`. No collision detection needed.
7. **Exhaustive pattern matches** — `write_expr`, `write_typ`, `walk_expr` have no catch-all `_ =>`. New VIR variants cause compile errors.
8. **Choose → `Classical.epsilon`** — total function, no sorry needed.
9. **`#[must_use]` on `CheckResult`** — can't silently drop verification results.

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document
  HANDOFF.md                   ← this file
  dependencies/
    syn/src/verus.rs           ← MODIFIED: tactic_by with byte_range()
  source/
    lean_verify/               ← 1731 lines: Lean generation + invocation
      TactusPrelude.lean       ← Lean prelude (real .lean file)
      scripts/setup-mathlib.sh ← Mathlib setup script
      src/
        dep_order.rs           ← dependency analysis: topo sort, Tarjan's SCC, walk_expr
        generate.rs            ← orchestrates file gen + Lean invocation
        to_lean_type.rs        ← TypX → Lean type, lean_name(), sanitize_ident()
        to_lean_expr.rs        ← ExprX → Lean expr, precedence parens, write_name()
        to_lean_fn.rs          ← FunctionX → def/theorem, source map, datatypes, traits
        lean_process.rs        ← invoke lean, parse JSON diagnostics, format errors
        project.rs             ← ~/.tactus/lean-project/ detection
        prelude.rs             ← include_str! of TactusPrelude.lean
      tests/integration.rs     ← 7 standalone Lean tests
    builtin_macros/src/
      syntax.rs                ← MODIFIED: by {} detection, byte range capture
    rust_verify/src/
      file_loader.rs           ← TactusFileLoader: sanitizes tactic blocks + 17 unit tests
      attributes.rs            ← MODIFIED: TacticSpan attr parsing
      rust_to_vir_func.rs      ← MODIFIED: threads tactic_span to FunctionAttrsX
      verifier.rs              ← MODIFIED: installs FileLoader, reads source, routes to Lean
    rust_verify_test/tests/
      tactus.rs                ← 63 end-to-end tests (1108 lines)
    vir/src/
      ast.rs                   ← MODIFIED: tactic_span: Option<(usize, usize)>

tree-sitter-tactus/           ← separate repo (to be added as submodule)
  grammar.js                  ← Tactus grammar: Rust + Lean tactic block rules
  src/scanner.c               ← external scanner (strings, raw strings, block comments)
  test/corpus/
    tactic_blocks.txt          ← 36 tactic-specific tests
    declarations.txt           ← fixed attribute test expectations
```

## What we learned

### FileLoader design (this session)

We explored multiple approaches for handling Unicode/Lean syntax in tactic blocks:

1. **Fork rustc_lexer** — rejected: Verus uses stock rustc (toolchain 1.94.0), not a forked compiler. Would require building a custom rustc.
2. **Raw string syntax** (`by r#"..."#`) — rejected: feels hacky, no syntax highlighting inside strings.
3. **tree-sitter in FileLoader** — explored extensively, but tree-sitter's `extras` are global (no way to disable `line_comment` for specific rules). Required adding `line_comment` to dozens of grammar rules, creating unresolvable conflicts between expression rules.
4. **Remove `line_comment` from extras** — explored: works for most cases but `field_expression` (prec 15) and `range_expression` steal comments from `if`/`while`/`for` conditions. `prec.dynamic` can't override static shift/reduce resolution.
5. **FileLoader + disallow `//` in tactics** — final solution: simple, clean, no conflicts.

Key tree-sitter lessons:
- **Extras are truly global** — no grammar-level mechanism to disable them for specific rules
- **`prec()` doesn't override extras** — extras are consumed between ALL tokens regardless of precedence
- **`prec.dynamic()` can't override static resolution** — only works when GLR paths complete successfully
- **`repeat($.line_comment)` before operators steals from parent rules** — `field_expression` at prec 15 grabs comments meant for `if_expression`

### Quality principles (from earlier sessions)

1. **No sorry in generated output.** Every VIR feature either has a proper Lean translation or panics on invariant violation.
2. **Exhaustive matches over catch-all.** If VIR adds a variant, the compiler tells you.
3. **Avoid allocation in hot paths.** `write_name` checks `needs_sanitization` before allocating.
4. **No manual string escaping.** Byte-range approach avoids string-literal roundtrip entirely.
5. **Store data at the right level.** Integers (byte offsets) pass through attributes cleanly.
6. **Test every code path.** Each round of testing caught real bugs.

## What remains to be done

### Immediate next steps

1. **Wire FileLoader end-to-end** — the `TactusFileLoader` is installed in the `config` callback and has 17 passing unit tests. Need to verify it works with actual tactic blocks containing Unicode and Lean syntax in the end-to-end tests. May need to add new e2e tests with Unicode tactics.

2. **Add `//` detection in tactic bodies** — at verification time, when extracting tactic text from the original file, check for `//` and emit a clear error: "use Nat.div/Int.div instead of // in tactic blocks."

3. **tree-sitter-tactus as submodule** — currently a separate repo. Should be added as a git submodule inside `tactus/`. The grammar is complete (184 tests) but not yet integrated as a dependency.

### Track B: Exec fn VC generation (3-6 months)

Implement `sst_to_lean.rs` — weakest-precondition VC generation from SST targeting Lean. See DESIGN.md for WP rules. This is the largest remaining work item.

### Track C: vstd translation

Build VIR path → Lean name lookup table for `vstd::seq::Seq`, `vstd::set::Set`, etc. Expand `TactusPrelude.lean` with Seq/Set/Map definitions.

### Track D completion: full trait/type support

Trait impls as Lean instances. Associated types. Type projections. These are partially working but need more tests.

### Other

- Per-module Lean generation (currently one .lean per proof fn)
- IDE integration (goal states in editor)
- `HANDOFF.md` and `DESIGN.md` may drift — keep them updated
- Update `setup-mathlib.sh` when Lean/Mathlib versions change

## Setup and testing

```bash
cd tactus/source

# First-time build
cd ../tools/vargo && cargo build --release && cd ../../source
PATH="../tools/vargo/target/release:$PATH" vargo build --release

# Mathlib setup (optional, ~5 min download)
cd lean_verify && ./scripts/setup-mathlib.sh && cd ..

# Run end-to-end tests (63 tests, 57 core + 6 Mathlib)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Quick compile check
RUSTC_BOOTSTRAP=1 cargo check -p rust_verify

# FileLoader unit tests (17 tests)
RUSTC_BOOTSTRAP=1 cargo test -p rust_verify --lib -- file_loader

# tree-sitter-tactus tests (184 tests)
cd ../tree-sitter-tactus
nix-shell -p tree-sitter nodejs --run "tree-sitter generate && tree-sitter test"

# Single e2e test
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_add_comm
```
