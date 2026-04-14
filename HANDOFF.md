# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Current state

**63 end-to-end tests pass.** The pipeline works: user writes a proof fn with `by { }`, Tactus generates Lean, invokes Lean (with Mathlib if available), reports results through Verus's diagnostic system.

### What works

- **`by { }` syntax**: tactic bodies extracted verbatim from source file via byte range (preserves newlines, Unicode)
- **`import` keyword**: `import Mathlib.Tactic.Ring` threaded through proc macro → VIR → Lean
- **Mathlib**: Lake project at `~/.tactus/lean-project/`, precompiled oleans via `lake exe cache get`
- **All VIR spec-mode features**: exhaustive match on TypX and ExprX — no sorry, panics on invariant violations
- **Structs/enums/traits**: struct → `structure`, enum → `inductive`, trait → `class` with method dispatch
- **Generics**: type params, trait bounds, const generics, explicit type args in calls
- **Dependency ordering**: Tarjan's SCC, topological sort, mutual recursion → `mutual ... end`
- **Fully qualified names**: `lean_name(path)` prevents collisions, no namespace wrapper needed
- **Source map**: tactic line numbers in error messages
- **63 tests**: arithmetic, logic, datatypes, traits, generics, Mathlib tactics, error reporting
- **vstd builds**: `vargo build --release` → 1530 verified, 0 errors

### Architecture

```
User writes: proof fn lemma(x: nat) requires x > 0 ensures double(x) > x by { unfold double; omega }

verus-syn:   captures `by { }` brace group, records Span::byte_range() → (start, end)
proc macro:  emits #[verus::internal(tactic_span(start, end))], truncates body
VIR:         tactic_span: Option<(usize, usize)> on FunctionAttrsX
verifier:    reads source file at byte range → verbatim tactic text
             calls lean_verify::check_proof_fn(krate, fn, tactic_text, imports)
lean_verify:  generates .lean file (imports, prelude, spec fns, theorem)
             invokes `lake env lean` or `lean --stdin --json`
             parses JSON diagnostics, maps via source map
             reports through Verus diagnostic system
```

### Key design decisions

1. **Tactic body via byte range, not string literal** — proc macro stores `tactic_span(start_byte, end_byte)` as integers in the attribute. Verifier reads source file directly. No string escaping/unescaping.
2. **lean_verify depends on VIR directly** — no intermediate IR. Translators operate on VIR types.
3. **Zero-allocation dependency analysis** — lifetime-preserving `walk_expr` borrows from the krate AST. `HashSet<&str>` for references. No Arc clones.
4. **Fully qualified Lean names** — `lean_name(path)` skips crate prefix, joins segments with `.`. No collision detection needed.
5. **Exhaustive pattern matches** — `write_expr`, `write_typ`, `walk_expr` have no catch-all `_ =>`. New VIR variants cause compile errors.
6. **Choose → `Classical.epsilon`** — total function, no sorry needed.
7. **`#[must_use]` on `CheckResult`** — can't silently drop verification results.

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
      attributes.rs            ← MODIFIED: TacticSpan attr parsing
      rust_to_vir_func.rs      ← MODIFIED: threads tactic_span to FunctionAttrsX
      verifier.rs              ← MODIFIED: reads source file, routes to Lean
    rust_verify_test/tests/
      tactus.rs                ← 63 end-to-end tests (1108 lines)
    vir/src/
      ast.rs                   ← MODIFIED: tactic_span: Option<(usize, usize)>
```

## What we learned from code review

### Quality principles (Torvalds-level)

1. **No sorry in generated output.** Every VIR feature either has a proper Lean translation or panics on invariant violation. "Sorry" is silent unsoundness.
2. **Exhaustive matches over catch-all.** If VIR adds a variant, the compiler tells you. `_ => {}` hides bugs.
3. **Avoid allocation in hot paths.** `write_name` checks `needs_sanitization` before allocating. `lean_name` has a fast path for single segments. Hypothesis names use direct char push for i<10.
4. **No manual string escaping.** The byte-range approach avoids string-literal roundtrip entirely. When we tried `source_text()` → string attribute → attribute parser, the `\n` ↔ `\\n` roundtrip was fragile and required unescaping.
5. **Store data at the right level.** Integers (byte offsets) pass through attributes cleanly. Strings with newlines don't. Choose the representation that avoids encoding issues.
6. **Don't roll your own when established code exists.** We initially wrote a custom expression walker, then switched to VIR's built-in `expr_visitor_walk`, then wrote a minimal lifetime-preserving `walk_expr` when we needed `&'a` borrows. Each step was justified.
7. **`format!` allocates.** Use `out.push_str()` sequences instead of `format!()` in writers. Every `format!(" ({} : Type)", id)` is a temporary String allocation.
8. **Test every code path.** Each round of testing caught real bugs: missing type args, wrong const generic params, precedence issues, name collisions.

### Anti-patterns we caught and fixed

- **`TokenStream::to_string()` collapses whitespace** — replaced with byte-range file reading
- **`Arc::clone()` in dependency analysis** — replaced with lifetime-preserving borrows (`&'a`)
- **`HashSet<String>` for name tracking** — replaced with `HashSet<&'a str>` (zero allocation)
- **Index-based collision detection** — replaced with fully qualified names (simpler, correct by construction)
- **Sorry as fallback** — replaced with exhaustive handling + panic on invariant violations
- **`sorry` in `Choose`** — replaced with `Classical.epsilon` (total, sound)
- **Manual unescape of `\n`** — replaced with byte-range approach (no escaping at all)

## What remains to be done

### Immediate: Fork rustc_lexer for `//` comments in `by { }`

**The blocking issue.** Rust's lexer treats `//` inside `by { }` as a line comment, eating the closing `}`. Users can't write Lean comments (`--` works as `- -` tokens, but `//` doesn't). This also blocks Unicode support (DESIGN.md's `⟨⟩`, `·`, `∀` etc.).

The fix: modify `rustc_lexer` in the Verus fork to not interpret `//` as comments inside brace groups that follow the `by` keyword. This requires adding context to the otherwise-context-free lexer.

Alternative: accept the limitation for now (users use `--` not `//`, and semicolons for multi-line). Document it.

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

# Run tests (63 tests, 57 core + 6 Mathlib)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Quick compile check
RUSTC_BOOTSTRAP=1 cargo check -p rust_verify

# Single test
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_add_comm
```

## Git log (this session)

```
8fd59cd Fix setup-mathlib.sh: auto-detect Lean version, pin matching Mathlib tag
708037a Final review fixes: exhaustive binop, no-alloc names, Choose→epsilon, setup script
5bd091b 63 tests: or-pattern, const generics, nested enums + const generic param fix
06ee43c 60 tests: exists, precedence, fixed-width types, multi type params
40259fd 50 tests, generic type args, struct update, full coverage
849a998 Fix write_method_type self detection: starts_with instead of contains
4ddf325 Full VIR spec-mode coverage, fully qualified names, no sorry
746dbd9 Track A complete + Track D (structs/enums/traits) + architectural refactor
267c7dc Update HANDOFF.md: current state, tracks B/C/D, lessons learned
```

(Plus ~10 earlier commits: lean_verify crate, proc macro, VIR threading, initial pipeline)
