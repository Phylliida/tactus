# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions.

## Current state (2026-04 session end)

**109 end-to-end tests + 1 coverage test + 35 unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

### Recent session summary (Track A stabilization → Track B first slice → infrastructure hardening)

This session landed 13 commits on `main`:

1. **Track B first slice (`cac0f28`)** — `sst_to_lean.rs` generates a weakest-precondition theorem for `#[verifier::tactus_auto]` exec fns. Handles straight-line code only (Block + Return + Assign). On-disk Lean artifacts replaced stdin piping.
2. **Slice 1 review (`e2b2fcb`)** — sound assert/assume handling (they were being silently dropped); expression-level support check so unsupported forms fail cleanly; preamble extraction; shared helpers.
3. **AST refactor (`decbc4b`)** — replaced string-based Lean emission with typed AST (`lean_ast.rs`) and precedence-aware pretty-printer (`lean_pp.rs`). All `write_*` functions now build AST nodes; `pp_commands` renders once.
4. **AST review (`061c459`)** — killed dead back-compat wrappers, deduplicated helpers (`ensures_conj` → `and_all`, `sanitize_ident` → `sanitize`), dropped unused AST fields (`span`, `noncomputable: bool`, `Xor`), made `If.else_` optional, fixed the `fun` hack in instance method bodies.
5. **Edge cases (`85874c1`)** — added `ExprNode::Anon` (Lean's `⟨⟩`), `BinOp::Prod` (`×`), block fold via nested Let/Match; panics on unreachable variants (`Header`, `BreakOrContinue`) instead of silent empty emission.
6. **dep_order fix + tuple rendering (`24aacaa`)** — the walker treated `ReadPlace`, `Match` scrutinee, and the `BorrowMut` family as leaves, dropping any `Call` buried inside a `Place`. Added `walk_place`. Tuple types render as `Int × Int`, constructors as `⟨a, b⟩`, field access as `.1`/`.2` (Lean 1-indexed) via a shared `field_access_name` helper.
7. **Sanity check + invariant (`e65df10`)** — new `sanity.rs` module walks the final `Vec<Command>` and verifies every `Var(name)` reference resolves to a local, an earlier def, or a Lean built-in. Panics in debug builds with a pointed error. Invariant comment on `walk_expr`. Tuple test uses inequality to avoid tactic-fragility.
8. **Coverage matrix (`8585e22`)** — subprocess-aware instrumentation in `dep_order::walk_expr`/`walk_place`. When `$TACTUS_COVERAGE_FILE` is set, the verifier appends visited variant names. A dedicated test binary (`tactus_coverage.rs`) drives curated snippets and asserts the expected variant set was covered.

## Architecture

### Full pipeline

```
User writes:
  proof fn lemma(x: nat) requires x > 0 ensures double(x) > x by { unfold double; omega }
  — OR —
  #[verifier::tactus_auto] fn add_one(x: u32) requires x < MAX ensures r == x + 1 { x + 1 }

FileLoader:
  tree-sitter-tactus parses file, finds tactic_block nodes inside verus! { }
  replaces content between { } with spaces (same byte offsets)
  rustc sees: by {                              }
  installed in BOTH compilation passes

verus-syn:    captures `by { }` brace group, records Span::byte_range() → (start, end)
proc macro:   emits #[verus::internal(tactic_span(start, end))], truncates body
              — OR for exec fns — emits #[verifier::tactus_auto] marker
VIR:          tactic_span: Option<(String, usize, usize)> — file path + byte range
              tactus_auto: bool on FunctionAttrs
              file path resolved via SourceMap at VIR construction time

verifier.rs routes:
  tactic_span  → lean_verify::check_proof_fn(krate, fn, tactic_text, imports, crate_name)
  tactus_auto  → lean_verify::check_exec_fn(krate, vir_fn, fn_sst, check, imports, crate_name)

lean_verify pipeline (AST-based):
  1. krate_preamble(krate, ...) → Vec<Command> (imports, prelude, namespace, traits, datatypes,
     spec fns, trait impls; walks dep_order to find transitively-referenced decls)
  2. Theorem builder:
       proof_fn  → to_lean_fn::proof_fn_to_ast  (Tactic::Raw from user text)
       exec_fn   → sst_to_lean::exec_fn_theorem_to_ast  (Tactic::Named("tactus_auto"))
  3. debug_check(&cmds) — sanity::check_references panics on unresolved references
     (gated on #[cfg(debug_assertions)])
  4. pp_commands(&cmds) → PpOutput { text, tactic_starts }
     — tactic_starts[0] gives 1-indexed line where `Tactic::Raw` body begins, for source map
  5. write_lean_file(path, text) → target/tactus-lean/{crate}/{fn}.lean
  6. lean_process::check_lean_file(path, lake_dir) — invokes `lake env lean --json <path>`
  7. Parse JSON diagnostics, map via LeanSourceMap, report through Verus
```

### lean_verify module map

```
lean_verify/src/
  lean_ast.rs        Typed AST: Command / Expr / Tactic / Binder / Pattern /
                     BinOp / UnOp. `and_all` helper for right-assoc conjunctions.
  lean_pp.rs         Precedence-aware pretty-printer. 28 unit tests covering
                     associativity, parenthesization, tuple/product rendering,
                     tactic-start tracking. Returns PpOutput { text, tactic_starts }.

  dep_order.rs       VIR dependency walking. `walk_expr` + `walk_place` — the
                     critical invariant is documented at walk_expr: every Expr
                     AND every Place sub-field must be recursed into. Adds
                     coverage instrumentation (file-append) when
                     $TACTUS_COVERAGE_FILE is set.

  to_lean_type.rs    TypX → lean_ast::Expr. Tuple types fold to nested
                     BinOp::Prod. sanitize() handles keywords + %/@/# chars.
  to_lean_expr.rs    VIR-AST Expr → lean_ast::Expr. Includes field_access_name
                     (Dt::Tuple + numeric → n+1, Dt::Path + numeric → valN).
  to_lean_sst_expr.rs  SST Exp → lean_ast::Expr. HasType/IntegerTypeBound
                       render as True (type-propositions hold trivially in
                       Lean's typed world).
  to_lean_fn.rs      VIR decls → lean_ast::Command (Def / Theorem / Datatype /
                     Class / Instance). Includes LeanSourceMap struct.
  sst_to_lean.rs     SST exec-fn body → lean_ast::Theorem via WP. Nests Let /
                     Assume (→) / Assert (∧) in source order. supported_body
                     gates unsupported SST forms with clean errors before
                     generation begins.
  generate.rs        Orchestration: builds Vec<Command>, runs sanity, pp's,
                     writes file, invokes Lean, formats errors.

  sanity.rs          Post-codegen reference check. Walks Theorem goals,
                     Def bodies, Class method sigs, Instance method bodies.
                     Tracks binders from Let/Lambda/Forall/Exists/Match. Panics
                     in debug builds with "unresolved X in context Y". 7 unit
                     tests.

  lean_process.rs    File-based Lean invocation (`lean --json <path>` or
                     `lake env lean --json <path>`).
  project.rs         Lake project discovery (tactus/lean-project/).
  prelude.rs         include_str! of TactusPrelude.lean.
  TactusPrelude.lean tactus_auto macro def + linter settings.
```

### Key design decisions (updated)

1. **Typed AST, not string concatenation.** `lean_ast.rs` + `lean_pp.rs` replaced ad-hoc `push_str` construction. Precedence is the pp's responsibility; callers construct nodes. Tests lock down precedence once instead of sprinkling defensive parens through every writer.
2. **On-disk Lean artifacts, not stdin piping.** Every generated file lands in `target/tactus-lean/{crate}/{fn}.lean`. Makes debugging trivial (`cat` the file), Lean error positions refer to real paths, and future olean caching can slot in.
3. **Sanity check on every generation (debug builds).** Catches the class of bug where `dep_order` drops a reference — panics with "unresolved `foo`" instead of a cryptic Lean error.
4. **Subprocess-aware coverage instrumentation.** `walk_expr` / `walk_place` append variant names to `$TACTUS_COVERAGE_FILE` when set. `OnceLock`-cached lookup — zero cost when disabled.
5. **Assert/assume as WP nesting, not conjoined.** `assert(P); assume(P)` (which Verus generates for user `assert(P)`) must NOT trivially satisfy itself. Our goal-builder uses `(P) ∧ (rest)` for asserts and `(P) → rest` for assumes, so asserts must prove without subsequent assumes' help. This was a real bug found during slice 1 review.
6. **`_tactus_body_` reserved prefix.** Exec-fn theorem names start with `_tactus_body_` to avoid collision with user code (Rust doesn't produce `_tactus_`-prefixed identifiers).
7. **Two-layer dependency walking.** `dep_order::walk_expr` recurses through ExprX; `dep_order::walk_place` recurses through PlaceX. Previously, Place variants were leaves — `ReadPlace(Field(Temporary(Call(f, ...))))` hid `f` from the walker.
8. **Tuple rendering.** `Dt::Tuple(n)` → `T₁ × T₂ × …` type, `⟨a, b, …⟩` constructor, `.1`/`.2` field access (Lean 1-indexed; Verus is 0-indexed, so we shift by 1).
9. **Exec-mode forms panic when seen in spec bodies.** Not silent no-op. `Header`, `BreakOrContinue`, exec Assign/Loop/Return — all panic rather than emit `Raw("")`.
10. **Exhaustive matches, no catch-all `_ =>`.** New VIR variants force compile errors at every walker / writer site. Backed by coverage test to make sure the walker is exercised.

## Track B status

`#[verifier::tactus_auto]` routes an exec fn's body through `sst_to_lean` instead of Z3.

### Slice 1: straight-line code ✅

Supports: `StmX::Block`, `StmX::Assign`, `StmX::Return { inside_body: false }`, `StmX::Assert`, `StmX::Assume`, `StmX::Air` / `StmX::Fuel` / `StmX::RevealString` (transparent).

Semantic model (WP, in body order):
- `let x = e` → `let x := e; rest`
- `assume(P)` → `(P) → rest`
- `assert(P)` → `(P) ∧ (rest)`  — crucially NOT conjoin-everything, so `assert(P); assume(P)` (Verus's desugaring of `assert(P)`) doesn't trivially satisfy itself
- `return e` → wrap ensures in `let <ret> := e; <ensures_conj>`

Tests: `test_exec_const_return`, `test_exec_add_one`, `test_exec_wrong_ensures`, `test_exec_assert_holds`, `test_exec_assert_fails`.

### Slice 2–5: remaining work (pending tasks)

| # | Task | Notes |
|---|------|-------|
| 3 | **if/else WP rule** | `ExprNode::If` already has `else_: Option<Box<Expr>>` + precedence-tested pp. WP rule: `(c → wp(t)) ∧ (¬c → wp(e))`. Add `StmX::If` to `supported_body`. |
| 4 | **Mutation via SSA** | `let mut x = …; x = …;` → variable versioning. Maintain a rename map as we walk the body; each mutation creates `x_1`, `x_2`, etc. |
| 5 | **Loop obligations** | `while cond invariant I decreases D { body }` → three theorems: init (`requires ⟹ I`), maintain (`I ∧ cond ⟹ wp(body, I) ∧ D decreases`), use (`I ∧ ¬cond ⟹ ensures`). Each becomes its own `Command::Theorem`. |
| 6 | **Overflow obligations** | Each arithmetic op on fixed-width types emits an `Assert` for `0 ≤ result ∧ result < 2^bits`. Currently silently skipped — all `test_exec_*` functions use `u8` with generous bounds. |

Each new slice should:
1. Extend `sst_to_lean::supported_body` / `supported_stmt` to accept the new form.
2. Extend `sst_to_lean::build_goal` to fold it into the WP nesting structure.
3. If it produces new AST shapes, extend `lean_ast` and `lean_pp`.
4. Add one or more snippets to `tactus_coverage::run_snippets` that exercise the new walker path.
5. Add the new ExprX / PlaceX variants to `EXPECTED_EXPR_VARIANTS` / `EXPECTED_PLACE_VARIANTS` if they become reachable.
6. Update the expected variants in `sanity.rs` only if new Lean-level builtins become referenced.

## Testing infrastructure

### Test suites at a glance

| Binary | Count | What it tests |
|---|---|---|
| `cargo test -p lean_verify --lib` | 35 | AST pp (precedence, tuples, indexing), type translation, sanity check scope tracking, lean_process |
| `cargo test -p lean_verify --test integration` | 7 | Tactus-prelude + Lean invocation end-to-end on hand-written Lean |
| `vargo test -p rust_verify_test --test tactus` | 109 | Full e2e: VIR → AST → Lean for proof fns + exec fns |
| `vargo test -p rust_verify_test --test tactus_coverage` | 1 | Coverage assertion: expected VIR variants all hit by `walk_expr`/`walk_place` |
| `vargo build --release` (vstd) | 1530 | Regression guard: vstd proof library still verifies |

### Sanity check (`lean_verify/src/sanity.rs`)

**What it does**: after `generate.rs` builds the final `Vec<Command>`, walks every theorem goal, def body, class method sig, and instance method body. For each `ExprNode::Var(name)`, verifies `name` resolves to either:
- A local binder (def/theorem params, `let`, `λ`, `∀`/`∃`, match-arm pattern)
- An earlier top-level `Command` in the same file
- A Lean/Mathlib built-in on a small allowlist (`Nat`, `Int`, `Prop`, `True`, ...)
- A dotted name (`Classical.arbitrary`, `Nat.succ` — trust Lean)
- `«…»` keyword-quoted or `_`

Panics in debug builds when a violation is found, pointing at the exact identifier. The generator-caught-vs-Lean-caught distinction matters: Lean errors say "unknown identifier" and point at a line in the generated file; our panic says "unresolved `foo` in theorem `bar`" and tells you it's a dep_order bug.

**Gated on** `#[cfg(debug_assertions)]`. Release builds skip the check (perf). Future: add a `TACTUS_STRICT_CODEGEN` env var to force-enable in release.

### Coverage matrix (`rust_verify_test/tests/tactus_coverage.rs`)

**What it does**: a dedicated test binary that drives a curated battery of spec/proof snippets through the full pipeline, with walker instrumentation active. Asserts that every variant on the expected list was visited at least once.

**How the instrumentation works**:

1. `dep_order.rs` has `record(kind: &str)` that appends `kind\n` to `$TACTUS_COVERAGE_FILE` if set. `OnceLock<Option<PathBuf>>` memoizes the env lookup — zero cost when unset.
2. `walk_expr` calls `record(expr_variant_name(&expr.x))` at entry.
3. `walk_place` calls `record("Place::" + place_variant_name(&place))` at entry.
4. `expr_variant_name` and `place_variant_name` are exhaustive matches — compiler forces updates when a new variant is added.

**How the test uses it**:

1. Sets `$TACTUS_COVERAGE_FILE` to a pid-keyed temp file.
2. Runs `verify_one_file` on each snippet (subprocess spawn; env is inherited).
3. Reads the file back; parses the set of visited variant names.
4. Asserts each entry in `EXPECTED_EXPR_VARIANTS` / `EXPECTED_PLACE_VARIANTS` appears.
5. On failure, prints missing variants + full visited set.

**Why a separate test binary**: setting env vars in-process would affect sibling test binaries running in parallel. Separate binary = separate process = own env.

### Adding new variants to coverage

When a new feature causes the walker to hit a new ExprX/PlaceX variant:

1. Add a minimal snippet in `tactus_coverage::run_snippets` that forces the walker through it. Each snippet must have a proof fn whose ensures / spec fn body reaches the variant (that's how `dep_order` walks it).
2. Add the variant name to `EXPECTED_EXPR_VARIANTS` (or `EXPECTED_PLACE_VARIANTS`).
3. Run the test locally. If the variant still isn't hit, the snippet isn't triggering it — often because Verus simplifies or routes through a different VIR node. Check by running with `TACTUS_COVERAGE_FILE=/tmp/dbg.txt vargo test -p rust_verify_test --test tactus_coverage` and inspecting `/tmp/dbg.txt`.

### Variants explicitly not in scope for coverage

Documented in `tactus_coverage.rs`'s module comment. Exec-only forms (Assign, Loop, Return, BreakOrContinue, NonSpecClosure, AssignToPlace, the BorrowMut family) never appear in spec fn bodies. Transparent markers that VIR strips (Header, Fuel, RevealString, AirStmt, Nondeterministic, AssertQuery, AssertCompute, AssertAssumeUDTI, OpenInvariant, NeverToAny, Old, EvalAndResolve, ProofInSpec, VarAt, VarLoc, Loc, ExecFnByName, ImplicitReborrowOrSpecRead) aren't in user-written spec code.

### Known limitations of the coverage matrix

1. **The coverage matrix catches "variant never recorded", not "walker skips sub-fields".** If the walker enters an `If` but doesn't recurse into `cond`, we still record `"If"` at entry. We'd only notice if a Call inside the skipped cond doesn't surface downstream. The **sanity check** catches that case separately (because the Call's Fun isn't marked needed and the Def doesn't get emitted). Combined defense: sanity + coverage covers most real walker bugs.
2. **Not a proof of walker correctness.** A walker bug that skips a sub-field whose contents contain nothing interesting (no fn references, no Places) would go undetected.
3. **Expected ⊂ actual.** The test only catches regressions of expected-to-be-covered variants. New variants added to VIR won't trigger a failure until someone updates the expected list.

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
    grammar.js
    src/scanner.c
    test/corpus/*.txt          ← 199 grammar tests
  dependencies/
    syn/src/verus.rs           ← MODIFIED: tactic_by with byte_range()
  source/
    lean_verify/
      TactusPrelude.lean       ← tactus_auto macro + linter settings
      scripts/setup-mathlib.sh
      src/
        lean_ast.rs            ← NEW: typed Lean AST
        lean_pp.rs             ← NEW: precedence-aware pp + tactic-start tracking
        sanity.rs              ← NEW: post-codegen reference check
        dep_order.rs           ← walker + coverage instrumentation
        generate.rs            ← orchestration + debug_check
        to_lean_type.rs        ← TypX → Expr
        to_lean_expr.rs        ← VIR Expr → Expr + field_access_name
        to_lean_sst_expr.rs    ← SST Exp → Expr
        to_lean_fn.rs          ← VIR decls → Commands + LeanSourceMap
        sst_to_lean.rs         ← WP generator for exec fns
        lean_process.rs        ← file-based Lean invocation
        project.rs             ← Lake project discovery
        prelude.rs             ← include_str! of TactusPrelude.lean
      tests/integration.rs     ← 7 standalone Lean tests
    builtin_macros/src/
      syntax.rs                ← by {} detection, byte range capture
    rust_verify/src/
      file_loader.rs           ← tree-sitter FileLoader + 36 unit tests
      driver.rs                ← FileLoader in both compilation passes
      attributes.rs            ← TacticSpan + TactusAuto attr parsing
      rust_to_vir_func.rs      ← threads tactic_span + tactus_auto
      verifier.rs              ← routes proof fn AND exec fn to Lean
      util.rs                  ← dedent() + 8 unit tests
    rust_verify_test/tests/
      tactus.rs                ← 109 end-to-end tests
      tactus_coverage.rs       ← NEW: coverage matrix test binary
    vir/src/
      ast.rs                   ← FunctionAttrs.tactic_span + tactus_auto
```

## Known limitations and tradeoffs

Documented here rather than surfaced as bugs; future sessions can prioritize.

1. **Two `PlaceX` walkers.** `dep_order::walk_place` and `to_lean_expr::place_to_expr` both enumerate `PlaceX`. Compiler enforces exhaustiveness so new variants fail to compile; but semantic changes need to happen in two places.
2. **`debug_check` only in debug builds.** Release users running Tactus get the cryptic Lean error instead of our pointed panic. Option: add `TACTUS_STRICT_CODEGEN` env.
3. **Sanity check's builtin allowlist is static.** New bare Lean names (if any become common) need the list updated. Dotted names (`Classical.*`, `Nat.*`) already pass through.
4. **`noncomputable` baked into pp.** Every emitted `def` is `noncomputable def`. Correct for all current users; revisit if we ever emit computable helpers.
5. **Exec-fn source mapping not wired.** Sanity check + coverage instrumentation point at the generator; when Lean rejects an exec-fn body, the error points at the generated file's line, not the Rust source. TODO in `sst_to_lean::exec_fn_theorem_to_ast`.
6. **Coverage test is ~30s.** Seven subprocess spawns, each compiling the test input from scratch. Acceptable for now.
7. **`//` not allowed in tactic blocks.** tree-sitter's `line_comment` extra consumes `//` globally. Reported as a clear error at verification time; use `Nat.div` / `Int.div`.
8. **Per-module Lean generation not implemented.** One `.lean` file per proof fn / exec fn. Fine at our scale; future work when we have many fns per module.

## Running tests

```bash
cd tactus/source

# First-time build (builds vargo first if needed)
cd ../tools/vargo && cargo build --release && cd ../../source
PATH="../tools/vargo/target/release:$PATH" vargo build --release
# → "1530 verified, 0 errors"

# Mathlib setup (~5 min download, ~2 GB)
cd lean_verify && ./scripts/setup-mathlib.sh && cd ..
# or: TACTUS_LEAN_PROJECT=/custom/path ./scripts/setup-mathlib.sh

# ── Full test suite ────────────────────────────────────────────────
# 109 end-to-end tests
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Coverage matrix (1 test, asserts walker visits the expected variant set)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus_coverage

# 35 unit tests (AST pp, sanity check, type translation)
cargo test -p lean_verify --lib

# 7 integration tests (Lean invocation end-to-end)
cargo test -p lean_verify --test integration

# ── Single test / debug ────────────────────────────────────────────
# One e2e test
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_add_comm

# Inspect generated Lean for a test
cat rust_verify_test/target/tactus-lean/test_crate/<fn_name>.lean

# Dump coverage trace for debugging
rm -f /tmp/cov.txt && TACTUS_COVERAGE_FILE=/tmp/cov.txt \
  PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_tuple_return
sort -u /tmp/cov.txt

# ── Other ──────────────────────────────────────────────────────────
# Quick compile check (no tests)
RUSTC_BOOTSTRAP=1 cargo check -p rust_verify

# FileLoader + dedent unit tests
RUSTC_BOOTSTRAP=1 cargo test -p rust_verify --lib -- file_loader dedent

# tree-sitter-tactus grammar tests (199 tests)
cd ../tree-sitter-tactus
nix-shell -p tree-sitter nodejs --run "tree-sitter generate && tree-sitter test"
```
