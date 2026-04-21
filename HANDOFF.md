# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions, including a comprehensive "Known deferrals, rejected cases, and untested edges" catalogue.

## Current state (2026-04 session end)

**152 end-to-end tests + 1 coverage test + 35 unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

**Track B status: all seven slices landed.** Exec fns can have: `let`-bindings, mutation (via Lean let-shadowing), if/else, early returns, loops (arbitrary nesting — sequential, nested, inside if-branches), function calls (direct named), and arithmetic with overflow checking. Most realistic Rust exec fns should verify, modulo documented restrictions (no trait-method calls, no `&mut` args, no generic calls, no break/continue — see DESIGN.md § "Known deferrals").

### Recent session landings

**Slice 4 — recursive `lift_if_value` for tail/let if-expressions (`3a6f379`).** `let x := if c then a else b; rest` now lifts to `(c → let x := a; rest) ∧ (¬c → let x := b; rest)` so `omega` can chew each branch. Peels through transparent wrappers (`Loc`, `Box`/`Unbox`, `CoerceMode`, `Trigger`) and through single-binder `ExpX::Bind(Let, …)` (Verus's preferred representation of `let y = …; y` blocks). Same helper handles `Return(if_expr)`.

**Slice 5 — loops (`7e3eb8b`, `436448a`, `2ace442`).** `StmX::Loop` contributes a conjunctive WP `I ∧ maintain ∧ havoc_continuation` inline into the enclosing goal. Recursive structure → handles arbitrary nesting + sequential + in-if-branch. `tactus_peel` (recursive Lean macro in the prelude) peels the resulting `∀` / `∧` structure; `tactus_auto` stays a dumb leaf closer. `collect_modifications` tracks `locally_declared` per-body so `let mut x` inside a loop doesn't leak into the outer's modified-var set. `_tactus_d_old` captures the decrease measure pre-body.

**Slice 6 — overflow obligations / u-types-as-Int soundness fix (`556b09e`, `a638af8`, `0054723`).** `HasType(e, U(n))` emits `0 ≤ e ∧ e < 2^n` instead of `True`. u-types render as Lean `Int` (not `Nat`) so subtraction semantics catch underflow. USize/ISize bounds wired via `usize_hi` / `isize_hi` prelude constants built on `arch_word_bits`.

**Slice 7 — `StmX::Call` (`491ddb1`).** Exec fn bodies can call other exec/proof/spec fns. Callee's spec is inlined via `vir_expr_to_ast` at each call site; no separate Lean definition emitted. WP: `(let p1 := a1; requires) ∧ ∀ ret, h_bound(ret) → (let p1 := a1; ensures_using_ret) → let dest := ret; wp(rest)`. Rejects trait methods, generics, `&mut` args.

**Architecture / FP passes (`3f048a9`, `7e3eb8b`, `436448a`, `2ace442`, `3a6f379`).**
- Smart constructors on `LExpr` (`and`, `implies`, `let_bind`, `forall`, `field_proj`, `app`, `lit_int`, etc.) replace 3-line `Box::new(LExpr::new(ExprNode::…))` chains everywhere.
- `walk` is pure — `fn walk(stm) -> Vec<BodyItem>` via `flat_map` instead of `&mut Vec` output param.
- `build_goal` / `build_wrapped` / `build_loop_conjunction` unified into `build_goal_with_terminator` parameterized on its terminal goal (`&LExpr`). Halved the duplication.
- Error messages include the generated `.lean` file path so diagnosing tactic failures doesn't require dropping into `lake env lean`.

**Earlier non-slice work** (for context, from the prior session's 13 commits): typed AST + precedence pp replacing string emission, sanity check on every codegen, property-coverage matrix via `$TACTUS_COVERAGE_FILE` env var, two-layer dependency walking (`walk_expr` + `walk_place`), tuple rendering as Lean products, reserved `_tactus_body_` prefix for emitted theorem names.

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
  2. build_fn_map(krate) → FnMap for StmX::Call inlining (exec fn path only)
  3. Theorem builder:
       proof_fn  → to_lean_fn::proof_fn_to_ast  (Tactic::Raw from user text)
       exec_fn   → sst_to_lean::exec_fn_theorems_to_ast  (Vec<Theorem>)
  4. debug_check(&cmds) — sanity::check_references panics on unresolved references
     (gated on #[cfg(debug_assertions)])
  5. pp_commands(&cmds) → PpOutput { text, tactic_starts }
     — tactic_starts[0] gives 1-indexed line where `Tactic::Raw` body begins, for source map
  6. write_lean_file(path, text) → target/tactus-lean/{crate}/{fn}.lean
  7. lean_process::check_lean_file(path, lake_dir) — invokes `lake env lean --json <path>`
  8. Parse JSON diagnostics, map via LeanSourceMap, report through Verus
     (error messages include the generated .lean path for easy inspection)
```

### WP emission for exec fns

`sst_to_lean::build_goal_with_terminator` is the single function that turns `BodyItem` sequences into a Lean `LExpr` goal, parameterized on its terminal value (the "terminator"). All five WP rules — `Let` / `Assume` / `Assert` / `Return` / control-flow — live in one match.

- **`Let(x, rhs)`** → `let x := rhs; wp(rest, terminator)`. If `rhs` is an `ExpX::If`, lifts via `lift_if_value` so omega sees each branch.
- **`Assume(P)`** → `P → wp(rest, terminator)`.
- **`Assert(P)`** → `P ∧ wp(rest, terminator)`. Crucially not just "conjoin everything" — Verus's `assert(P)` desugars to `Assert(P); Assume(P)`, and without the asymmetry the assert would trivially satisfy itself.
- **`Return(e)`** → `let <ret> := e; terminator` (or just `terminator` for unit returns). Early returns (`inside_body: true`) work the same way — the Return terminates its local sequence, upstream composition ignores the items after.
- **`IfThenElse { cond, then_items, else_items }`** → `(cond → wp(then ++ rest)) ∧ (¬cond → wp(else ++ rest))`. Rest duplicates into both branches.
- **`Loop { cond, invs, decrease, modified_vars, body_items }`** → `build_loop_conjunction` emits `I ∧ maintain ∧ havoc_continuation`. Maintain has its own local terminator `I ∧ D < _tactus_d_old`; the use-clause threads the outer `terminator` through. Arbitrary loop nesting works because the loop's contribution is itself just another `LExpr` that fits into the recursive framework.
- **`Call { callee, args, dest }`** → `build_call_conjunction` inlines the callee's `require` / `ensure` via Lean `let`-bindings that substitute params. WP is `requires_conj ∧ ∀ ret, h_bound(ret) → ensures_conj_with_ret → let dest := ret; wp(rest, terminator)`.

Theorems with no loops and no calls get the simple `Tactic::Named("tactus_auto")` tactic. Theorems with either get `Tactic::Raw("tactus_peel; all_goals tactus_auto")` — `tactus_peel` is a recursive Lean macro in the prelude that strips `∧` and `∀` structure until each leaf is arithmetic, then `tactus_auto` closes each.

### `lean_verify` module map

```
lean_verify/src/
  lean_ast.rs        Typed AST: Command / Expr / Tactic / Binder / Pattern /
                     BinOp / UnOp. Smart constructors (LExpr::and, implies,
                     let_bind, forall, app, lit_int, etc.) — call sites no
                     longer write Box::new(LExpr::new(ExprNode::…)) chains.
  lean_pp.rs         Precedence-aware pretty-printer. 28 unit tests covering
                     associativity, parenthesization, tuple/product rendering,
                     tactic-start tracking. Returns PpOutput { text, tactic_starts }.

  dep_order.rs       VIR dependency walking. `walk_expr` + `walk_place` — the
                     critical invariant is documented at walk_expr: every Expr
                     AND every Place sub-field must be recursed into. Adds
                     coverage instrumentation (file-append) when
                     $TACTUS_COVERAGE_FILE is set.

  to_lean_type.rs    TypX → lean_ast::Expr. Tuple types fold to nested
                     BinOp::Prod. u-types render as `Int` (not `Nat`) so
                     subtraction underflow is catchable. USize stays `Nat`
                     because Verus elides `as nat` casts from usize (breaks
                     const generics if changed). sanitize() handles keywords
                     + %/@/# chars.
  to_lean_expr.rs    VIR-AST Expr → lean_ast::Expr. Includes field_access_name
                     (Dt::Tuple + numeric → n+1, Dt::Path + numeric → valN).
                     HasType / IntegerTypeBound render via
                     to_lean_sst_expr::type_bound_predicate /
                     integer_type_bound_from_vir (shared with SST path).
  to_lean_sst_expr.rs  SST Exp → lean_ast::Expr. Exposes `type_bound_predicate`
                       (the refinement for each fixed-width int type),
                       `integer_type_bound_node` (numeric literal for
                       `u8::MAX` etc.), and clip_to_node (Nat↔Int coercion).
  to_lean_fn.rs      VIR decls → lean_ast::Command (Def / Theorem / Datatype /
                     Class / Instance). Includes LeanSourceMap struct. Proof
                     fn params pick up h_<name>_bound hypotheses via the
                     shared type_bound_predicate.
  sst_to_lean.rs     SST exec-fn body → Vec<Theorem> via WP. Core module for
                     Track B. See "WP emission" section above; key exports:
                     supported_body, exec_fn_theorems_to_ast, build_fn_map.
  generate.rs        Orchestration: builds Vec<Command>, runs sanity, pp's,
                     writes file, invokes Lean, formats errors. Error output
                     includes the generated .lean path.

  sanity.rs          Post-codegen reference check. Walks Theorem goals,
                     Def bodies, Class method sigs, Instance method bodies.
                     Tracks binders from Let/Lambda/Forall/Exists/Match. Panics
                     in debug builds with "unresolved X in context Y". Allow-
                     lists Tactus prelude names (arch_word_bits,
                     arch_word_bits_valid, usize_hi, isize_hi, tactus_peel).

  lean_process.rs    File-based Lean invocation (`lean --json <path>` or
                     `lake env lean --json <path>`).
  project.rs         Lake project discovery (tactus/lean-project/).
  prelude.rs         include_str! of TactusPrelude.lean.
  TactusPrelude.lean tactus_auto (leaf closer: rfl | decide | omega | simp_all),
                     tactus_peel (recursive ∧/∀ peeler), arch_word_bits axiom,
                     arch_word_bits_valid disjunction, usize_hi / isize_hi
                     Int defs, linter settings.
```

### Key design decisions

1. **Typed AST with smart constructors.** `lean_ast.rs` has 30+ constructors (`LExpr::and`, `implies`, `let_bind`, `forall`, `app`, etc.). Precedence is the pp's responsibility; callers build typed nodes.
2. **On-disk Lean artifacts.** Every generated file lands in `target/tactus-lean/{crate}/{fn}.lean`. Debuggable (`cat` the file) and referenced from error messages.
3. **Sanity check every generation (debug builds).** Catches "dep_order dropped a reference" class of bug with pointed errors; allowlist for Tactus prelude names.
4. **`tactus_auto` is a dumb leaf closer; `tactus_peel` is a recursive peeler.** Structural tactics — which `refine ⟨?_, ?_⟩` to use, which `intros` — belong at codegen time because the emitter knows the shape. Loops/calls emit `tactus_peel; all_goals tactus_auto`.
5. **Assert/assume as WP nesting, not conjoined.** `assert(P); assume(P)` (Verus's desugaring of user `assert(P)`) must NOT trivially satisfy itself. `(P) ∧ (rest)` for asserts vs `(P) → rest` for assumes.
6. **`_tactus_body_` / `_tactus_d_old` / `tactus_peel` reserved prefix.** Tool-generated names never collide with user code (Rust doesn't produce `_tactus_` or `tactus_`-prefixed identifiers).
7. **Two-layer dependency walking.** `dep_order::walk_expr` recurses through ExprX; `dep_order::walk_place` recurses through PlaceX. Place variants can hide Call refs inside; both walkers cover the full tree.
8. **Tuple rendering.** `Dt::Tuple(n)` → `T₁ × T₂ × …` type, `⟨a, b, …⟩` constructor, `.1`/`.2` field access (Lean 1-indexed).
9. **u-types render as Int, not Nat.** Lean's `Nat` truncates subtraction (`0 - 1 = 0`); rendering u8/u16/…/u128 as `Int` with both-sided bounds makes underflow catchable. USize keeps rendering as `Nat` — const-generic constraint (see DESIGN.md).
10. **Unified `build_goal_with_terminator`.** One function handles Let/Assume/Assert/Return/If/Loop/Call with a `&LExpr` terminator parameter. Loop's maintain uses its own local terminator (`I ∧ D < d_old`); call's `rest` threads the outer terminator through.
11. **Callees inlined, not defined.** Exec fn calls pull callee's `require`/`ensure` from its `FunctionX` at the call site — no Lean definition of the callee needed.
12. **Exhaustive matches, no catch-all `_ =>`.** New VIR variants force compile errors at every walker / writer site. Backed by coverage test to make sure the walker is exercised.

## Track B status

`#[verifier::tactus_auto]` routes an exec fn's body through `sst_to_lean` instead of Z3. All seven planned slices landed.

### Slice 1: straight-line code ✅

Supports: `StmX::Block`, `StmX::Assign`, `StmX::Return`, `StmX::Assert`, `StmX::Assume`, `StmX::Air` / `StmX::Fuel` / `StmX::RevealString` (transparent).

Tests: `test_exec_const_return`, `test_exec_add_one`, `test_exec_wrong_ensures`, `test_exec_assert_holds`, `test_exec_assert_fails`.

### Slice 2: if/else WP rule ✅

`StmX::If(cond, then, Option<else>)` folds to `(c → wp(then ++ rest)) ∧ (¬c → wp(else ++ rest))`.

Tests: `test_exec_if_assert_holds`, `test_exec_if_no_else`, `test_exec_if_assert_fails`, `test_exec_nested_if`, `test_exec_mutation_both_branches`.

### Slice 3: mutation via SSA ✅

No-op: Lean's let-shadowing gives SSA for free. `StmX::Assign` emits `let x := e` regardless of `is_init`.

Tests: `test_exec_mut_seq`, `test_exec_mut_in_branch`, `test_exec_mut_branch_leak` (negative).

### Slice 4: tail / let if-expression lift ✅

`let y = if c then a else b; rest` lifts to `(c → let y := a; rest) ∧ (¬c → let y := b; rest)` via `lift_if_value`. Peels through transparent wrappers and single-binder `ExpX::Bind(Let, …)`. Same helper applies at Return position.

Tests: `test_exec_tail_if_expression`, `test_exec_let_if_expression`.

### Slice 5: loops ✅

`StmX::Loop` contributes `I ∧ maintain ∧ havoc_continuation` inline into the enclosing goal. Arbitrary nesting works via recursion. `tactus_peel` (recursive Lean macro) strips the goal's `∧`/`∀` structure; `tactus_auto` closes each leaf.

Tests: `test_exec_loop_count_down`, `test_exec_loop_count_up`, `test_exec_loop_invariant_fails` (negative), `test_exec_loop_sequential`, `test_exec_loop_nested`, `test_exec_loop_in_if_branch`, `test_exec_loop_in_else_branch`, `test_exec_loop_lex_decreases_rejected`, `test_exec_loop_break_rejected`, `test_exec_loop_no_invariant`, `test_exec_loop_decreases_unchanged` (negative).

Known shape restrictions (rejected by `check_loop`): `loop_isolation: false`, `cond: None`, condition setup stmts, lexicographic `decreases`, `invariant_except_break` / `ensures` invariants.

### Slice 6: overflow obligations ✅ (soundness fix)

`HasType(e, U(n))` emits `0 ≤ e ∧ e < 2^n` (was `True`). u-types render as `Int`. Fixed-width params get `(h_<name>_bound : …)` hypotheses. `IntegerTypeBound(kind, _)` evaluates to the decimal literal (`u8::MAX` → `255`). `ArchWordBits` resolves to the prelude axiom. USize/ISize emit bounds via `usize_hi` / `isize_hi` constants.

Tests: `test_exec_overflow_diagnostic`, `test_exec_overflow_tight_ok`, `test_exec_signed_overflow_fails`, `test_exec_underflow_unguarded_fails` (the u-as-Int soundness demo), `test_exec_underflow_guarded`, `test_exec_mul_overflow_fails`, `test_exec_u32_add_guarded`, `test_exec_integer_type_bound_u8_max`, `test_exec_integer_type_bound_i8_max`, `test_exec_char_bound`, `test_exec_widen_u8_to_i16`, `test_exec_usize_trivially_bounded`, `test_exec_usize_overflow_fails`, `test_proof_arch_word_bits_compiles`.

### Slice 7: function calls ✅

`StmX::Call` inlines callee's `require`/`ensure` via Lean let-bindings. WP: `requires_conj ∧ ∀ ret, h_bound(ret) → ensures_conj_with_ret → let dest := ret; wp(rest)`.

Tests: `test_exec_call_basic`, `test_exec_call_requires_violated` (negative), `test_exec_call_in_if_branch`, `test_exec_call_in_loop`, `test_exec_call_trait_method_rejected`.

Rejected: trait-method calls (dynamic dispatch), generic calls (`typ_args` non-empty), `&mut` args, cross-crate callees, split-assertion calls.

### What's deferred

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the comprehensive catalogue. Headline items:

- **`break` / `continue`** — rejected.
- **Trait-method calls / generic calls** — rejected at the call site; require dispatch resolution + monomorphization / type-parameter substitution respectively.
- **`&mut` args** — rejected; would need havoc-after-call semantics.
- **`proof { … }` blocks inside exec fns** — DESIGN.md claims support, untested; likely requires plumbing through `walk`.
- **`assert(P) by { tactics }` in exec fns** — user-provided tactic bodies for asserts; not wired.
- **`assume(P)` warnings** — DESIGN.md promises a "unproved assumption" warning; not wired.
- **USize arith rarely auto-verifies** — the bound is emitted, but `tactus_auto` can't discharge symbolic `2 ^ arch_word_bits`. Users need `cases arch_word_bits_valid` proofs.
- **Recursive call termination** — no decreasing-measure obligation across recursive calls.
- **Pattern matching in exec bodies** (`StmX` has no Match, but `ExpX::Ctor` / `ExpX::CallLambda` / `ExpX::ArrayLiteral` rejected — blocks match scrutinees containing these).

### Adding new slices

1. Extend `sst_to_lean::check_stm` / `check_loop` / `check_call` to accept the new form (or add a new helper).
2. Extend `walk` to produce a corresponding `BodyItem` variant if needed.
3. Extend `build_goal_with_terminator` to emit the WP shape — typically delegating to a new `build_<feature>_conjunction` function for non-trivial ones.
4. If the goal shape makes `tactus_auto` fail, add a prelude macro or emit a targeted `Tactic::Raw` at emission time. Keep `tactus_auto` dumb.
5. If new AST shapes are needed, extend `lean_ast` (preferably via smart constructors) and `lean_pp`.
6. Add snippets to `tactus_coverage::run_snippets` if new VIR variants become reachable via `dep_order::walk_expr` / `walk_place`.
7. Update DESIGN.md — both any relevant architecture section and the deferrals catalogue.

## Testing infrastructure

### Test suites at a glance

| Binary | Count | What it tests |
|---|---|---|
| `cargo test -p lean_verify --lib` | 35 | AST pp (precedence, tuples, indexing), type translation, sanity check scope tracking, lean_process |
| `cargo test -p lean_verify --test integration` | 7 | Tactus-prelude + Lean invocation end-to-end on hand-written Lean |
| `vargo test -p rust_verify_test --test tactus` | 152 | Full e2e: VIR → AST → Lean for proof fns + exec fns (all slices) |
| `vargo test -p rust_verify_test --test tactus_coverage` | 1 | Coverage assertion: expected VIR variants all hit by `walk_expr`/`walk_place` |
| `vargo build --release` (vstd) | 1530 | Regression guard: vstd proof library still verifies |

### Sanity check (`lean_verify/src/sanity.rs`)

**What it does**: after `generate.rs` builds the final `Vec<Command>`, walks every theorem goal, def body, class method sig, and instance method body. For each `ExprNode::Var(name)`, verifies `name` resolves to either:
- A local binder (def/theorem params, `let`, `λ`, `∀`/`∃`, match-arm pattern)
- An earlier top-level `Command` in the same file
- A Lean/Mathlib built-in on a small allowlist (`Nat`, `Int`, `Prop`, `True`, ...)
- A Tactus prelude name (`arch_word_bits`, `arch_word_bits_valid`, `usize_hi`, `isize_hi`, `tactus_peel`)
- A dotted name (`Classical.arbitrary`, `Nat.succ` — trust Lean)
- `«…»` keyword-quoted or `_`

Panics in debug builds when a violation is found. The generator-caught-vs-Lean-caught distinction matters: Lean errors say "unknown identifier" and point at a line in the generated file; our panic says "unresolved `foo` in theorem `bar`" and tells you it's a dep_order bug.

**Gated on** `#[cfg(debug_assertions)]`. Release builds skip the check (perf).

### Coverage matrix (`rust_verify_test/tests/tactus_coverage.rs`)

Dedicated test binary that drives a curated battery of spec/proof snippets through the full pipeline, with walker instrumentation active. Asserts that every variant on the expected list was visited at least once.

1. `dep_order.rs` has `record(kind: &str)` that appends `kind\n` to `$TACTUS_COVERAGE_FILE` if set. `OnceLock<Option<PathBuf>>` memoizes the env lookup — zero cost when unset.
2. `walk_expr` / `walk_place` call `record(expr_variant_name(...))` at entry.
3. Test sets `$TACTUS_COVERAGE_FILE`, runs `verify_one_file` on each snippet (subprocess spawn, env inherited), reads back the file, asserts `EXPECTED_EXPR_VARIANTS` / `EXPECTED_PLACE_VARIANTS` all appear.

Separate test binary because setting env vars in-process would affect sibling test binaries running in parallel.

### Debugging tactic failures

When `tactus_auto` fails, the error message now includes the generated `.lean` file path:

```
error: Lean tactus_auto failed for foo:
       
       unsolved goals:
         ...
       
       (generated .lean file: target/tactus-lean/test_crate/foo.lean)
```

`cat` that file to inspect the generated WP goal. For running Lean directly:

```bash
cd tactus/lean-project
lake env lean --json /path/to/foo.lean
```

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document (includes
                                 deferrals catalogue under §
                                 "Known deferrals, rejected cases, and
                                 untested edges")
  HANDOFF.md                   ← this file
  POEMS.md                     ← occasional pieces written during sessions
  lean-project/                ← repo-local Lake project for Mathlib
    lakefile.lean              ← imports Mathlib
    lean-toolchain             ← pins Lean version (v4.25.0)
    .lake/                     ← precompiled oleans (gitignored)
  tree-sitter-tactus/          ← git submodule
    grammar.js
    src/scanner.c
    test/corpus/*.txt          ← 199 grammar tests
  dependencies/
    syn/src/verus.rs           ← MODIFIED: tactic_by with byte_range()
  source/
    lean_verify/
      TactusPrelude.lean       ← tactus_auto + tactus_peel macros,
                                 arch_word_bits / usize_hi / isize_hi
      scripts/setup-mathlib.sh
      src/
        lean_ast.rs            ← typed Lean AST + smart constructors
        lean_pp.rs             ← precedence-aware pp + tactic-start tracking
        sanity.rs              ← post-codegen reference check
        dep_order.rs           ← walker + coverage instrumentation
        generate.rs            ← orchestration + debug_check
        to_lean_type.rs        ← TypX → Expr
        to_lean_expr.rs        ← VIR Expr → Expr + field_access_name
        to_lean_sst_expr.rs    ← SST Exp → Expr + type_bound_predicate
        to_lean_fn.rs          ← VIR decls → Commands + LeanSourceMap
        sst_to_lean.rs         ← WP generator for exec fns (all slices)
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
      tactus.rs                ← 152 end-to-end tests
      tactus_coverage.rs       ← coverage matrix test binary
    vir/src/
      ast.rs                   ← FunctionAttrs.tactic_span + tactus_auto
```

## Known limitations and tradeoffs

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the comprehensive catalogue. This section surfaces the ones most likely to bite a future session.

1. **HANDOFF.md staleness recurrence.** This document should be updated when a slice lands or architecture shifts. DESIGN.md's deferrals section is the canonical record of what's missing; keep this one aligned.
2. **`debug_check` only in debug builds.** Release users running Tactus get the cryptic Lean error instead of the pointed panic. Option: add `TACTUS_STRICT_CODEGEN` env.
3. **`noncomputable` baked into pp.** Every emitted `def` is `noncomputable def`. Correct for all current users; revisit if we ever emit computable helpers.
4. **Exec-fn source mapping not wired.** Sanity check + coverage instrumentation point at the generator; when Lean rejects an exec-fn body, the error points at the generated file's line, not the Rust source. The error message now includes the file path so `cat` is one command, but true source mapping (Rust line numbers in the error) is still TODO.
5. **Per-module Lean generation not implemented.** One `.lean` file per proof fn / exec fn. Fine at our scale; future work when we have many fns per module.
6. **`//` not allowed in tactic blocks.** tree-sitter's `line_comment` extra consumes `//` globally. Reported as a clear error at verification time; use `Nat.div` / `Int.div`.
7. **No `StmX::Call` termination obligation for recursive calls.** See DESIGN.md § "StmX::Call — landed".
8. **USize arith bounds are emitted but rarely auto-discharge.** `tactus_auto` can't handle symbolic `2 ^ arch_word_bits`. User proofs need `cases arch_word_bits_valid`. A future `tactus_usize_bound` tactic could automate this.

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
# 152 end-to-end tests
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Coverage matrix (1 test, asserts walker visits the expected variant set)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus_coverage

# 35 unit tests (AST pp, sanity check, type translation)
cargo test -p lean_verify --lib

# 7 integration tests (Lean invocation end-to-end)
cargo test -p lean_verify --test integration

# ── Single test / debug ────────────────────────────────────────────
# One e2e test
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus -- test_exec_call_basic

# Inspect generated Lean for a test (path is also in the error message
# when tactus_auto fails)
cat rust_verify_test/target/tactus-lean/test_crate/<fn_name>.lean

# Run Lean directly on a generated file
cd ../lean-project
lake env lean --json /path/to/fn.lean

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
