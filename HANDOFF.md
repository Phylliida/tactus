# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions, including a comprehensive "Known deferrals, rejected cases, and untested edges" catalogue.

## Current state

**172 end-to-end tests + 1 coverage test + 110 unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

**Track B status: all seven slices landed.** Exec fns can have: `let`-bindings, mutation (via Lean let-shadowing), if/else, early returns, loops (arbitrary nesting — sequential, nested, inside if-branches), function calls (direct named, including recursion and mutual recursion via Verus's `CheckDecreaseHeight` obligation), and arithmetic with overflow checking. Most realistic Rust exec fns should verify, modulo documented restrictions (no trait-method calls, no `&mut` args, no generic calls, no break/continue — see DESIGN.md § "Known deferrals").

### Recent session landings

#### Prior sessions (preserved in git log)

Earlier sessions landed the core WP pipeline, soundness hardening, the Wp DSL refactor, expression-renderer shared leaves, and the upstream-brittleness triangle. Key outputs still referenced elsewhere in this doc:

- **Wp DSL** (`fba8170`) — structural continuations, `Wp::Done` terminator, type-level "discard after Return." Core of Track B.
- **WpCtx** (`ccaf300`) — single context struct replacing 8 parameter sites.
- **Lean-AST substitution** (`eeb97f9`) — capture-avoiding `substitute` on `LExpr`, 27 unit tests.
- **Post-simplify krate routing** (`1a72322`) — `simplified_krate()` aligns exec-fn path with call-site SST.
- **Validation / rendering unification** (`906b59a`) — `sst_exp_to_ast_checked` as single source of truth for SST support.
- **`CheckDecreaseHeight` lowering** (`260f3b3`) — termination via Verus's own recursion-pass obligation, not duplicated.
- **Upstream-brittleness review** (`2a2428c`) — explicit field destructures, shared `peel_transparent`, shape-drift tests. See DESIGN.md § "Upstream-robustness patterns".
- **`expr_shared.rs`** (`02747de`) — op tables, Clip coercion, constant rendering shared between VIR-AST and SST renderers. Full rationale in DESIGN.md § "Two parallel expression renderers".

#### Current session (2026-04-24 — Track B tightening)

Seven roadmap tasks landed plus two review-driven cleanup passes. Grouped by theme:

**Infrastructure enabling the Tier 1/2 tasks:**
- **Track B tightening roadmap** (`dec269d`) — 9 items across 3 tiers documented in DESIGN.md with rejection-reasoning for deferred designs.
- **FileLoader sanitization for `proof { }` + `assert by { }`** (`4386307`) — inside `#[verifier::tactus_auto]`-marked fns, the FileLoader now sanitizes these brace bodies (previously only sanitized proof-fn `by { }`). Discrimination: walk up from the node to find the enclosing `function_item` and substring-match for `tactus_auto` in its `attribute_item` children. vstd's Verus-flavoured proof blocks stay on the normal path because vstd doesn't use `tactus_auto`.

**Tier 2 landings:**
- **#52 struct Ctor + enum Ctor infrastructure** (`4efd98d`) — `ExpX::Ctor` via shared `ctor_node` helper. `datatype_to_cmds` emits per-variant discriminator (`Type.isVariant : Type → Prop`) and accessor (`Type.Variant_val0 : Type → FieldTy`) defs alongside multi-variant inductives. Accessor emission guarded by `emit_accessors` flag (exec-fn path = true, proof-fn path = false — spec fns preserve native Lean match; accessor bodies use `default` which needs `[Inhabited α]` that user enum field types may not provide). `Classical.propDecidable` opened in the prelude so Prop discriminators decide in `if` contexts. Enum PATTERN MATCHING automation is the one gap — tracked as #58.
- **#53 generic calls** (`8aae485`) — `Wp::Call` carries `typ_args: &'a [Typ]`. `lower_call` composes value-param + type-param substitution through the shared `lean_ast::substitute` (works because `TypX::TypParam` renders as `Var(name)`). `build_param_binders` emits `(T : Type)` theorem-level binders.

**Tier 1 landings (user tactic escape hatches):**
- **#50 `assert(P) by { lean_tactic }`** (`4386307`, `fa54699`, `6205352`, `cba5d0d`) — user-written Lean tactic inside exec-fn assert-by. Routed via `AssertQueryMode::Tactus { tactic_span, kind: AssertBy }` → `Wp::AssertByTactus { cond: Some(P), tactic_text, body }`. Theorem emitter prepends `have h_tactus_assert_N : P := by <user_tac>;` before the closer; hypothesis propagates to subsequent `simp_all` / `omega`.
- **#49 `proof { lean_tactics }`** (`815b564`) — built on #50 as essentially the same pattern, different kind: `TactusKind::ProofBlock` + `Wp::AssertByTactus { cond: None, ... }`. `rust_to_vir_expr` synthesises an AssertBy-wrapped-in-Ghost when it sees a `proof { }` with empty HIR body inside a tactus_auto fn (empty-body is the discriminator from Verus's `auto_proof_block` pass, which always has content inside). Prepends `<user_tac>` raw instead of wrapping — the user's own `have`s propagate to theorem level.

**Tier 3 landing:**
- **#57 break / continue** (`2cede37`) — unlabeled break/continue in while loops. `Wp::Loop::cond` becomes `Option<&'a Exp>` (Verus lowers `while c { … break; … }` to `cond: None` + inserted `if !c { break; }`). New `WpLoopCtx { break_leaf, continue_leaf }` threaded through `build_wp` as `Option<&WpLoopCtx>`; `StmX::BreakOrContinue` emits `Wp::Done(leaf)` with the chosen leaf. Estimated 3-4 days in the roadmap; actual was ~30 minutes because the AssertBy/ProofBlock pattern (+ `Option<cond>` trick) generalised cleanly.

**Two code review passes (fed cleanup work):**
- **First cleanup** (`568d9d5`) — fixed three smells surfaced by reviewing the #50 landing: (1) `StmX::AssertQuery` was smuggling the asserted condition via `typ_inv_exps`, a field meant for type invariants — moved to `body` as `StmX::Assert(cond)`; (2) `WpCtx::tactus_asserts: RefCell<_>` made `lower_wp` lie about its purity — replaced with `collect_tactus_haves` two-pass walk; (3) duplicated `dedent` + `read_tactic_from_source` between rust_verify and lean_verify — moved to `lean_verify::source_util` and have rust_verify thin-delegate.
- **Second cleanup** (`479765a`) — fixed review findings from the full five-lens pass: orphaned docstring on `WpCtx` (had inserted `WpLoopCtx` between the comment and the struct it described), double-commented block in rust_to_vir_expr, flag-soup `tactic_span: Option<_>` + `is_tactus_proof_block: bool` folded into `tactus: Option<TactusSpan>` (with `TactusSpan { file_path, start_byte, end_byte, kind }`), unused `_outer_loop_ctx` parameter dropped. Added 6 regression tests including labeled-break-rejected, nested-loops-inner-break, break+continue-in-same-body, return-inside-loop-with-break, proof-block-with-goal-modifying-tactic, and auto-wrapped-assert-alongside-proof-block (shape-drift guard for the HIR-body-empty discriminator).

**Writing + reflection** (`af57e0c`) — three poems in POEMS.md about this session's themes: honest shape (the type-level lies in the typ_inv_exps / RefCell smells), the third time (Option<cond> as a recurring trick across #50/#49/#57), against the thing I wanted to build (why the walker-derive-macro hasn't cleared the "do it" threshold yet).

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
                   uses self.vir_crate (pre-simplify — user-written specs)
  tactus_auto  → lean_verify::check_exec_fn(krate, vir_fn, fn_sst, check, imports, crate_name)
                   uses self.simplified_krate() (post-simplify — aligned with SST call sites)

lean_verify pipeline (AST-based):
  1. krate_preamble(krate, ...) → Vec<Command> (imports, prelude, namespace, traits, datatypes,
     spec fns, trait impls; walks dep_order to find transitively-referenced decls)
  2. Theorem builder:
       proof_fn  → to_lean_fn::proof_fn_to_ast  (Tactic::Raw from user text)
       exec_fn   → sst_to_lean::exec_fn_theorems_to_ast  (Vec<Theorem>)
                     validates reqs/ens via `check_exp` (which calls sst_exp_to_ast_checked)
                     constructs WpCtx (fn_map, type_map, ret_name, ensures_goal)
                     build_wp(check.body, Done(ensures_goal), ctx) → Wp<'_>
                     lower_wp(wp, ctx) → LExpr
  3. debug_check(&cmds) — sanity::check_references panics on unresolved references
     (gated on #[cfg(debug_assertions)])
  4. pp_commands(&cmds) → PpOutput { text, tactic_starts }
     — tactic_starts[0] gives 1-indexed line where `Tactic::Raw` body begins, for source map
  5. write_lean_file(path, text) → target/tactus-lean/{crate}/{fn}.lean
  6. lean_process::check_lean_file(path, lake_dir) — invokes `lake env lean --json <path>`
  7. Parse JSON diagnostics, map via LeanSourceMap, report through Verus
     (error messages include the generated .lean path for easy inspection)
```

### WP emission for exec fns

`sst_to_lean::build_wp` (SST → Wp) and `lower_wp` (Wp → LExpr) replace the earlier `walk` + `build_goal_with_terminator` pair. Each `Wp<'a>` variant is one WP rule:

- **`Done(leaf)`** — terminator. Built from the fn's ensures at top level, from `Done(I ∧ D < _tactus_d_old)` for loop bodies, or from `Return(e)`'s `let <ret> := e; ensures_goal` (discarding whatever `after` was at that point).
- **`Let(x, rhs, body)`** → `let x := rhs; lower_wp(body)`. If `rhs` is an `ExpX::If`, lowering lifts via `lift_if_value` — splits into `(c → let x := a; body) ∧ (¬c → let x := b; body)` so omega sees each branch.
- **`Assume(P, body)`** → `P → lower_wp(body)`.
- **`Assert(P, body)`** → `P ∧ lower_wp(body)`. Crucially not just "conjoin everything" — Verus's `assert(P)` desugars to `Assert(P); Assume(P)`, and without the asymmetry the assert would trivially satisfy itself.
- **`Branch { cond, then_branch, else_branch }`** → `(c → lower_wp(then_branch)) ∧ (¬c → lower_wp(else_branch))`. Each branch carries its own continuation via its sub-Wp tree.
- **`Loop { cond, invs, decrease, modified_vars, body, after }`** → `init ∧ maintain ∧ use`. Maintain wraps `lower_wp(body)` with `let _tactus_d_old := D; ...` (the body was built with `Done(I ∧ D < _tactus_d_old)` as its terminator, referencing `_tactus_d_old` as a Var). Use quantifies over modified vars and lowers `after`.
- **`Call { callee, args, dest, after }`** → `requires(subst) ∧ ∀ ret, h_bound(ret) → ensures_using_ret(subst) → (let dest := ret; lower_wp(after))`. Inlines the callee's spec via `lean_ast::substitute` (no let-wrapping — avoids name shadowing).

`needs_peel()` on the Wp tree decides tactic shape: flat Let/Assert/Assume chains over arithmetic get `Tactic::Named("tactus_auto")`; anything with Loop/Call gets `Tactic::Raw("tactus_peel; all_goals tactus_auto")`. `tactus_peel` (prelude macro) recursively strips `∧` / `∀` / `→` / `intro ⟨_, _⟩` (destructure And-hypotheses); `tactus_auto` is a dumb leaf closer (`rfl | decide | omega | simp_all | fail`).

### `lean_verify` module map

```
lean_verify/src/
  lean_ast.rs        Typed AST: Command / Expr / Tactic / Binder / Pattern /
                     BinOp / UnOp. Smart constructors (LExpr::and, implies,
                     let_bind, forall, app, lit_int, etc.) — call sites no
                     longer write Box::new(LExpr::new(ExprNode::…)) chains.
                     Also exports `substitute(expr, subst)` — capture-avoiding
                     Lean-AST substitution used at call sites to inline
                     callee specs without let-shadowing. 27 unit tests
                     (per-variant coverage, capture avoidance both
                     positive and negative cases).
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
  expr_shared.rs     Rules both expression renderers must apply identically:
                     `binop_to_ast` (op table), `non_binop_head` (head for
                     non-structural binops), `const_to_node_common` (non-float
                     Constant arms), `clip_coercion_head` + `apply_clip_coercion`
                     (Int/Nat wrapper resolution). Plus the existing
                     `pub(crate)` helpers in `to_lean_sst_expr.rs`
                     (`type_bound_predicate`, `integer_type_bound_node`,
                     `renders_as_lean_int`) that predate the split. Module
                     docstring lays out the analysis of trait unification
                     and SST-routing, and why shared leaves is the chosen
                     level of unification.
  to_lean_expr.rs    VIR-AST Expr → lean_ast::Expr. Includes field_access_name
                     (Dt::Tuple + numeric → n+1, Dt::Path + numeric → valN).
                     Delegates to `expr_shared` for op tables and constant
                     rendering; HasType / IntegerTypeBound render via
                     `to_lean_sst_expr`'s shared helpers; Clip uses the
                     shared `renders_as_lean_int` + `apply_clip_coercion`.
  to_lean_sst_expr.rs  SST Exp → lean_ast::Expr. Dual API:
                       `sst_exp_to_ast_checked(e) -> Result<LExpr, String>`
                       (primary; validates as it renders) and
                       `sst_exp_to_ast(e) -> LExpr` (infallible wrapper,
                       panics if called with unvalidated input — used at
                       build_* sites where walk has cleared validation).
                       Lowers `InternalFun::CheckDecreaseHeight` to the
                       int-typed termination obligation
                       `(0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)`.
                       Exports `type_bound_predicate`, `integer_type_bound_node`,
                       `renders_as_lean_int` (shared with VIR path),
                       `clip_to_node_checked`.
  to_lean_fn.rs      VIR decls → lean_ast::Command (Def / Theorem / Datatype /
                     Class / Instance). Includes LeanSourceMap struct. Proof
                     fn params pick up h_<name>_bound hypotheses via the
                     shared type_bound_predicate.
  sst_to_lean.rs     SST exec-fn body → Vec<Theorem> via WP. Core module for
                     Track B. Key types:
                       - `WpCtx<'a>`: fn_map + type_map + ret_name +
                         ensures_goal. `WpCtx::new` validates reqs/
                         ens_exps and returns Result — precondition
                         enforced in the type.
                       - `Wp<'a>`: Done / Let / Assert / Assume / Branch /
                         Loop / Call — WP algebra; see "WP emission" above.
                         `Wp::Call::args` borrows `&'a [Exp]` from the
                         SST directly (no Vec allocation).
                     Key fns: `exec_fn_theorems_to_ast`, `build_wp`,
                     `build_wp_call`, `build_wp_loop`, `lower_wp`,
                     `lower_loop`, `lower_call`. `check_exp` is a thin
                     validation wrapper around `sst_exp_to_ast_checked`.
                     `peel_transparent(&Exp) -> &Exp` is the shared
                     Box/Unbox/CoerceMode/Trigger peeler used by
                     `contains_loc`, `lift_if_value`, and
                     `render_checked_decrease_arg` — adding a new
                     transparent wrapper = one edit, not three.
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
                     tactus_peel (recursive ∧/∀ peeler with And-destructure
                     intro), arch_word_bits axiom, arch_word_bits_valid
                     disjunction, usize_hi / isize_hi Int defs, linter settings.
```

### Key design decisions

1. **Typed AST with smart constructors + Lean-AST substitution.** `lean_ast.rs` has 30+ constructors plus `substitute` (capture-avoiding, lazy-per-scope capture check, panics on real captures). Call-site inlining substitutes directly rather than emitting nested `let` bindings that would shadow caller names.
2. **On-disk Lean artifacts.** Every generated file lands in `target/tactus-lean/{crate}/{fn}.lean`. Debuggable (`cat` the file) and referenced from error messages.
3. **Sanity check every generation (debug builds).** Catches "dep_order dropped a reference" class of bug with pointed errors; allowlist for Tactus prelude names.
4. **`tactus_auto` is a dumb leaf closer; `tactus_peel` is a recursive peeler.** Structural tactics — which `refine ⟨?_, ?_⟩` to use, which `intros` — belong at codegen time because the emitter knows the shape. Loops/calls emit `tactus_peel; all_goals tactus_auto`.
5. **Assert/assume as WP nesting, not conjoined.** `assert(P); assume(P)` (Verus's desugaring of user `assert(P)`) must NOT trivially satisfy itself. `(P) ∧ (rest)` for asserts vs `(P) → rest` for assumes.
6. **`_tactus_body_` / `_tactus_d_old` / `tactus_peel` reserved prefix.** Tool-generated names never collide with user code (Rust doesn't produce `_tactus_` or `tactus_`-prefixed identifiers).
7. **Two-layer dependency walking.** `dep_order::walk_expr` recurses through ExprX; `dep_order::walk_place` recurses through PlaceX. Place variants can hide Call refs inside; both walkers cover the full tree.
8. **Tuple rendering.** `Dt::Tuple(n)` → `T₁ × T₂ × …` type, `⟨a, b, …⟩` constructor, `.1`/`.2` field access (Lean 1-indexed).
9. **u-types render as Int, not Nat.** Lean's `Nat` truncates subtraction (`0 - 1 = 0`); rendering u8/u16/…/u128 as `Int` with both-sided bounds makes underflow catchable. USize keeps rendering as `Nat` — const-generic constraint (see DESIGN.md).
10. **WP DSL (`Wp<'a>`) with structural continuations.** Each compound node carries its own `after: Box<Wp<'a>>`; `Done(leaf)` is the only terminator and has no continuation slot. `Return` writes `Done(let ret := e; ctx.ensures_goal)`, naturally fn-exit by construction. Adding a new WP form means one constructor + one arm each in `build_wp` and `lower_wp` — no central dispatcher to keep in sync.
11. **Single fallible case analysis for SST lowering.** `sst_exp_to_ast_checked` validates and renders in one pass. `check_exp` is a thin wrapper; `sst_exp_to_ast` is the infallible form for already-validated contexts. Adding a new `ExpX` variant means one edit.
12. **Callees inlined via Lean-AST substitution, not Lean definitions.** Exec fn calls pull callee's `require`/`ensure` from its `FunctionX` and substitute arg expressions for param names via `lean_ast::substitute` — no shadowing, no zeta-reduction needed for omega.
13. **Pre vs post-simplify krate split.** Proof fns route through `self.vir_crate` (pre-simplify — user-visible spec forms). Exec fns route through `self.simplified_krate()` (post-simplify — aligns with SST call-site arg layout for zero-arg fns).
14. **Exhaustive matches, no catch-all `_ =>`.** New VIR variants force compile errors at every walker / writer site. Backed by coverage test to make sure the walker is exercised.
15. **Termination via Verus's own `CheckDecreaseHeight`.** Recursive calls (including mutual across an SCC) are protected by a `StmX::Assert(InternalFun::CheckDecreaseHeight)` that Verus inserts upstream. `sst_exp_to_ast_checked` lowers it to the int-typed obligation; we get termination for free.
16. **Upstream-robustness patterns** (post-audit pass). Three layers of defence against Verus-side refactors surprising us:
    - *Explicit field destructures* — no `..` in `StmX::Assign` / `Return` / `Loop` / `Call` patterns. Any Verus-side field addition is a compile error.
    - *Shared helpers for implicit shapes* — `peel_transparent` centralises the Box/Unbox/CoerceMode/Trigger wrapper set; `renders_as_lean_int` centralises the Int-vs-Nat rendering decision. Adding a new variant = one edit across all consumers.
    - *Shape-drift tests* — e.g., `full_check_decrease_height_shape_pinned` constructs a synthetic CheckDecreaseHeight and asserts the expected lowering. Failure message points at the exact fix site, turning a future mystery breakage into a focused test fail.
17. **Tactus tactic-span plumbing via `TactusSpan`.** A single `Option<TactusSpan>` field on `ExprX::AssertBy` carries (file path, byte range, kind: AssertBy / ProofBlock) for both user-tactic escape hatches. The previous flag-soup (`Option<(path, s, e)>` + `is_tactus_proof_block: bool`) coupled two fields that could never take independent values; folding into one struct encodes the invariant in the type. `rust_to_vir` populates only inside `tactus_auto` fns; `ast_to_sst` routes to `AssertQueryMode::Tactus { kind }`; `sst_to_lean` branches on kind for the `have`-wrap vs raw emission.
18. **Loop break / continue via threaded `WpLoopCtx`.** `build_wp` takes `Option<&WpLoopCtx>` as a parameter; `WpLoopCtx { break_leaf, continue_leaf }` holds the goals each control-flow edge must establish. Inner loops shadow outer (innermost applies). `StmX::BreakOrContinue` emits `Wp::Done(chosen_leaf)`. `Wp::Loop::cond` is `Option<&Exp>` — `None` is Verus's break-lowered `while c { … break; … }` shape; `lower_loop` drops the cond-gates in that case.

## Track B status

`#[verifier::tactus_auto]` routes an exec fn's body through `sst_to_lean` instead of Z3. All seven planned slices landed.

### Slice 1: straight-line code ✅

Supports: `StmX::Block`, `StmX::Assign`, `StmX::Return`, `StmX::Assert`, `StmX::Assume`, `StmX::Air` / `StmX::Fuel` / `StmX::RevealString` (transparent).

Tests: `test_exec_const_return`, `test_exec_add_one`, `test_exec_wrong_ensures`, `test_exec_assert_holds`, `test_exec_assert_fails`.

### Slice 2: if/else WP rule ✅

`StmX::If(cond, then, Option<else>)` becomes `Wp::Branch` — each branch carries its own continuation via its sub-Wp, folded into `(c → lower(then)) ∧ (¬c → lower(else))` at emission.

Tests: `test_exec_if_assert_holds`, `test_exec_if_no_else`, `test_exec_if_assert_fails`, `test_exec_nested_if`, `test_exec_mutation_both_branches`.

### Slice 3: mutation via SSA ✅

No-op: Lean's let-shadowing gives SSA for free. `StmX::Assign` emits `Wp::Let(x, e, body)` regardless of `is_init`.

Tests: `test_exec_mut_seq`, `test_exec_mut_in_branch`, `test_exec_mut_branch_leak` (negative).

### Slice 4: tail / let if-expression lift ✅

`let y = if c then a else b; rest` lifts to `(c → let y := a; rest) ∧ (¬c → let y := b; rest)` via `lift_if_value` in `lower_wp`'s `Let` arm. Peels through transparent wrappers and single-binder `ExpX::Bind(Let, …)`. Same helper applies at Return position.

Tests: `test_exec_tail_if_expression`, `test_exec_let_if_expression`.

### Slice 5: loops ✅

`StmX::Loop` becomes `Wp::Loop { body, after }` — `body` is built with `Done(I ∧ D < _tactus_d_old)` as its terminator; `after` is the post-loop continuation. Lowering emits `init ∧ maintain ∧ use`; nested loops compose structurally. `tactus_peel` strips the goal's `∧`/`∀` structure; `tactus_auto` closes each leaf.

Tests: `test_exec_loop_count_down`, `test_exec_loop_count_up`, `test_exec_loop_invariant_fails` (negative), `test_exec_loop_sequential`, `test_exec_loop_nested`, `test_exec_loop_in_if_branch`, `test_exec_loop_in_else_branch`, `test_exec_loop_lex_decreases_rejected`, `test_exec_loop_break_rejected`, `test_exec_loop_no_invariant`, `test_exec_loop_decreases_unchanged` (negative).

Known shape restrictions (rejected by `build_wp_loop`): `loop_isolation: false`, `cond: None`, condition setup stmts, lexicographic `decreases`, `invariant_except_break` / `ensures` invariants.

### Slice 6: overflow obligations ✅ (soundness fix)

`HasType(e, U(n))` emits `0 ≤ e ∧ e < 2^n` (was `True`). u-types render as `Int`. Fixed-width params get `(h_<name>_bound : …)` hypotheses. `IntegerTypeBound(kind, _)` evaluates to the decimal literal (`u8::MAX` → `255`). `ArchWordBits` resolves to the prelude axiom. USize/ISize emit bounds via `usize_hi` / `isize_hi` constants.

Tests: `test_exec_overflow_diagnostic`, `test_exec_overflow_tight_ok`, `test_exec_signed_overflow_fails`, `test_exec_underflow_unguarded_fails` (the u-as-Int soundness demo), `test_exec_underflow_guarded`, `test_exec_mul_overflow_fails`, `test_exec_u32_add_guarded`, `test_exec_integer_type_bound_u8_max`, `test_exec_integer_type_bound_i8_max`, `test_exec_char_bound`, `test_exec_widen_u8_to_i16`, `test_exec_usize_trivially_bounded`, `test_exec_usize_overflow_fails`, `test_proof_arch_word_bits_compiles`.

### Slice 7: function calls ✅ (with recursion)

`StmX::Call` becomes `Wp::Call { callee, args, dest, after }`. Lowering emits `requires(subst) ∧ ∀ ret, h_bound(ret) → ensures_using_ret(subst) → let dest := ret; lower_wp(after)`. Callee's `require`/`ensure` are rendered via `vir_expr_to_ast` and param-substituted via `lean_ast::substitute` — no let-shadowing.

**Termination** comes via Verus's own `recursion` pass, which inserts a `StmX::Assert(InternalFun::CheckDecreaseHeight)` before every recursive call site (including mutual recursion across an SCC). `sst_exp_to_ast_checked` lowers `CheckDecreaseHeight` to the int-typed obligation `(0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)`. Non-int decreases rejected with a clear error.

Tests: `test_exec_call_basic`, `test_exec_call_requires_violated` (negative), `test_exec_call_in_if_branch`, `test_exec_call_in_loop`, `test_exec_call_trait_method_rejected`, `test_exec_call_zero_args`, `test_exec_call_many_args`, `test_exec_call_mut_ref_rejected`, `test_exec_call_recursive_decreasing`, `test_exec_call_recursive_nondecreasing` (negative), `test_exec_call_recursive_no_decreases` (negative), `test_exec_call_mutual_recursion`, `test_exec_ctor_rejected`.

Rejected (in `build_wp_call`): trait-method calls (dynamic dispatch), trait-default-impl calls, generic calls (`typ_args` non-empty), `&mut` args (detected through transparent wrappers), cross-crate callees, split-assertion calls.

### What's deferred

The seven original Track B slices are all landed. Subsequent Tier 1-3 roadmap tasks have continued the work — see **Pending work** below for the remaining queue. Landed from the roadmap this session: #50 assert-by user tactics, #49 proof blocks, #52 struct Ctor (enum infra + automation gap as #58), #53 generic calls, #57 break/continue.

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the full catalogue. Currently blocking realistic exec fns:

- **`&mut` args** — rejected; needs havoc-after-call semantics. Task #55.
- **Trait-method calls** — rejected; needs dispatch resolution. Task #56.
- **Non-int decreases** — datatype-typed decreases rejected; needs Lean `height` function generation per datatype. Task #54.
- **Enum pattern-matching verification** — structural codegen works; `tactus_auto` can't case-split the enum scrutinee. Task #58.
- **Source-mapping exec-fn errors** — Lean errors cite generated-file line numbers, not Rust source. Task #51.
- **`assume(P)` warning** — DESIGN.md promises a "unproved assumption" compile warning; not wired.
- **USize arith rarely auto-verifies** — the bound is emitted, but `tactus_auto` can't discharge symbolic `2 ^ arch_word_bits`. Users need `cases arch_word_bits_valid` proofs.
- **Labeled `break` / `continue`** — rejected in `build_wp`'s StmX::BreakOrContinue arm; would need a label-keyed stack of loop contexts.
- **`invariant_except_break` / `ensures` loop invariants** — only `at_entry = at_exit = true` invariants accepted. Verus's default `invariant x …` syntax produces both, so this covers the user-written common case; more complex loop shapes (e.g., ones desugared from `while let Some(x) = it.next() { … }`) may hit it.
- **VIR / SST expression renderer unification** — shared leaves extracted into `expr_shared.rs`; the walkers themselves stay separate because the source trees are genuinely different shapes. See DESIGN.md § "Two parallel expression renderers" for the analysis of why full unification was rejected.

### Adding new slices

1. Extend `sst_to_lean::build_wp` / `build_wp_call` / `build_wp_loop` to produce a new `Wp` variant (or accept a new form). Validation (Err for unsupported shapes) happens in the same pass.
2. Extend `Wp` enum with the new variant if the WP rule doesn't fit an existing one. Each new variant needs: constructor + `needs_peel` arm + `lower_wp` arm + `collect_tactus_haves_into` arm.
3. If the goal shape makes `tactus_auto` fail, add a prelude macro or emit a targeted `Tactic::Raw` at emission time. Keep `tactus_auto` dumb.
4. If new AST shapes are needed, extend `lean_ast` (preferably via smart constructors) and `lean_pp`. If the new shape has binders, extend `lean_ast::substitute` and `collect_free_vars` — three places to edit.
5. Add snippets to `tactus_coverage::run_snippets` if new VIR variants become reachable via `dep_order::walk_expr` / `walk_place`.
6. Update DESIGN.md — both any relevant architecture section and the deferrals catalogue.
7. Do a review pass (see **Code review strategy** below) before calling it done.

## Pending work

Five tasks remain on the Track B roadmap. Rough order by cost-effectiveness:

### #51 — Source mapping for exec-fn errors  [~2 days, standalone]

**What**: Lean errors currently report line numbers in the generated `.lean` file, not the Rust source. Users `cat` the file to understand what failed; fine for debugging but not what a production verifier should do.

**Approach**: Thread `Span` through the `Wp` tree so each node carries source location. Extend `LeanSourceMap` (currently only populated for proof fns in `to_lean_fn.rs`) to track exec-fn theorem positions — build a mapping from Lean line → SST node → Rust span. On Lean error, look up by line number.

**What to read first**: `to_lean_fn.rs::LeanSourceMap` for the proof-fn pattern, `generate.rs::check_exec_fn` for where the error flows back to the user, `lean_pp::PpOutput::tactic_starts` for the proof-fn line-tracking approach.

**Gotcha**: Lean errors report positions in the generated file *as read by Lean*, which can include `_tactus_d_old` let-bindings and synthesized helper tactics. The mapping has to distinguish user-attributable positions from synthesized-context positions.

### #58 — Enum-match automation  [~1-2 days, follow-up to #52]

**What**: The enum-pattern-match infrastructure (#52) produces structurally-correct Lean: `inductive` with synthesized `Type.isVariant` / `Type.Variant_val0` accessor fns, `Classical.propDecidable` opened so Prop discriminators decide. The one gap: `tactus_auto` (currently `rfl | decide | omega | simp_all`) can't case-split the enum scrutinee to close the residual `match k with | Variant _ => …` subterms after `@[simp]` unfolds the accessors.

**Approach**: Either (a) extend `tactus_auto` in `TactusPrelude.lean` with `cases <enum-typed-hypothesis> <;> simp_all <;> omega` (needs a way to find enum-typed hypotheses), (b) introduce a `tactus_cases` recursive tactic that scans hypotheses for inductive types, or (c) emit `rcases k` explicitly at codegen time when we detect the body matches on k.

**What to read first**: `test_exec_match_enum_automation_gap` in `tactus.rs` shows the failing case and its current error. The generated `.lean` file shows the residual goal shape.

**Gotcha**: Option (a)/(b) needs `aesop` or similar from Mathlib — `cases` without a named argument isn't in core Lean. Option (c) requires the codegen to know which binder is the scrutinee, which means routing scrutinee info through to_lean_sst_expr's IsVariant / Field arms.

### #54 — Non-int `decreases`  [~3-4 days, unblocks recursive enum fns]

**What**: `CheckDecreaseHeight` rejects non-int decrease types (see `is_int_height` in `to_lean_sst_expr.rs`). Blocks `fn walk(t: Tree) decreases t { match t { ... } }` and any recursion on user datatypes.

**Approach**: Generate a `Type.height : Type → Nat` function per datatype used in a `decreases` clause — recursive definition summing child heights + 1. Add axioms matching the prelude's `height_lt` ↔ arithmetic equivalence (so the existing `CheckDecreaseHeight` lowering handles both int and datatype cases uniformly). Update `is_int_height` to accept types with a generated height.

**What to read first**: `to_lean_sst_expr.rs::sst_exp_to_ast_checked` CheckDecreaseHeight arm (the current int-only path) and `is_int_height`. Verus's prelude axioms at `vir/src/prelude.rs:1019-1037` define what `height` needs to satisfy.

**Gotcha**: Interacts with #58 — a recursive enum fn typically has a `match` in its body, so #54 is most useful after enum-match automation lands. Also generic decreases (decreasing on a `Box<Self>` or similar) need type-param handling.

### #55 — `&mut` args in exec-fn calls  [~1 week, heavy]

**What**: `build_wp_call` rejects calls with `&mut` args (via `contains_loc`). Blocks any fn that mutates through a reference — common in idiomatic Rust.

**Approach**: Havoc-after-call semantics. Post-call the mutated parameter is "any value satisfying its type invariant AND the callee's `ensures` clause (which may reference the new value)." Encoding: `∀ (x' : T), type_inv(x') → ensures[x ↦ x'] → <continuation>` replacing the current pre/post pair. Aliasing: two `&mut` args to the same call must reference distinct storage — Rust's borrow checker guarantees this upstream.

**What to read first**: `build_wp_call` current rejection logic, `lower_call` for the current non-mut encoding.

**Gotcha**: Multiple `&mut` args need a multi-variable havoc. `old(x)` in ensures clauses (if we support it — currently rejected) is the pre-call value. The ensures rewrite `[x ↦ x']` has to handle whatever VIR's representation of the mutated-parameter reference is.

### #56 — Trait-method calls  [~1 week, heavy]

**What**: `build_wp_call` rejects `resolved_method: Some(_)` (dynamically-dispatched trait methods) and `is_trait_default: Some(_)` (trait-default-impl calls).

**Approach**: Two sub-cases.
- **`DynamicResolved`**: the resolved concrete impl is known. Can emit a direct call to the impl's Lean name (infrastructure in `to_lean_expr::call_to_node` handles this for proof fns).
- **`Dynamic`**: use Lean's typeclass machinery. Emit `TraitName.method (instance)` where `instance` is inferred from the receiver type.

**What to read first**: `fn_call_to_vir.rs` for how Verus surfaces trait-call kinds, `to_lean_expr.rs::call_to_node` for the proof-fn trait-method handling that already works.

**Gotcha**: Trait methods can have generic type params on the method itself, stacked on top of the trait's type params. Substitution gets nested. Trait default impls are yet another path — the impl is the trait's default body with `Self` substituted.

## Code review strategy

When landing non-trivial work, we run multi-lens reviews. Each lens catches a different class of issue; a single "read it over" pass misses most of them. The five lenses:

### 1. Linus hat

Role-play a grumpy maintainer who's seen every possible misuse of Rust. Ask: *would this annoy me if I had to review it in someone else's PR?*

Looks for:
- Clever abstractions that make code harder to understand
- Defensive code for scenarios that can't actually happen
- Flag soup — `Option<...>` + `bool` fields that can never take independent values
- Bad naming (the code doing what the name doesn't say, or vice versa)
- Orphaned docstrings (comments pointing at the wrong thing after an edit)
- Double-commented blocks (edit history showing through)
- Code that lies about what it does (function signature says pure, body has mutation)

Canonical session example: the typ_inv_exps smuggling and RefCell-in-pure-fn from the first cleanup pass, the orphaned WpCtx docstring from the second.

### 2. FP lens

Ask: *what's mutable that could be immutable? What's stateful that could be a parameter?*

Looks for:
- Hidden state via `RefCell` / `Cell` / thread-locals where a parameter would work
- Fn signatures that lie about purity
- Accumulators that could be folds / iterator chains
- Shared mutable state across module boundaries

Canonical session example: replacing `WpCtx::tactus_asserts: RefCell<Vec<_>>` with `collect_tactus_haves` two-pass walk. `lower_wp` went from pure-but-lying to actually pure.

### 3. Comprehensive coverage

Ask: *what code paths have no test?*

Looks for:
- Variants of a new enum that aren't exercised
- Edge cases at the boundaries (empty, singleton, nested, maximum)
- Negative tests — if we claim something is rejected, is there a regression test?
- Interaction tests — two features in the same fn

Canonical session example: after landing #57 (break/continue), adding tests for labeled-break-rejected, nested-loops-inner-break, break-plus-continue-in-same-body, return-inside-loop-with-break.

### 4. Upstream-brittleness

Ask: *what breaks silently if Verus changes X?*

Tactus is a fork of Verus. Every rebase could change fields, lowerings, or AST shapes. The "triangle" of defences (full description in DESIGN.md § "Upstream-robustness patterns"):
- **Explicit field destructures** (no `..` in `StmX::_` patterns) — Verus field additions cause compile errors
- **Shared helpers** (`peel_transparent`, `renders_as_lean_int`, etc.) — one edit site instead of N parallel ones
- **Shape-drift tests** (e.g., `full_check_decrease_height_shape_pinned`) — synthetic SST constructed to the expected shape; drift fails with a pointed error message

Looks for:
- New pattern matches on Verus types using `..`
- Logic assuming specific Verus AST shapes without a compile-time or test-time guard
- Reliance on pass-ordering invariants (e.g., "the recursion pass inserts X before Y") without a shape-drift test

Canonical session example: the `test_exec_auto_proof_block_not_tactus` test guards against Verus's `auto_proof_block` ever generating empty synthetic blocks (would mis-classify them as user-written Tactus blocks).

### 5. Documentation / deferrals

Ask: *what's landed but not documented? What caveats are we implicitly carrying?*

Looks for:
- Behaviour that's correct but counterintuitive (proof-block tactics affecting the outer goal, for instance)
- Deferrals that exist in code comments but not in DESIGN.md's deferrals catalogue
- Removed negative tests without corresponding positive tests
- Stale comments (assertions about rejected features that are now accepted, etc.)

Canonical session example: documenting the proof-block goal-modifying-tactic semantics in DESIGN.md and pinning it with a test so users (and future maintainers) aren't surprised.

### How to apply

For a landing that introduces a new variant, adds a few fields, or changes a pipeline arm:

1. Do the work. Get tests green.
2. Run the five lenses against the diff. For each lens, write down what you'd fix.
3. Triage: what's worth fixing now, what's worth filing, what's not worth it.
4. Do the "worth fixing now" in a follow-up commit labeled as review cleanup.
5. Update DESIGN.md if any caveat / deferral surfaced.

The cleanup pass usually takes 10-30 minutes and catches 3-5 real issues even on code that looked fine. It's the difference between "it works" and "it's clean."

## Testing infrastructure

### Test suites at a glance

| Binary | Count | What it tests |
|---|---|---|
| `cargo test -p lean_verify --lib` | 104 | AST pp (precedence, tuples, indexing), `substitute` (shadowing, capture avoidance), `Wp` / `lower_wp` / `needs_peel` / `contains_loc` / `lift_if_value`, type translation, sanity check scope tracking, lean_process |
| `cargo test -p lean_verify --test integration` | 7 | Tactus-prelude + Lean invocation end-to-end on hand-written Lean |
| `vargo test -p rust_verify_test --test tactus` | 161 | Full e2e: VIR → AST → Lean for proof fns + exec fns (all slices) |
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

When `tactus_auto` fails, the error message includes the generated `.lean` file path:

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
        lean_ast.rs            ← typed Lean AST + smart constructors +
                                 substitute (+27 unit tests)
        lean_pp.rs             ← precedence-aware pp + tactic-start tracking
        sanity.rs              ← post-codegen reference check
        dep_order.rs           ← walker + coverage instrumentation
        generate.rs            ← orchestration + debug_check
        to_lean_type.rs        ← TypX → Expr
        expr_shared.rs         ← shared-leaf helpers (op tables, constants,
                                 Clip coercion) — see module docstring for
                                 the trait-unification / SST-routing analysis
        to_lean_expr.rs        ← VIR Expr → Expr
        to_lean_sst_expr.rs    ← SST Exp → Expr (_checked primary,
                                 infallible wrapper; shared helpers)
        to_lean_fn.rs          ← VIR decls → Commands + LeanSourceMap
        sst_to_lean.rs         ← WpCtx + Wp DSL + build_wp / lower_wp
                                 (core of Track B)
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
      verifier.rs              ← routes proof fn AND exec fn to Lean;
                                 simplified_krate() getter for exec fn path
      util.rs                  ← dedent() delegates to lean_verify::source_util
      fn_call_to_vir.rs        ← tactus_span_from, enclosing_fn_is_tactus_auto
      rust_to_vir_expr.rs      ← Tactus proof-block synthesis (AssertBy-in-Ghost)
    rust_verify_test/tests/
      tactus.rs                ← 172 end-to-end tests
      tactus_coverage.rs       ← coverage matrix test binary
    vir/src/
      ast.rs                   ← FunctionAttrs.tactic_span + tactus_auto;
                                 ExprX::AssertBy.tactus: Option<TactusSpan>;
                                 TactusSpan / TactusKind;
                                 AssertQueryMode::Tactus { tactic_span, kind }
```

## Known limitations and tradeoffs

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the comprehensive catalogue. This section surfaces the ones most likely to bite a future session.

1. **HANDOFF.md staleness recurrence.** This document should be updated when a slice lands or architecture shifts. DESIGN.md's deferrals section is the canonical record of what's missing; keep this one aligned.
2. **`debug_check` only in debug builds.** Release users running Tactus get the cryptic Lean error instead of the pointed panic. Option: add `TACTUS_STRICT_CODEGEN` env.
3. **`noncomputable` baked into pp.** Every emitted `def` is `noncomputable def`. Correct for all current users; revisit if we ever emit computable helpers.
4. **Exec-fn source mapping** — tracked as task #51 in Pending work. Users currently `cat` the generated `.lean` path from the error message.
5. **Per-module Lean generation not implemented.** One `.lean` file per proof fn / exec fn. Fine at our scale; future work when we have many fns per module.
6. **`//` not allowed in tactic blocks.** tree-sitter's `line_comment` extra consumes `//` globally. Reported as a clear error at verification time; use `Nat.div` / `Int.div`.
7. **USize arith bounds are emitted but rarely auto-discharge.** `tactus_auto` can't handle symbolic `2 ^ arch_word_bits`. User proofs need `cases arch_word_bits_valid`. A future `tactus_usize_bound` tactic could automate this.
8. **Parallel VIR / SST renderers — shared leaves, not full unification.** Full analysis in DESIGN.md § "Two parallel expression renderers". Shared rules live in `expr_shared.rs`; walkers stay separate because the source trees are genuinely different shapes.
9. **Return inside a loop body writes the fn's ensures.** Semantically correct (it's a fn-exit, enforced by the DSL's `Wp::Done` terminator shape). Pinned by `test_exec_return_inside_loop` + `test_exec_return_inside_loop_with_break`.
10. **`needs_peel` is a recursive tree walk.** Constant-cost today but will want to become a constructor-level bit if more variants need peeling. Same rationale applies to `collect_tactus_haves`.
11. **`Wp::Branch` still clones `after` into both branches.** Exponential in nested if-depth. Fine for realistic code (DESIGN.md § "Known codegen-complexity trade-offs"). Rc/arena would fix cleanly; neither is worth the lifetime-threading cost yet.
12. **Proof-block goal-modifying tactics affect the outer goal.** `proof { simp_all }` simplifies the whole theorem goal, not just a local sub-proof. Pinned by `test_exec_proof_block_goal_modifying_tactic`; users coming from Verus's self-contained proof blocks may be surprised. The alternative (wrapping in a local `have`) breaks the common `have h : P := by tac` propagation case.
13. **Labeled break / continue** rejected in `build_wp`. Pinned by `test_exec_loop_labeled_break_rejected`. Would need a label-keyed stack of `WpLoopCtx` rather than the current single innermost-loop context.
14. **`enclosing_fn_is_tactus_auto` re-parses attrs per call site.** Each AssertBy / proof-block re-parses the enclosing fn's attrs. O(attrs) per site, cheap in practice; caching would add per-verification-unit state for unmeasured gain.

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
# 172 end-to-end tests
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Coverage matrix (1 test, asserts walker visits the expected variant set)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus_coverage

# 110 unit tests (AST pp, substitute, Wp DSL, sanity check, type translation,
#                 source_util — dedent + read_tactic_from_source)
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
