# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions, including a comprehensive "Known deferrals, rejected cases, and untested edges" catalogue.

## Current state

**161 end-to-end tests + 1 coverage test + 104 unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

**Track B status: all seven slices landed.** Exec fns can have: `let`-bindings, mutation (via Lean let-shadowing), if/else, early returns, loops (arbitrary nesting — sequential, nested, inside if-branches), function calls (direct named, including recursion and mutual recursion via Verus's `CheckDecreaseHeight` obligation), and arithmetic with overflow checking. Most realistic Rust exec fns should verify, modulo documented restrictions (no trait-method calls, no `&mut` args, no generic calls, no break/continue — see DESIGN.md § "Known deferrals").

### Recent session landings

This handoff is refreshed at the end of a deep review+refactor cycle. Highlights:

**Soundness hardening (review round 1, `f750a1a`, `9356631`).** Linus-hat review of the slice 7 StmX::Call implementation surfaced a real soundness blocker: `debug_assert_eq!` on param/arg count mismatch compiled to nothing in release, so a silent zip-to-shorter could bind wrong variables. Fixed by moving the check into the validator (now `build_wp_call`, then called `walk_call`) — Result-returning, not assert — and making the defensive assert in the builder unconditional. Other fixes in the same pass:
- `contains_loc` now peels transparent wrappers (Box/Unbox/CoerceMode/Trigger) so `&mut` args can't slip past buried under decoration.
- `is_trait_default` is rejected alongside `resolved_method` (dispatch shape that was previously un-guarded).
- `StmX::Call` fields destructured explicitly — future Verus additions force a compile-error audit.
- Three new tests: zero-arg call, many-arg call, `&mut` arg rejection.

**Termination obligations (`260f3b3`).** Previously any recursive exec fn verified as long as the body obligation passed. Now `sst_exp_to_ast_checked` lowers `InternalFun::CheckDecreaseHeight` — Verus's own recursion pass inserts this before every recursive call (including mutual recursion across an SCC), so we get termination for free for int-typed decreases. Non-int decreases rejected with a clear error pointing at the gap.

**Clip-rule sharing (`4396a58`).** `renders_as_lean_int` extracted to a pub(crate) helper so the VIR-AST renderer (proof-fn inlining) and SST renderer (exec-fn bodies) agree on which int ranges render as Lean `Int` vs `Nat`. Earlier the logic was duplicated with a "keep in sync" comment — a latent divergence risk.

**Validation / rendering unification (`906b59a`).** Merged `check_exp` and `sst_exp_to_ast` into one fallible impl — `sst_exp_to_ast_checked` is the primary case analysis; `sst_exp_to_ast` is an infallible wrapper that panics if called with unvalidated input; `check_exp` is a thin `.map(|_| ())` wrapper. Single source of truth for "what ExpX forms we support."

**Pipeline cleanups:**
- **WpCtx** (`ccaf300`) — collapsed `fn_map` + `type_map` threading (was 8 parameter sites) into a single context struct. Later gained `ret_name` and `ensures_goal` fields when the WP DSL landed.
- **Lean-AST substitution** (`eeb97f9`) — capture-avoiding `substitute` on `LExpr` replaces the previous `let p := arg; body` wrapping at call sites. Generated Lean now reads `tmp_ < decrease_init0` instead of the shadowed `(let n := tmp_; n) < decrease_init0` that defeated omega and required a `(simp_all; omega)` fallback rung. Comes with 18 unit tests covering lexical scoping, capture avoidance, and false-positive avoidance.
- **Post-simplify krate** (`1a72322`) — `verifier::Verifier::simplified_krate()` exposes the post-`ast_simplify` krate. Previously the exec-fn router saw the pre-simplify `FunctionX` while call-site args were post-simplify, forcing a `dummy_param_skip` / `is_zero_arg_desugared` workaround for zero-arg fns. Both sides now agree; workaround deleted.
- **`tactus_peel` destructures And hypotheses** (`ccaf300`) — `intro ⟨_, _⟩` alternative in the prelude macro.

**WP DSL refactor (`fba8170`).** Replaced `BodyItem` + positional `build_goal_with_terminator(items, rest, terminator, ctx)` with a proper WP algebra: `Wp<'a>` where each compound node carries its own continuation (`after: Box<Wp<'a>>`) by construction. Three structural wins:

- **Continuation is type-level.** `Done(LExpr)` has no continuation slot — "discard after Return" is enforced by the type system.
- **`Return` is cleanly fn-exit.** Previously Return wrote to whatever terminator was being threaded through (loop's `I ∧ D < d_old` inside a loop body; fn's ensures at top). Now it always writes `ctx.ensures_goal`. The DSL shape gets this right by construction.
- **`needs_peel` is one-line per variant.** Based on the node's own shape, not a post-hoc traversal looking for Loop/Call.

Net -59 lines (including fuller docstrings) and green on first compile — the types were right.

**Post-DSL review cleanups (`3ce09c3`, `92ac1a5`, `c635b51`, `daf1c95`).** Lazy-per-scope capture check in `substitute`, dead code deletion, Ok-turbofish cleanup, simplified_krate getter forcing Option handling. Refreshed docstrings (module-level + stale refs), dropped `Wp::Call::dest`'s dead Typ field, made `WpCtx::new` return `Result` so the "validate-first" precondition lives in the type signature. Added tests: 18 direct `substitute` unit tests, `test_exec_ctor_rejected` for the Ctor Err arm, `test_exec_call_mutual_recursion` for the SCC termination path, 25 direct `Wp` / `lower_wp` / `needs_peel` / `contains_loc` / `lift_if_value` unit tests, and `test_exec_return_inside_loop` pinning the Wp DSL's fn-exit semantics.

**Audit-driven coverage (`3e03e97`).** Walked recent code paths looking for things that compile but no test executes. Added 14 tests covering: multi-binder shadowing + capture (3), `substitute` missing ExprNode variants (UnOp, StructUpdate, ArrayLit, Anon, Index, Raw — 6 tests), `contains_loc` through `CoerceMode`/`Trigger`/stacked wrappers (3), `lift_if_value` through the `Bind(Let)` branch (2). These exercise real paths that e2e tests covered only indirectly.

**`Wp::Call::args` Vec→slice (`c02ee03`).** Dropped the unnecessary `Vec<&'a Exp>` allocation at every call site; now borrows `&'a [Exp]` directly from the SST's `Arc<Vec<Exp>>`. The one collapsible Box/Arc case found in an audit pass — the rest of the Box uses are load-bearing self-referential enums.

**Upstream-brittleness review (`2a2428c`).** Systematic audit of "what breaks if Verus changes X?" — our fork assumptions made explicit and caught at compile/test time:

- **Explicit field destructures** replace `..` in `StmX::Assign`, `StmX::Return`, `StmX::Loop` (6 previously-hidden Loop fields). Any Verus-side field addition now forces a compile-time audit.
- **Shared `peel_transparent(e: &Exp) -> &Exp`** centralises the Box/Unbox/CoerceMode/Trigger peel previously duplicated across `contains_loc`, `lift_if_value`, `render_checked_decrease_arg`. Adding a new transparent wrapper is one edit, not three parallel ones.
- **`full_check_decrease_height_shape_pinned` test** constructs a synthetic `CheckDecreaseHeight(Box(Let([(n, tmp)], n)), Box(n_old), False)` and asserts the substituted-form lowering. If Verus's encoding drifts, the assertion message points at `render_checked_decrease_arg` — turning a future recursive-fn verification mystery into a focused test failure with a named fix site.
- 12 total new tests (8 `peel_transparent` wrapper matrix + 4 shape-drift), including specific "Loc NOT peeled" and "If NOT peeled" checks.

**Expression-renderer shared leaves.** Investigated full unification of `to_lean_expr.rs` (VIR-AST; spec/proof fns + callee-spec inlining) and `to_lean_sst_expr.rs` (SST; exec-fn bodies). Rejected approaches 1 (trait over source-expression type) and 2 (route callee specs through SST) after reviewing the actual overlap — roughly half the variants are asymmetric (VIR-AST's `Block`/`Match`/`Ctor`/`Place` vs SST's `CheckDecreaseHeight`/`InternalFun`/flattened statements), so full unification would rearrange boilerplate without eliminating it. Chose approach 3: extract the rules both renderers must apply identically into a new `expr_shared.rs` module — `binop_to_ast`, `non_binop_head`, `const_to_node_common`, `clip_coercion_head` + `apply_clip_coercion`. SST also now calls `vir_var_binders_to_ast` directly for `BndX::Quant`/`Lambda`/`Choose` binder construction. Net: the op-table, constant-rendering, Clip-coercion, and binder-construction rules each live in exactly one place; walker asymmetry is documented, not pretended away. Full analysis in DESIGN.md § "Two parallel expression renderers — and why we didn't fully unify them".

**Track B tightening — roadmap + Ctor/match partial landing.** Laid out a 9-item roadmap across 3 tiers in DESIGN.md (see § "Track B tightening roadmap"). Started with Tier 2 item #52 (Ctor + pattern matching in exec fns) because FileLoader-adjacent blockers stalled Tier 1's user-tactic work (tasks #49/#50 — see their descriptions). Landed:

- **Struct Ctor + field access** end-to-end (test_exec_ctor_struct). `ExpX::Ctor` routed through the shared `ctor_node` helper; struct field access uses auto-derived accessors from Lean `structure`.
- **Enum Ctor construction** works (both spec and exec paths).
- **Accessor-fn synthesis** for multi-variant inductives: `datatype_to_cmds` now emits `def Type.isVariant : Type → Prop` and `def Type.Variant_val0 : Type → FieldTy` alongside the `inductive` declaration. `field_access_name` routes the desugared `Field` projections to the variant-scoped names. `Classical.propDecidable` is opened in the prelude so Prop discriminators decide in `if` contexts. Accessor emission is guarded by an `emit_accessors: bool` flag on `krate_preamble` — exec-fn entry passes true, proof-fn entry passes false (spec fns preserve native Lean match and the default-fallback of accessors breaks elaboration for types with non-Inhabited fields).
- **dep_order fix** (incidental): `walk_expr` was skipping `StmtX::Decl { init, .. }`, which meant `let p = Ctor(...)` missed the datatype reference and the preamble omitted the struct/enum definition. Fixed to walk the init `Place`.

Deferred to task #58: **automation** for enum pattern matching. The desugared if-chain over discriminators + @[simp]-unfolded accessors is structurally correct (Lean elaborates, types check), but `tactus_auto` (`rfl | decide | omega | simp_all`) can't case-split the enum scrutinee to close the residual `match k with | Variant _ => …` subterms. Current state pinned by `test_exec_match_enum_automation_gap`.

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

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the comprehensive catalogue. Headline items:

- **`break` / `continue`** — rejected.
- **Trait-method calls / generic calls** — rejected at the call site; require dispatch resolution + monomorphization / type-parameter substitution respectively.
- **`&mut` args** — rejected; would need havoc-after-call semantics.
- **Non-int decreases** — datatype-typed `decreases` clauses rejected because we don't encode a Lean `height` function yet. Int decreases work via `CheckDecreaseHeight`.
- **`proof { … }` blocks inside exec fns** — DESIGN.md claims support, untested; likely requires plumbing through `build_wp`.
- **`assert(P) by { tactics }` in exec fns** — user-provided tactic bodies for asserts; not wired.
- **`assume(P)` warnings** — DESIGN.md promises a "unproved assumption" warning; not wired.
- **USize arith rarely auto-verifies** — the bound is emitted, but `tactus_auto` can't discharge symbolic `2 ^ arch_word_bits`. Users need `cases arch_word_bits_valid` proofs.
- **Pattern matching in exec bodies** (`StmX` has no Match, but `ExpX::Ctor` / `ExpX::CallLambda` / `ExpX::ArrayLiteral` rejected — blocks match scrutinees containing these).
- **VIR / SST expression renderer unification** — shared leaves extracted into `expr_shared.rs` (op tables, constant rendering, `Clip` coercion, binder construction). The two walkers themselves stay separate because the source trees are genuinely different shapes; see DESIGN.md § "Two parallel expression renderers — and why we didn't fully unify them" for the full analysis of why approaches 1 (trait over source-expression type) and 2 (route callee specs through SST) were rejected.

### Adding new slices

1. Extend `sst_to_lean::build_wp` / `build_wp_call` / `build_wp_loop` to produce a new `Wp` variant (or accept a new form). Validation (Err for unsupported shapes) happens in the same pass.
2. Extend `Wp` enum with the new variant if the WP rule doesn't fit an existing one. Each new variant needs: constructor + `needs_peel` arm + `lower_wp` arm.
3. If the goal shape makes `tactus_auto` fail, add a prelude macro or emit a targeted `Tactic::Raw` at emission time. Keep `tactus_auto` dumb.
4. If new AST shapes are needed, extend `lean_ast` (preferably via smart constructors) and `lean_pp`. If the new shape has binders, extend `lean_ast::substitute` and `collect_free_vars` — three places to edit.
5. Add snippets to `tactus_coverage::run_snippets` if new VIR variants become reachable via `dep_order::walk_expr` / `walk_place`.
6. Update DESIGN.md — both any relevant architecture section and the deferrals catalogue.

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
      util.rs                  ← dedent() + 8 unit tests
    rust_verify_test/tests/
      tactus.rs                ← 161 end-to-end tests
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
7. **USize arith bounds are emitted but rarely auto-discharge.** `tactus_auto` can't handle symbolic `2 ^ arch_word_bits`. User proofs need `cases arch_word_bits_valid`. A future `tactus_usize_bound` tactic could automate this.
8. **Parallel VIR / SST renderers — shared leaves, not full unification.** `to_lean_expr.rs` (VIR-AST for proof fns + callee inlining) and `to_lean_sst_expr.rs` (SST for exec fn bodies) render structurally different trees. The common rules live in `expr_shared.rs`: op tables (`binop_to_ast`, `non_binop_head`), constant rendering (`const_to_node_common`), Clip coercion (`clip_coercion_head`), plus existing shared helpers (`type_bound_predicate`, `integer_type_bound_node`, `renders_as_lean_int`). The walkers themselves stay separate because the asymmetric variants (VIR-AST `Block`/`Match`/`Ctor`/`Place` vs SST `CheckDecreaseHeight`/`InternalFun`/flattened statements) would still need per-path dispatch even behind a unification trait. Full unification investigation recorded in DESIGN.md § "Two parallel expression renderers — and why we didn't fully unify them".
9. **Return inside a loop body writes the fn's ensures.** Semantically correct (it's a fn-exit, enforced by the DSL's `Wp::Done` terminator shape). Pinned by `test_exec_return_inside_loop`.
10. **`needs_peel` is a recursive tree walk.** Constant-cost today but will want to become a constructor-level bit if more variants need peeling.
11. **`Wp::Branch` still clones `after` into both branches.** Exponential in nested if-depth. Fine for realistic code (documented in DESIGN.md § "Known codegen-complexity trade-offs"). Rc/arena would fix cleanly; neither is worth the lifetime-threading cost yet.

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
# 161 end-to-end tests
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Coverage matrix (1 test, asserts walker visits the expected variant set)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus_coverage

# 104 unit tests (AST pp, substitute, Wp DSL, sanity check, type translation)
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
