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

Tree-sitter-tactus recognizes `import` declarations at the top of files via the `import_declaration` grammar rule: `'import' Ident('.' Ident)*` (no semicolon terminator; matches verus_syn's parser at `builtin_macros/src/syntax.rs:4485-4505`). Without this rule, tree-sitter's error recovery from raw-Rust parse of the `import` line truncates the parse and downstream `assert_expression` / `proof_block` nodes inside exec fn bodies fail to register — FileLoader then sees no brace bodies to sanitize and tactic text reaches rustc as identifier references (BUG-exec-fn-imports.md bug 2, fixed 2026-05-17).

**Attribute propagation**: `builtin_macros/src/syntax.rs:4807` attaches `lean_import` attrs to fns the file's imports should reach. **Both** proof fns with `tactic_by` (`by { ... }` tactic body) **and** exec fns with `#[verifier::tactus_auto]` get attached — file-level imports reach every generated Lean file regardless of fn kind. `rust_to_vir_func` threads these to `FunctionAttrsX.lean_imports`; both `check_proof_fn` and `check_exec_fn` read from `vir_fn.x.attrs.lean_imports` and pass to `krate_preamble`, which emits the imports at the top of every generated `.lean` file. (Pre-2026-05-17 the attachment was gated on `tactic_by`, so exec fn theorem files got no imports — Mathlib tactics inside `assert(P) by { tac }` raised "unknown tactic" at Lean elaboration. BUG-exec-fn-imports.md bug 1.)

**Attribute-vs-function-item parse disambiguation**: tree-sitter-tactus's grammar declares an explicit GLR conflict `[$._statement, $.function_item]` for the two ways to parse `#[attr]\nfn f(){}` — as a standalone `attribute_item` followed by sibling `function_item`, or as a `function_item` containing `attribute_item` as a child. Tools that walk the parse tree (Tactus's FileLoader checking for `#[verifier::tactus_auto]` via `function_has_tactus_auto_attr`) expect the nested form. In specific contexts — a preceding `tactic_block` (proof fn's `by { }`) plus intervening `line_comment` extras — tree-sitter silently flipped to the standalone-sibling parse, leaving FileLoader unable to find the attr and downstream tactic bodies unsanitized (BUG-fileloader-by-in-comment.md). Fix: `prec.dynamic(-1, $.attribute_item)` on the standalone path in `_declaration_statement` deprioritizes it without removing the production (which would break unrelated "Attributes" / "Derive macro helper attributes" corpus tests). Matches Rust semantics — outer attributes always attach to a following item; the standalone form is only a tree-sitter GLR fallback. Pinned by corpus test "Attribute nested in function_item after tactic_block + comments" + e2e `test_fileloader_by_in_comment_regression` + unit `test_by_in_comment_does_not_break_sanitization`.

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

Spec fn opacity follows Verus's `Opaqueness` enum, NOT a Lean-side default. The mapping (in `to_lean_fn::spec_fn_to_ast`):

- Default `spec fn` (Verus `Opaqueness::Revealed { visibility }`) → `noncomputable def`
- `#[verifier::opaque] spec fn` (Verus `Opaqueness::Opaque`) → `@[irreducible] noncomputable def`
- `open spec fn` is also `Opaqueness::Revealed` (with broader visibility) → `noncomputable def`

This means the default is **transparent**, matching Verus's spec semantics: the body is visible within its visibility scope and treated as definitionally equal to its body during VC generation; `@[irreducible]` is only emitted when the user explicitly opts in via `#[verifier::opaque]`.

(An earlier draft of this doc claimed "irreducible by default" with the opposite mapping. That was aspirational — the design considered making spec fns implicitly opaque to give users full control over unfolding — but was never implemented. Verus's `Opaqueness` discriminator is the source of truth and the code emits faithfully against it.)

Tactic implications worth knowing:

- `unfold f` in tactic blocks targets occurrences of `f` in the **goal** by default. For occurrences in hypotheses, use `unfold f at h` or `unfold f at *`. Pinned by `test_chained_compare_in_spec_fn_body` (uses `at *` for a hypothesis-position occurrence) and `test_chained_compare_in_spec_fn_body_via_ensures` (the goal-position case where bare `unfold f` works). This is standard Lean behaviour, not a Tactus quirk; flagged here because it's the most common stumble for users coming from Verus's reveal-based mental model.
- `simp_all` won't unfold `f` even when transparent — Lean's `simp` only unfolds defs marked `@[simp]` or explicitly listed (`simp_all [f]`).
- `decide` reduces concrete computations; if `f` is irreducible (i.e., the user marked it `#[verifier::opaque]`), `decide` can't reduce through it.

The `reveal(f)` pattern from Verus has no analog in Tactus — Tactus has no fuel concept. The closest equivalent is `proof { unfold f }` in `tactus_auto` exec fns or `unfold f` directly in proof-fn `by { }` blocks. See "reveal_with_fuel and unfold in Tactus" below.

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

**`DiagLocation` enum replaces two parallel `Option` fields (2026-05-19).** `TactusDiag` (and `FormattedDiag`) used to carry `rust_span: Option<vir::messages::Span>` + `proof_fn_body_line_offset: Option<usize>`. The three valid combinations (exec-fn obligation has Some-Span/None-offset, proof-fn diag has None-Span/Some-offset, sanity-failure has None/None) were three out of four representable states — the "both Some" case was meaningless and would have caused the verifier to silently prefer the span over the offset. Post-fix: `enum DiagLocation { Direct(Span), ProofFnBodyLine(usize), Unknown }`. Construction sites must pick a variant; consumers exhaustively match. The TOCTOU-ish "did we set both?" / "neither was set" states are gone. Surfaced by the first review-pass lens (#13, typed-invariant) on the error-span UX arc; same pattern as `MutArgInfo`, `LoopInvKind`, `DecreaseLevel`.

**The pattern, named.** When a value's type doesn't carry the property the code requires of it, and the requirement is checked at runtime via panic or assertion: introduce a newtype, make its constructors the only path that satisfies the property, and let the type system enforce the rest. Reviewer-visible at every call site (the constructor name documents the source); refactor-resistant (half-finished migrations don't compile); future-proof (new code added in years can't accidentally break the invariant). The cost is a typed wrapper. The benefit is a soundness hole that's structurally unrepresentable.

### Potential future applications of the typed-invariant pattern

Candidates noted from prior audits but not yet promoted. Each is a runtime-checked invariant that could be lifted to the type system; each was judged below the cost/benefit threshold *for now*. If a related bug surfaces — or if the codebase grows to where the runtime check becomes load-bearing — they're the natural next applications.

* **`OblCtx` frame ordering invariant.** `OblCtx::with_frame` accepts any `CtxFrame` in any order; `wrap` folds outermost-first to preserve source-scoping. The "outermost-first" invariant is a documented contract on the API, not enforced by the type. A typed builder pattern (e.g., separate `OblCtxOuter` / `OblCtxInner` typestates with constructors that allow only consistent additions) would make wrong-order use a compile error. Cost: more types, more transitions. Current cost of the runtime convention: zero bugs to date.

* **`Tactic::Raw` vs `Tactic::Named`.** The `Tactic` enum has a single `Raw(String)` variant covering both arbitrary-text closer tactics (`tactus_auto`, user overrides) and structurally-meaningful names. A split (`Raw(String)` for free-form text, `Named(LeanName)` for known prelude tactics) would let the pp / sanity layers treat them differently without parsing the string. Today everything goes through string equality; no bug has surfaced from the conflation.

* **`format_rust_loc` returning typed `RustLoc`.** The function returns a `String` formatted as `path:line:col`. Downstream `find_span_mark` parses it back to extract the line. A typed `RustLoc { path, line, col }` struct would eliminate the parse-format roundtrip. Bounded mechanical work; the current shape is small enough that the round-trip cost isn't visible.

### Potential future infrastructure

Pieces of infrastructure that, if built, would simplify or unify existing code. Distinct from the typed-invariant section above — those are patterns to apply at specific sites; these are *new structure* that would replace ad-hoc compositions.

* **`RewritePipeline` for SST→SST passes.** Tactus runs several SST→SST rewrite passes inside `exec_fn_theorems_to_ast` (in `sst_to_lean.rs`): `normalize_mut_ref_in_stm` (#95) maps new-mut-ref shapes back to legacy form; `rewrite_varat_for_mut_params_in_stm` (#94) renames pre-state references; `insert_nat_coercions_in_stm` (BUG-as-nat-cast.md, 2026-05-15) inserts `Clip(Nat, _)` at Call sites where args render as Lean Int but params render as Lean Nat; `is_synthetic_assume_to_drop` filters out Verus-internal `Assume(HasResolved(...))` / closure-spec assumes during walk; `collect_borrow_mut_links` + `is_borrow_mut_linkage_assign` (2026-05-26) eliminate Verus's BorrowMut indirection in caller-side new-mut-ref calls — see "BorrowMut elimination" entry below. They compose by being called in sequence in the orchestrator (so the order is implicit in the Rust source).

  A typed pipeline — e.g., `RewritePipeline::new().drop_synthetic_assumes().normalize_mut_ref(&params).rewrite_varat(&params).eliminate_borrow_mut().insert_nat_coercions(&fn_map).run(stm)` — would make the data flow explicit, let new passes be added without touching the orchestrator, and surface ordering invariants (e.g., "normalize before rewrite") as compile errors when a new pass is inserted in the wrong place.

  Current cost-benefit: borderline. The five current passes are stable and the orchestrator is one call site. The win shows up when the next rewrite lands (likely a candidate: a pass that strips synthetic `BuiltinSpecFun::ClosureReq` calls at spec position, for #124's exec-mode closure calls if that ever unblocks upstream).

* **BorrowMut elimination (2026-05-26)** — Tactus-side pre-pass that removes Verus's `LocalDeclKind::BorrowMut` indirection in the simple `&mut <local>` case. Verus emits `let tmp = BorrowMut(y); ... y = MutRefFuture(tmp); bump(tmp);` for SMT borrow-tracking; Lean's binding model handles direct mutation natively, so the indirection isn't needed in our target. The pre-pass detects the linkage `Assign(user_local, Var(borrow_mut_local))` plus SSA-rename aliases, drops the linkage Assign from the body, and redirects the call's mut-arg target so Phase 4 rebinds the user-local directly. Result: the SST renders as if the user had written "bump mutates y directly" — matching what they did semantically. Same family as #94 / #95 / BUG-as-nat-cast normalization passes (Verus emits SMT-shaped output; Tactus pre-passes into Lean-faithful form). Helpers: `collect_borrow_mut_links`, `resolve_borrow_mut_aliases`, `is_borrow_mut_linkage_assign`, `borrow_mut_key` in `sst_to_lean.rs`. Pinned by `test_exec_call_mut_arg_new_mut_ref` / `_use_after` / `_two_mut_args_new_mut_ref` / `test_new_mut_ref_pre_post_substitution_probe` (the last three were previously passing via the False-hypothesis soundness bug — see § "Soundness trade-offs accepted" below).

* **Public TypX walker for lean_verify.** `vir::ast_visitor::map_typ_visitor` is `pub(crate)` and not accessible from `lean_verify`. Tactus has two near-duplicate structural TypX walkers today: `to_lean_type::walk_typ` (read-only visitor) and `impl_subst::walk_typ_for_projections` + `impl_subst::rewrite_typ_rec` (visit + transform). They share the same shape — list every TypX variant explicitly, recurse into nested Typs, leave leaves as-is — but each is hand-rolled. Exposing a `pub` `map_typ_visitor` from VIR (or a Tactus-side wrapper that delegates to it) would let both sites share the walker, surfacing a new TypX variant as a compile error in the wrapper alone instead of N matching locations.

  Current cost-benefit: low priority while the walkers are stable. Both are exhaustive-match today (no `_ =>` catch-all), so a new TypX variant fails at compile time in each — the safety property is already there, just duplicated. Worth revisiting if a third TypX walker enters Tactus.

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

The sanitizer preserves `\n` AND `\r` (not just `\n`): newline positions matter for `lines`, and `\r` matters for `normalized_pos` (rustc normalizes `\r\n` → `\n` at SourceFile construction; if sanitized had bare `\n` where the original had `\r\n`, the two views' `normalized_pos` tables would disagree, breaking the diagnostic-source swap described below).

### Diagnostic source preview swap (landed 2026-05-19)

The FileLoader sanitization is correct for parsing — rustc lexes blank-space content trivially. But it leaves rustc's `SourceMap` holding sanitized content as the canonical view of the file. When a verification error fires inside a tactic body, rustc's diagnostic renderer pulls the line from `SourceFile.src` and renders something like:

```
  --> test.rs:18:5
   |
18 |          
   |     ^^^^^
```

The `-->` line:col is correct for navigation (`vi test.rs +18`), but the inline source preview is blank because the lexer saw spaces where `omega` lives. Compounded across 5–10 failures per proof iteration, this adds a real workflow tax.

**The fix** (small, scoped):

1. `TactusFileLoader::read_file` caches the original content per canonical path in a static `OnceLock<Mutex<HashMap<PathBuf, Arc<String>>>>` before sanitization.

2. At diagnostic emission time, `Reporter::report_as` (which runs on the main thread, the only consumer of `sf.src` via rustc's diagnostic renderer) calls `spans::swap_source_for_diagnostics` for each span's file. The swap:
   - Looks up the SourceFile via `SourceMap`.
   - Recomputes `multibyte_chars` from the original content (a ~20-line UTF-8 byte-length iteration; rustc's `analyze_source_file` is `pub(crate)` so we replicate the logic locally).
   - Writes `sf.src` and `sf.multibyte_chars` through a `*mut SourceFile` derived from `Arc::as_ptr`.
   - Memoizes per file via a static `SWAPPED_FILES` set.

3. rustc then renders the preview with the original content:

```
  --> test.rs:18:5
   |
18 |     omega
   |     ^^^^^
```

`lines` and `normalized_pos` need no recompute because the sanitizer preserves `\n` and `\r` byte-for-byte — the metadata matches between sanitized and original by construction.

**Safety of the `unsafe` swap.** Three invariants:

1. *Single-threaded reader.* Rustc's diagnostic renderer reads `sf.src` only via `SourceMap::span_to_source`, which is called from `Reporter::report_as` on the main thread. Verus's worker threads queue `Message` values over an mpsc channel — they hold vir `Span`s with `BytePos` values, not `Arc<SourceFile>`, and never read `sf.src`.

2. *No concurrent mutation by rustc.* rustc creates `SourceFile`s during file load and doesn't mutate them after. Our swap is the only write to `sf.src` post-construction.

3. *No concurrent swap.* The "have we swapped this file?" check and the unsafe write happen inside the same `SWAPPED_FILES` lock acquisition, so two threads that call `swap_source_for_diagnostics` for the same file serialize: the first thread does the write and inserts the entry; the second sees the entry and returns without writing. Without this, two `*mut` writes to the same location without synchronization would be UB even though they'd produce identical content. The helper is also `pub(crate)` rather than `pub` — the safety story depends on Reporter-only invocation, so narrowing visibility prevents accidental external callers from violating invariant (1).

**Point-in-time consistency.** Both `swap_source_for_diagnostics` and `tactic_body_line_span` (the proof-fn helper that computes per-tactic-line spans via byte arithmetic) read from the same `TactusFileLoader::ORIGINAL_CACHE`. If the user edits the file between rustc parsing and diagnostic emission, both helpers see the SAME cached snapshot — the one rustc parsed, the one the spans were resolved against. Computing one helper against disk-current content and the other against cache would risk the span pointing at line N of new content while the rendered preview showed line N of old content.

**`DiagLocation` enum** (in `lean_verify::generate`) makes the diagnostic-location options structurally exclusive: `Direct(Span)` for exec-fn obligations whose span we already have, `ProofFnBodyLine(usize)` for proof-fn diagnostics that the verifier resolves to a span via `tactic_body_line_span` at emit time, or `Unknown` for pre-Lean rejections (sanity-check failures, codegen-rejected fn shapes). Replaces an earlier two-Option encoding (`rust_span: Option<Span>` + `proof_fn_body_line_offset: Option<usize>`) whose "both Some" permitted state was meaningless. Same typed-invariant pattern as `AssertKind` sum split, `LoopInvKind`, etc.

**Alternatives rejected.** We explored several before settling on the swap-with-recompute:

- **Selective sanitization** (only blank chars rustc's lexer can't handle, keep ASCII intact). Same fundamental problem documented elsewhere in this section: every Lean syntax that's tokenizable-but-meaning-different in Rust becomes an ongoing maintenance edge case (`'x` as Lean prime vs Rust char literal start, `//` as Lean integer-division vs Rust line-comment, every new Unicode operator). Brittle and unbounded.

- **Tree-sitter-guided selective sanitization** (preserve ASCII tokens, blank only Lean-specific tokens like `--` blocks and Unicode). More principled detection, same underlying brittleness — anything kept still has to lex as valid Rust, which is the unbounded class.

- **Append source preview to the message body** (read original, format `18 |     omega\n   |     ^^^^^` in the error text). Works always, requires no `unsafe`, but renders the redundant blank rustc preview below. Two pseudo-previews per error.

- **Drop the rustc `Span` for proof-fn body errors; hand-render `-->`/`|`/source-line in the message text**. Clean visually, but loses structured-span integration with JSON-mode tooling (rust-analyzer etc.) and depends on text-mode editors parsing `-->` patterns from arbitrary message bodies.

- **Replace multi-byte chars with multi-byte Pattern_White_Space chars (LRM/NEL)** so `multibyte_chars` matches by construction without a recompute. Sanitizer is ~20 lines more complex, plus a quiet dependence on rustc's `Pattern_White_Space` set being stable across versions. The recompute-on-swap approach turned out to be simpler in practice — the UTF-8 byte-length helper is mechanical and version-independent.

- **Fork `rustc_span` to add a `swap_src` API or bypass the hash check on `add_external_src`**. Verus already forks `rustc_hir_typeck` and `rustc_mir_build`, so this is in-scope, but it's a substantial new fork to maintain. The `Arc::as_ptr`-cast swap accomplishes the same thing in ~25 lines with no vendoring.

- **Wrap rustc's emitter to post-process the rendered text** (substitute blank lines with disk content via regex on the output). Possible but tied to rustc's exact output format (would break silently on any format change).

The chosen swap is structurally the smallest change that preserves all editor integration (`-->` text, JSON spans, source navigation) and renders correct content. The `unsafe` is bounded by clear invariants and lives behind a documented helper.

### `//` in tactic blocks

`//` (Lean's integer division) is **not supported** in tactic blocks. Use `Nat.div` or `Int.div` instead. This avoids a fundamental conflict: Rust's lexer treats `//` as a line comment (consuming the rest of the line including potential `}`), and tree-sitter's extras mechanism makes `//` comments globally unavoidable in the grammar.

In practice, `//` rarely appears in tactic proofs. Tactics are proof steps (`omega`, `simp`, `ring`, etc.), not computations. `--` is the Lean comment syntax and works correctly.

### tree-sitter-tactus grammar

tree-sitter-tactus has Lean-aware rules for tactic block content:
- `_tactic_brace_body`: `{ ... }` with Lean-aware content parsing
- `_tactic_item`: handles `--` comments, `/- -/` nestable block comments, `"..."` strings, Unicode content, nested `{ }` braces
- `line_comment` stays in `extras` (global) — `//` is treated as a Rust comment everywhere including tactic blocks

The grammar has **184 tests** including 36 tactic-specific tests covering all Lean syntax edge cases.

### TODO: Unicode in `verus_code!` test fixtures

The FileLoader sanitization described above only runs on real `.rs`
files. The `verus_code!` proc macro used in
`rust_verify_test/tests/tactus.rs` captures its body as a Rust
`TokenStream`, which means rustc's tokenizer sees the raw source and
rejects non-ASCII tokens (`→`, `⟨⟩`, `≤`, `∀`, `—`, etc.) with
`error: unknown start of token` before the macro ever runs. The
practical consequence: probes written inline in `verus_code! { … }`
must use ASCII-only Lean tactic syntax (e.g., `Self -> Unit` instead
of `Self → Unit`, `<=` instead of `≤`).

This is a test-infrastructure gap, not a user-Tactus gap — real user
code that lives in `.rs` files on disk goes through the FileLoader
path and Unicode works correctly there. The end-to-end Mathlib
tactics tests at `rust_verify_test/tests/tactus.rs` get away with
ASCII because tactics like `omega`, `ring`, `decide`, `simp_all`, etc.
don't intrinsically need Unicode.

Plausible fixes when the gap matters (none implemented today):
- **(a) Route test inputs through a temp file** that DOES go through
  FileLoader. The macro would write `$body` to a temp file and
  invoke verus with that path instead of using stdin. Medium effort;
  matches the production code path more closely. Test isolation
  already creates per-test temp dirs (`TACTUS_KEEP_TEST_DIR`), so
  the infrastructure is partly there.
- **(b) Accept `verus_code!` body as a raw string literal**
  (`verus_code!(r#" ... "#)`). Strings can contain arbitrary
  Unicode. Heavy migration — every existing test would need to be
  rewritten.
- **(c) Document and accept the constraint.** Tests use ASCII Lean;
  real `.rs` files use full Unicode. Cheapest, status quo.

Today's pragmatic answer is (c). Revisit if a probe genuinely needs
Unicode tactic syntax that can't be expressed in ASCII.

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

### Classical-logic commitment

Tactus is **fully classical**. `TactusPrelude.lean` opens `Classical.propDecidable` as an instance, making every `Prop` decidable. This commits us to a Lean kernel with excluded middle, axiom of choice, and double-negation elimination available — equiconsistent with intuitionistic + classical axioms, no additional soundness risk (Lean's kernel already supports these).

Tactus inherits this commitment from Verus: Verus's Z3 backend reasons classically, and Verus's spec semantics implicitly assume classical logic for `choose`, `exists`, and bounded-quantifier reasoning. Tactus matching Verus's commitment is continuity, not a regression.

**What classical gives users (and Tactus's codegen):**
* **Excluded middle.** `Classical.em P` proves `P ∨ ¬P` for any spec-level proposition. Pinned by `test_proof_classical_excluded_middle`.
* **Decidability for if/match.** Match-defined discriminator Props from synthesized `Type.isVariant` decide in `if <prop> then …` contexts. Without `Classical.propDecidable`, the `if` elaborator can't resolve the `[Decidable P]` instance and elaboration fails.
* **Total epsilon for `Choose`.** `BinaryOp::Bind(BndX::Choose, …)` renders to `Classical.epsilon (fun … => cond ∧ body)`, which returns *some* witness satisfying the predicate without requiring an existence proof. Used by Verus's `choose|x| P(x)` spec idiom.
* **Total accessor fallbacks.** Multi-variant enum accessors (`Type.Foo_val0 : Type → FieldTy`) use `match x with | Type.Foo v _ => v | _ => Classical.arbitrary _` for the unreachable-other-variant cases. `Classical.arbitrary` requires `[Nonempty α]`, which holds for all primitive types Tactus actually emits accessors on.
* **`Seq.index` existence.** The prelude's `opaque index` is justified by `Classical.choice` (any total function `List α × Nat → α` agreeing with `List.get` in-bounds satisfies our axioms).

**Cost of classical:** `decide` won't reduce a `Classical.propDecidable`-derived `Decidable P` instance through to a concrete truth value, because the decision procedure is `Classical.choice`-based rather than constructive. `tactus_auto`'s ladder uses `omega` / `simp_all` rather than `decide` for free-var goals, so this rarely bites. When it does, the user can write `by_cases` or `Classical.em` in a `proof { }` block explicitly.

**Why this isn't a transparency violation.** Classical logic is *substrate*, not behavior. It's in the same category as `arch_word_bits` or `Seq.index` — invisible at use sites because it's foundational, not because Tactus is doing something the user can't see. Audited 2026-05-11 (#151); confirmed all four uses are load-bearing and appropriate to Tactus's spec-first model. The audit's deliverable was this section — visibility at the document level rather than at the use site.

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

Body-less spec fns (landed 2026-05-12):
```rust
pub uninterp spec fn my_oracle(x: int) -> int;
```
→
```lean
axiom my_oracle : Int → Int
```

Used for: `pub uninterp spec fn` (deliberately uninterpreted on the
Verus side), external-body spec fns (Verus's escape hatch), and
cross-crate spec fns whose body was stripped at `export_crate` time.
Lean's `axiom` is the right encoding — declares a constant whose
value is unspecified, matching Verus's "this is just a symbol with
a type" semantics. (The pre-2026-05-12 code path emitted
`def f := sorry` for body=None, but dep_order's `build_spec_fn_map`
filtered body=None fns out before they reached emission, so the
sorry branch was dead code. Audit removed the filter and routed
through `Command::Axiom` instead — see `to_lean_fn::spec_fn_to_ast`.)

Trait method decls (`FunctionKind::TraitMethodDecl`) are excluded
from this standalone-def emission regardless of body presence:
their content lives inside the class declaration produced by
`trait_to_ast`, not as top-level defs. Default bodies on trait
method decls become class-method defaults (see "Trait class and
instance emission" below).

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

VIR's `TypX::Bool` renders unconditionally as Lean `Prop`, regardless of context. `to_lean_type::typ_to_node` is mode-blind — both spec-position and exec-position `bool` arrive at the renderer the same way and produce the same `Prop` output. An exec fn `fn check(b: bool)` emits a theorem binder `b : Prop`, and bool-typed body expressions inherit the Prop typing.

**An earlier draft of this section** claimed Tactus rendered bool as `Prop` in spec context and `Bool` in exec context. That was aspirational and never implemented; the current behaviour is the deliberate landed choice (see § "Considered: context-sensitive bool rendering" below for why).

#### Why always-Prop

* **Tactus is spec-first.** Verification obligations (`requires`, `ensures`, `assert(P)`, loop invariants) are all Prop by construction. Exec-fn bodies *embed* spec expressions through the WP encoding — so the dominant typing context in generated Lean is Prop. Treating every `bool` as `Prop` keeps the dominant case clean: `assert(flag)` for a bool param renders as just `flag` with no coercion clutter.
* **`Classical.propDecidable` opens everything.** The prelude's `attribute [instance] Classical.propDecidable` makes every `Prop` decidable, so Lean can insert `decide : Prop → Bool` automatically wherever a `Bool`-typed operation receives a Prop arg. The coercion is total and well-behaved — no soundness risk, just goal-state verbosity.
* **No mode threading.** `typ_to_expr` has ~55 call sites across `to_lean_type.rs` / `to_lean_fn.rs` / `to_lean_sst_expr.rs` / `sst_to_lean.rs` / `to_lean_expr.rs`. A context-sensitive design would either thread a mode parameter through every one or fork into `typ_to_expr_spec` / `typ_to_expr_exec`. Either choice is invasive without a forcing concrete benefit.
* **The boundary case (`Bool`-typed operations on bool params) is closable with targeted simp lemmas.** When the `decide` coercions land in a goal that needs structural reasoning (xor commutativity, and/or-associativity, etc.), the fix is to add the relevant lemma to `tactus_auto`'s simp set. Done once for `Bool.xor_comm` (#121 follow-up, 2026-05-11); pattern is small and additive.

#### The trade-off accepted

The cost of always-Prop is **goal-state verbosity** when bool exec params flow into Bool-typed operations: `(decide b1 ^^ decide b2)` instead of `(b1 ^^ b2)`. This is cosmetic in error messages, not a soundness issue. The xor-commutativity-gap probe (`test_exec_xor_bool_free_vars_commutative`, #121) exercises this shape; closing it requires the user to write `assert(...) by { simp_all [Bool.xor_comm] };` — the lemma is right at the assertion site rather than buried in the closer.

This is the **canonical pattern for Bool-operation gaps** under always-Prop rendering: when `tactus_auto` falls through on a `(decide … ^^ decide …)` or similar, the user provides the relevant lemma explicitly. Per Tactus's design principle #1 (Transparency) and the canonical UX preference for visible proofs, this is *preferred* over extending the default closer's simp set — the proof on screen reflects the actual reasoning, not "and then `simp` did something."

If a class of Bool-operation gaps starts surfacing repeatedly across many fns in a real codebase, the right response is to introduce a *named* opt-in tactic (like `tactus_usize_bound` and `tactus_bit_vector` are today) that the user can compose into their `#[verifier::tactus_tactic("…")]` override — visible at the fn level, opt-in by name, NOT silently active everywhere.

#### Considered: context-sensitive bool rendering

Investigated and rejected (2026-05-11). The design would: thread a `mode: SpecOrExec` parameter through `typ_to_expr`, render exec-position `TypX::Bool` as Lean `Bool`, and emit explicit `b = true` coercions wherever a bool flows into a Prop-position spec expression (assertions, ensures clauses, requires clauses).

Cost: invasive (55+ call sites, each needs the new parameter), with the coercion bookkeeping moved from the Lean side (`decide` insertions, automatic) to the Tactus side (explicit `b = true` rendering, manual).

Benefit: less goal-state clutter for the narrow case of bool exec params used in Bool-typed operations.

The benefit is concrete but small. The cost is concrete and large. The pattern that surfaced the gap (`Bool.xor_comm` extension) generalises: whenever a new bool operation needs structural reasoning, add the lemma. This scales additively without touching the rendering pipeline.

**Conditions for revisiting** (any one would shift the cost-benefit):
* Multiple bool operations needing simp-lemma extensions that don't compose (today's `Bool.xor_comm` is one of perhaps a half-dozen analogous needs; if the list grows past ~5 we'd reconsider).
* A class of bool reasoning that genuinely can't close under `decide`-wrapped forms even with the right lemma.
* A user-facing pain point where the `decide`-wrapped goal shape is materially confusing.

None of these apply today; the simp-set extension covers the surface.

In VIR, equality and other Bool operations have the right shape — Verus's mode tracking IS present at the input. We're choosing not to consume the mode information, in favour of uniform Prop. The "ignore the mode" is the design, not a bug.

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

## Heartbeat annotations — LANDED (#123)

Lean's deterministic timeout uses `maxHeartbeats` (kernel reduction-step count, reproducible vs Z3's wall-clock-based rlimit). `#[verifier::heartbeats(N)]` provides per-fn override.

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

**Plumbing.** `Attr::TactusHeartbeats(u32)` parsed in `rust_verify::attributes` (validates positive integer at parse time); `FunctionAttrsX::tactus_heartbeats: Option<u32>` threads to VIR; `Theorem::heartbeats: Option<u32>` carried in lean_ast; `lean_pp::write_theorem` emits `set_option maxHeartbeats N in\n` before the `theorem` keyword when `Some(N)`. The `in` keyword is load-bearing — without it, the option would persist for subsequent declarations in the same file.

**Both fn paths covered.** Proof fns: `to_lean_fn::proof_fn_to_ast` reads from `f.attrs.tactus_heartbeats` and populates one theorem. Exec fns (`tactus_auto`): `ObligationEmitter::heartbeats` is set at construction from `fn_sst.x.attrs.tactus_heartbeats`; every emitted theorem inherits it via `self.heartbeats`.

**Default.** Prelude's `set_option maxHeartbeats 800000` applies globally when the attribute is absent. Pinned by `test_proof_heartbeats_attribute`, `test_exec_heartbeats_attribute`, `test_exec_heartbeats_multi_theorem` (loop fn — confirms every per-obligation theorem inherits the override), `test_heartbeats_zero_rejected` (negative — non-positive values rejected at parse via `get_heartbeats_arg`), plus unit tests `theorem_with_heartbeats_emits_set_option` / `theorem_without_heartbeats_no_set_option` for pp invariants.

**Z3-path interaction.** The attribute lives on `FunctionAttrsX` and is set for any fn that has it, but is only *read* by Tactus's emission paths (`to_lean_fn::proof_fn_to_ast` for proof fns, `ObligationEmitter` for exec fns). For fns that go through Verus's Z3 path (no `tactus_auto`, no proof-fn tactic body), the attribute is a noop — Z3 uses its own `rlimit` knob, not Lean's heartbeats. The two can coexist; users can write both `#[verifier::rlimit(...)]` and `#[verifier::heartbeats(...)]` on a single fn if they want different effective limits depending on which verifier processes it.

**Malformed invocations.** `get_heartbeats_arg` in `rust_verify::attributes` mirrors `get_rlimit_arg`'s shape — broadly matches `name == "heartbeats"` then validates the argument shape in one place. `heartbeats(0)`, `heartbeats()`, `heartbeats(1.5)`, `heartbeats(1, 2)`, `heartbeats("foo")` all error with `"heartbeats requires a positive integer literal (e.g., #[verifier::heartbeats(1600000)])"` rather than falling through to the generic "unrecognized verifier attribute" catch-all.

The other two items grouped under #123 — **per-module `.lean` file generation** (currently per-fn — fine at our scale) and **CI matrix** (multi-Lean-version testing — not yet wired) — remain as separate future work.

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

**Trade-off: USize subtraction truncates silently.** Because `USize` → `Nat`, `let r: usize = x - y;` for usize `x`, `y` truncates at zero if `y > x`. The `0 ≤` side of the `usize_hi` refinement is then trivially true and the underflow silently passes. Parallel to the u8-subtraction soundness hole before the u8 → Int change. Proper fix is the same: find a way to make USize render as Int without breaking const-generics. Open. **Note**: `DESIGN-cast-hygiene.md`'s Options B and C both close this gap as a side effect — rendering `nat` as Int eliminates the const-generic-body mismatch that currently blocks USize → Int.

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
    Deeper field paths LANDED via #144 — `extract_mut_target` peels
    multiple `Field` levels (`MutTargetRaw::Field { field_oprs:
    Vec<&FieldOpr> }`); rebind builds nested structure-updates inside-
    out (`let a := { a with b := { a.b with c := <fresh> } }`).
    Single-variant gate applied at each level. Tuple field mutation
    (`&mut t.0`) LANDED via #145 + #146 — Lean's structure-update
    syntax doesn't compose with `Prod`, so the rebind uses Lean tuple
    syntax `(t.1, fresh)` (sugar for `Prod.mk`) via a new
    `MutTargetRaw::TupleField` variant + `ExprNode::Tuple` AST node.
    `tuple_field_accessor` helper produces the correct multi-segment
    Lean accessor for arity > 2 (`.2.1` etc., since Lean N-tuples are
    right-nested `Prod`). (The `TupleField` variant was later retired
    in `73d1dd6` — folded into `MutTargetRaw::Field { field_oprs }`
    with per-step `Dt::Path`/`Dt::Tuple` dispatch — so mixed paths
    `&mut s.tup.0` / `&mut t.0.f` compose through the same rebind
    loop. See "Mixed tuple-and-struct paths" below.) `&mut v[i]`
    (Index L-value) and multi-variant enum field mutation remain
    deferred — different reasons (see "Edge cases observed but not
    yet handled" below).
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

    **Still deferred** (post-#144 / #145 / #146):
    * `&mut v[i]` (Index L-value) — cross-crate-trait-emission-
      blocked (NOT spec-inlining-blocked, NOT rebind-shape-blocked).
      In legacy mode, Verus rejects `&mut v[i]` outright with "index
      for &mut not supported"; only `new-mut-ref` mode supports it
      (`rust_to_vir_expr.rs:3140-3267` gated on `bctx.new_mut_ref`).
      Under new-mut-ref, Rust's `&mut v[i]` desugars to
      `vec_index_mut(&mut v, i)` — the `&mut` arg is Var-shaped
      (`&mut v`), so the existing `MutTargetRaw::Var` path handles
      it; no new variant or rebind encoding needed. `vec_index_mut`'s
      spec IS cross-crate-inlined (probe 2026-05-17 saw
      `seq.Seq.update` in the goal), so the obligation reaches Lean.
      Two real blockers prevent verification today: (A) cross-crate
      `View` trait+instance emission is malformed — standalone
      `view.view` axiom collides with `view.View.view` class method,
      duplicate body-less instances, mixed reference forms in goals;
      (B) pre/post substitution bug aliases `final(vec)` with
      `old(vec)` in one position (generates `view post = update
      (view post) ...` where the second `post` should be `v`). Both
      are sub-tasks of #122, not #106. Pinned by
      `test_exec_call_mut_arg_vec_index_probe`.
    * Multi-variant enum field mutation — upstream-blocked at Verus's
      mode check. Verus rejects `ref mut` patterns: "The verifier
      does not yet support the following Rust feature: &mut types,
      except in special cases." Direct `&mut foo.f` for enum-typed
      `foo` isn't expressible in Rust without unsafe; Verus's only
      viable shape (pattern binding `if let Foo::A { ref mut val }`)
      is rejected upstream. Pinned by
      `test_exec_call_mut_arg_enum_field_upstream_blocked`.
    `&mut x.f` for single-variant structs LANDED via #87; deeper
    paths `&mut a.b.c` LANDED via #144; tuple field mutation
    `&mut t.<i>` LANDED via #145 (arity-2) + #146 (arity > 2);
    mixed paths `&mut s.tup.0` (struct-then-tuple) and `&mut t.0.f`
    (tuple-then-struct) LANDED via `73d1dd6` (2026-05-11) — the
    `TupleField` variant was retired in favour of a unified
    `MutTargetRaw::Field { field_oprs: Vec<&FieldOpr> }` whose
    rebind loop dispatches per step on `FieldOpr.datatype`
    (`Dt::Path` → structure update, `Dt::Tuple` → tuple ctor).
    Pinned by `test_exec_call_mut_arg_struct_then_tuple`,
    `_tuple_then_struct`, `_mixed_path_siblings_preserved`.
    None of the landed cases need havoc-base + assume-other-fields-
    unchanged — Lean's structure-update / tuple syntax IS "all
    other fields unchanged" structurally.

    **New-mut-ref mode `MutRefCurrent` / `MutRefFuture`** —
    callee-side LANDED via #95 (pre-rewrite normalization step that
    maps new-mut-ref SST shapes back to the legacy shape so #94's
    existing rewrite handles them). **Caller-side LANDED via #107**:
    synthetic `LocalDeclKind::BorrowMut` locals (Verus introduces
    these around `bump(&mut y)` lowering: `let mut_ref: MutRef<u8>;
    assume(MutRefCurrent(mut_ref) == y); bump(mut_ref); y =
    MutRefFuture(mut_ref);`) are now folded into `mut_param_names`
    so the existing #95 normalization handles them; new
    `build_borrow_mut_binders` emits a theorem-level binder per
    BorrowMut local; `extract_mut_target` recognizes bare
    `Var(borrow_mut_local)` (no surrounding `Loc`) as a Var L-value;
    `is_mut_ref_par`-equivalent check in `build_call_mut_args`
    covers both legacy `is_mut: true` and new-mut-ref `MutRef<T>`
    typ. Pinned by `test_exec_call_mut_arg_new_mut_ref` /
    `_two_mut_args_new_mut_ref` / `_use_after`. Negative test for
    wrong-post-call assertion couldn't be pinned — the test
    framework reports `Err expected, got Ok` but no test_inputs
    dir is created, suggesting Verus's new-mut-ref pipeline
    swallows the error rather than surfacing it. Worth a future
    investigation; positive coverage is solid.
* **Non-int decreases** — datatype-typed decreases via emitted
  `T.height` companion fn (see #54 in Tier 2). Int decreases work
  via the transparent-identity `height` for ints.

### U → Nat coercion at Call sites (BUG-as-nat-cast.md, LANDED 2026-05-15)

Verus's `fn_call_to_vir.rs` cast lowering drops `U(_) → Nat` and `USize → Nat` casts as no-ops. This is sound for Z3 (which treats u_N and `nat` as `Int` with refinements) but unsound for Lean: Tactus renders `u_N` as Lean `Int` and `nat` as Lean `Nat`, so `f(i as nat)` for `i : u64` was lowering to `f i` where `i : Int` — fails Lean's type check.

**Fix**: Tactus-side normalization pass `insert_nat_coercions_in_{exp,stm,expr}` runs at fn entry. At each `Call` node, looks up the callee in `fn_map`; for any arg whose Verus type renders as Lean `Int` but whose callee param type renders as Lean `Nat`, wraps the arg in a synthetic `UnaryOp::Clip { range: Nat }` node. The renderer's existing Clip handler (`clip_to_node_checked` in `to_lean_sst_expr.rs`) then emits `Int.toNat` correctly.

**`needs_nat_coercion` predicate.** Peels transparent wrappers (`Boxed`, `Decorate`) via `peel_typ_wrappers` to match what `typ_to_expr` does at rendering time. Then checks `renders_as_lean_int(arg_range) && !renders_as_lean_int(param_range)`. The wrapper peel matters: SST args often arrive as `Boxed(Int(U(64)))` from Verus's poly encoding pass, and skipping the peel would miss them — surfaced by `test_exec_assert_u64_as_nat` during initial implementation.

**Why a pre-pass, not a Verus-side change.** Always-emitting Clip at fn_call_to_vir.rs breaks 7 vstd lemmas in `vstd/bits.rs` (the bit-shift macros: `lemma_*_shr_is_div`, `lemma_*_shl_is_mul`). Their calc-style proofs rely on Z3 silently equating `x` and `clip(Nat, x)` for u-typed `x`; adding Clip globally changes Z3's view enough to break the proof shape. The pre-pass runs only on Tactus-bound code, so Verus's Z3 path stays untouched and vstd continues to verify 1530/0.

**Sites the pre-pass fires at**:
* `exec_fn_theorems_to_ast`: body via `insert_nat_coercions_in_stm`; ens_exps and reqs via `insert_nat_coercions_in_exp` (inside `WpCtx::new` and `build_req_binders`).
* `proof_fn_to_ast`: require / ensure / decrease clauses via `insert_nat_coercions_in_expr` (VIR-AST level).
* `spec_fn_to_ast`: body + termination_by via `insert_nat_coercions_in_expr`. A spec fn may call another spec fn whose params are nat-typed.

**Pattern symmetry.** This is the fourth Tactus-side normalization (sibling to #94 `rewrite_varat_for_mut_params`, #95 `normalize_mut_ref`, and #127's `original_cond` recovery in `build_wp_loop`). The recurring shape: *Verus's pipeline produces an output that's right for SMT but wrong for Lean; Tactus runs a normalization pass at fn entry to fix it.* Listed under "Potential future infrastructure → RewritePipeline" as a candidate for typed-pipeline refactoring.

**Cross-crate callees** aren't in `fn_map`; they fall through unchanged. This matches existing cross-crate behavior (`build_wp_call`'s `pick_spec_source` rejects cross-crate trait method decls; the same call path also fails the coercion fix). Cross-crate spec fn inlining (#122 Phase 3) would need to extend `fn_map` to cover these.

**Pinned tests**: `test_proof_fn_u64_as_nat_in_ensures` (minimal reproducer from bug doc, VIR-AST path); `test_proof_fn_u_types_as_nat` (u8/u16/u32/u128 all coerce); `test_proof_fn_both_sides_as_nat` (both sides of `==`); `test_exec_assert_u64_as_nat` (SST path via exec assert); `test_exec_loop_invariant_u64_as_nat` (loop invariant via SST visitor).

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

*Audited 2026-05-11 (#153) — keep.* The substitution doesn't add reasoning — it eliminates a redundant quantifier. `∀ ret. (ret = E) ∧ Q(ret) → P(ret)` ↔ `Q(E) → P(E)` is exact logical equivalence: the antecedent has only one satisfying `ret`, so substituting E for ret loses no information. Same logical content rendered differently, like writing `a` instead of `if true then a else b`.

The transformation IS visible in output: user reads `let dest := E; ...` in the generated `.lean` and sees exactly what was substituted. The 4 pinned tests cover the substitution path; the conservative fallback (no `r == E` → ∀-path stays) is also tested. Bound preservation matches the ∀-path — omega sees the same factual content either way.

What the restructure buys: cond_setup goals (function-call-in-loop-cond from #114) close under `tactus_auto`'s default closer without user override. Pre-#128 users had to write `#[verifier::tactus_tactic("intros; simp_all; omega")]` to handle the ∀-Prop shape; post-#128 the substitution path avoids the quantifier and `omega` handles the rest natively.

Same audit verdict as #150 / #152: substrate-class restructuring, visible in output, downstream-justified. Not hiding work; just rendering the same obligation in the form the default closer can handle.

### Known deferrals, rejected cases, and untested edges

A flat catalogue of things that don't work yet, organized by where in the pipeline they're rejected or where the gap lives. If a gap has its own detailed section elsewhere in this doc, it's cross-referenced rather than duplicated.

#### Statement-level forms rejected by `build_wp`

Each one returns `Err("… not yet supported")`; users get a clean rejection instead of silent pass.

* **`StmX::BreakOrContinue`** — `break` / `continue` inside loops. Blocks `while`-with-exit patterns. Enabling this also requires relaxing `cond: Some` (loops that break compile to `cond: None`) and accepting `invariant_except_break` invariants (at-entry but not at-exit).
* **`StmX::AssertBitVector` — LANDED via #111 + #130.** `assert(...) by(bit_vector) requires P; ensures Q;` routes through `Wp::AssertBitVector { req_conj, ens_conj, rust_loc, body }`. The walker renders the goal in BitVec mode (`Var(x : U(n))` → `BitVec.ofInt n x`) and emits one theorem with goal `req_conj → ens_conj` (collapsed to bare `ens_conj` when requires is empty), discharged by `tactus_bit_vector` whose first rung is Lean core's `bv_decide` — full SAT-backed bit-vector decision procedure, handles XOR/AND/OR/shifts on free or parameterized BitVec terms uniformly. Files using `by(bit_vector)` conditionally import `Mathlib.Data.BitVec` and `Lean.Elab.Tactic.BVDecide` plus `HXor`/`HAnd`/`HOr`/`HShiftLeft`/`HShiftRight` Int instances (Verus's ast_to_sst pre-injects an Int-mode `Assume(ens)` before the AssertBitVector; without instances, the post-assert continuation theorems would fail to typecheck). Surrounding ctx hyps are dropped via `obl.wrap_no_hyps` so the bit_vector goal stays clean. Body's ctx doesn't get the ensures published as a hyp — Verus's pre-injected Assume already does that. Pinned by `test_exec_assert_bit_vector_concrete` / `_xor_comm` / `_xor_self` / `_xor_assoc` / `_and_or_comm` (positive) and `_false` (negative).
* **`StmX::AssertQuery`** — `assert by(…)` with specific query modes. Three modes exist; their dispositions differ:
  - `AssertQueryMode::Tactus { tactic_span, kind }` — LANDED via #49 / #50. Routes to `Wp::AssertByTactus`.
  - `AssertQueryMode::NonLinear` — LANDED. Lowers to `Wp::AssertQuery { primary: nlinarith, preamble: [Mathlib.Tactic.Linarith], body, after }` carrying just the mode-specific tactic. The walker composes the full closer at scope-entry time: `first | (intros; primary) | (<outer_closer>) | fail "<scope msg>"`. The `<outer_closer>` reads `obl.closer` so fn-level `#[verifier::tactus_tactic(...)]` overrides propagate, and nested AssertQuery scopes compose recursively. The trailing `fail` overrides Lean's last-failure-wins reporting so users see "by(nonlinear_arith) scope: could not close — add an explicit `proof { … }` block" instead of `tactus_auto`'s misdirected fallback message. `obl.new_scope(closer, preamble)` installs the composed closer + preamble and drops enclosing-scope Hyps (matching Verus's NonLinear query semantics — only requires + typ invariants are in scope). Every theorem the body's recursive walk emits picks them up. Generic over `primary` — future query modes (Polyrith etc.) would reuse `Wp::AssertQuery` with a different tactic. (Important: any such future mode is **upstream-blocked**, not Tactus homework. Verus's `AssertQueryMode` enum has three variants today — `Tactus`, `NonLinear`, `BitVector` — and Verus's parser only accepts the corresponding surface syntaxes. Adding a `by(polyrith)` form would require a Verus-side change to the enum + parser; the Tactus side is then ~10 lines: a new `build_wp` match arm constructing a `Wp::AssertQuery` with the new mode's `primary` / `preamble` / `surface_label`.) Pinned by `test_exec_assert_nonlinear_commutative`, `_with_requires`, `_with_proof_block`, `_scope_resets`, `_inside_loop`, `_nested_scopes`, `_wrong` (negative, also pins the scope-named failure message). Shape-drift guards: `ast_to_sst_emits_assume_assert_for_nonlinear_body` (Verus's body shape) + `nonlinear_preamble_fragments_shape_pinned` (Mathlib import path).
  - `AssertQueryMode::BitVector` — defensive arm. Verus's `ast_to_sst` (vir/src/ast_to_sst.rs:2416) converts user-syntax `assert by(bit_vector)` directly into `StmX::AssertBitVector` upstream, so this arm is structurally unreachable. The `StmX::AssertBitVector` path (above) supersedes it. Hitting the rejection would mean an upstream pipeline change worth investigating.
* **`StmX::DeadEnd`** — markers Verus uses for unreachable code. Usually harmless to skip, but we reject rather than silently strip in case a future pipeline relies on them.
* **`StmX::OpenInvariant`** — atomic invariant opening for concurrent verification. Reframed 2026-05-12 from "concurrency-blocked" to "cross-crate-blocked": Verus's `ast_to_sst` already prepares the verification block (`let inner = arb; assume(inv.inv(inner)); body; assert(inv.inv(inner))`) before wrapping in `StmX::OpenInvariant(stm)`. The marker itself signals "no unwinding" (which Tactus doesn't model anyway) plus namespace tracking for nested opens. The actual blocker for exec-mode usage is that the inner block references vstd-side spec fns (`AtomicInvariant::inv`, `LocalInvariant::inv`, `Inv::namespace()`) plus the `InternalFun::OpenInvariantMask` lowering, all of which require Phase-3-style cross-crate spec fn availability (#122). Once cross-crate spec inlining lands for vstd specifically, OpenInvariant should fall out as a near-trivial walker arm: `StmX::OpenInvariant(inner) => build_wp(inner, after, ctx, loop_stack)` — the inner SST is already shaped for verification. Currently kept as Err with the original rejection message.
* **`StmX::ClosureInner`** — LANDED (#93). The `StmX::ClosureInner` variant gained a `ast_body: Expr` field populated by `ast_to_sst` (see `vir/src/sst.rs`), and Tactus reads it to render the closure as a first-class Lean lambda. The closure body's own verification scope (overflow checks etc.) emits as a separate set of theorems via `Wp::ClosureBody`'s walker, which pushes `∀ p : T, h_p_bound → ...` binders for each closure param. Pinned by `test_exec_closure_decl`, `test_exec_closure_decl_wrong_ensures`, `test_exec_closure_body_overflow_caught` (negative — soundness probe), `test_exec_closure_body_safe_arithmetic`.

#### Expression-level forms rejected by `sst_exp_to_ast_checked`

`sst_exp_to_ast_checked` is the primary validator+renderer for SST expressions; `check_exp` is a thin wrapper (`.map(|_| ())`). Single case analysis for both validation and rendering.

* **`UnaryOp` variants beyond `Not` / `Clip` / `CoerceMode` / `Trigger`** — the spec-fn path (`to_lean_expr`) handles more (BitNot, IntToReal, etc.) but the SST path on exec bodies is conservative; add as needed.
* **`BinaryOp::HeightCompare { … }`** — VIR's termination-height comparison (the fn-level wrapper; `CheckDecreaseHeight` below is the per-call-site SST form we DO lower).
* **`BinaryOp::Index(_, _)`** — LANDED (#91 closed). SST guarantees `BoundsCheck::Allow` (the bounds obligation is discharged by Verus's mode pass before SST). Tactus emits `lhs[Int.toNat rhs]!` (Lean's `getElem!`-based indexing — total in the type system, panics out-of-bounds; observationally fine because Tactus only verifies the goal and never executes the generated Lean). Requires `[Inhabited α]` for the element type, which holds for primitives and for non-generic user datatypes (we already emit `deriving Inhabited`). Side-effect fix: `Primitive::Array` type rendering drops the const-length argument (Lean's `Array α` is unary). Reachable from spec-mode `array_index(a, i)` (Verus builtin) and from exec-mode `a[i]` after Verus's bounds-check pass lowers `PlaceX::Index(_, _, _, BoundsCheck::Allow)` to `BinaryOp::Index(_, BoundsCheck::Allow)`. **Caveat**: exec-mode `a[i]` for slices/arrays in Rust desugars to `vstd::array::array_index_get` / `vstd::slice::slice_index_get`, which Tactus can't yet inline (cross-crate); user code that wants exec-mode array access through `tactus_auto` either needs vstd routing or a synthetic same-crate exec wrapper.
* **`BinaryOp::StrGetChar` — LANDED via #113** (2026-05-11). Verus's `verus_builtin::strslice_get_char(s, i)` (surface syntax) now lowers cleanly through both the VIR-AST and SST renderers. Both paths share `non_binop_head(StrGetChar)` which routes to `Tactus.strGetChar`, a `def` in `TactusPrelude.lean` with signature `String → Int → Nat`. Implementation: `Tactus.strGetChar s i = (s.data[i.toNat]!).toNat` — `s.data : List Char` is the underlying codepoint list, `[i.toNat]!` is the panic-on-OOB `GetElem!` indexer, `.toNat` unwraps the `Char` to an integer codepoint. The naive head `String.get` (which the prior `non_binop_head` table emitted) was *wrong* — Lean's `String.get` takes a `String.Pos` (byte offset) and returns Lean's `Char`, whereas Verus's semantics is codepoint-indexed and the return type is Tactus's `Nat`. Out-of-bounds panic is observationally fine (Tactus verifies, never executes). Pinned by `test_proof_strslice_get_char` (VIR-AST path via proof fn), `test_exec_strslice_get_char_in_assert` (SST body-level path via exec-fn assert), `test_exec_strslice_get_char_in_ensures` (SST `ens_exps` path via exec-fn ensures).
* **`BinaryOp::IeeeFloat(_)`** — IEEE float comparisons. Verus doesn't support `f32`/`f64` at all; this branch exists for completeness.
* **`ExpX::Ctor(..)`** — LANDED. Renders via the shared `ctor_node` helper (`to_lean_sst_expr.rs:793`), so exec bodies can construct structs and enums (`Point { x: 1, y: 2 }`, `Wrap::V(x)`, etc.). The required datatype declarations are brought into the Lean preamble by `dep_order::walk_expr`'s `ExprX::Ctor` case. Pinned by `test_exec_ctor_struct_in_body` and `test_exec_ctor_enum_in_body`. (An earlier draft of this catalogue listed it as rejected with a `test_exec_ctor_rejected` regression test — both the claim and the test were stale; the catalogue is now corrected.)
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
* **`BinaryOp::Xor`** — renders via the shared `non_binop_head(Xor) -> "Bool.xor"`. Pinned at three levels: `test_exec_xor_bool` (fn-return-equals-body smoke), `test_exec_xor_bool_concrete` (concrete `(true ^ false) == true` closes via `decide`), `test_exec_xor_bool_free_vars_commutative` (commutativity on free bool vars — closed by user-explicit `assert(...) by { simp_all [Bool.xor_comm] };`, NOT by extending `tactus_auto`'s set). The commutativity goal shape on free vars is `(decide b1 ^^ decide b2) = (decide b2 ^^ decide b1)` because Tactus renders `TypX::Bool` as `Prop` unconditionally (see § "Bool vs Prop"). Per the design choice documented there, this kind of Bool-operation gap is closed *transparently* at the assertion site — the lemma being used is right where the user reads it.
* **`ExpX::Bind(BndX::Choose, ...)` → `Classical.epsilon (fun ... => cond ∧ body)`.** Pinned by `test_exec_choose_in_spec` — Choose inside a spec fn called from an exec fn's ensures. `Classical.epsilon` is total but its behaviour on unsatisfiable `cond` is unspecified; the test uses an ensures-disjunction that doesn't depend on the witness being defined. Direct exec-mode `choose|x| P` outside spec fns isn't exercised but goes through the same renderer arm.
* **`StmX::AssertCompute(_, e, ComputeMode)`** — Tactus dispatches identically to `StmX::Assert`, dropping the `ComputeMode` (`Z3` vs `ComputeOnly`). The mode is a Verus-side performance hint telling Z3 to discharge `e` via `interp` evaluation rather than full SMT — no direct Lean analog, but `tactus_auto`'s ladder includes `decide` (which IS the Lean equivalent of "compute the value structurally"), so the user-facing behaviour aligns even though the explicit mode tag is lost. `assert(P) by(compute)` and `assert(P) by(compute_only)` from user source aren't tested in tactus_auto fns; if a future test exercises a ComputeMode-shaped assertion that `decide` can't close, the ladder might need a `norm_num` / `simp_arith` rung.
* **`lift_if_value` chain-lifts through multi-binder `Bind(Let)` (#119).** Multi-binder lets (`let (a, b) = expr; …`) unfold to a single-binder chain via `unfold_multi_binder_let` (#92), and `lift_if_value` recurses through the chain when each binder's `inner_body` is itself a `Bind(Let, …)` — lifting any if-in-rhs along the way. The recursion is gated on `inner_is_let_chain` for soundness: when `inner_body` is `If` at top level (e.g., the match-compilation shape `let _disc := proj(k); if _disc = 0 then …`), lifting would move the if's condition outside the let scope and produce an unbound reference. The case-split tactic handles those match-style ifs at the obligation level instead.

#### Loop-shape restrictions (rejected by `build_wp_loop`)

* **`loop_isolation: false` — LANDED via #127 (2026-05-11).** Verus's `ast_to_sst` lowers `while c { body }` with isolation=false to break-lowered form (`loop { if !c { break; } body }`, cond:None) because AIR encodes this via the `Breakable` control-flow primitive — the natural-exit fact (`¬c` post-loop) is carried by AIR's state-preservation across `Break`, not by an SMT predicate. Lean's kernel has no equivalent primitive (it's pure type theory; no control-flow constructs that preserve state across control jumps), so we can't mirror AIR's encoding directly.

  **Solution: upstream-field recovery, not pattern-detect.** Added `StmX::Loop.original_cond: Option<(Stm, Exp)>` to upstream SST. `ast_to_sst`'s break-lowering populates it with the pre-conversion `(cond_setup, cond_exp)` at the same site it sets `cond` to None. AIR's `sst_to_air` ignores the field (binds `original_cond: _` in its destructure — per the upstream-robustness pattern). Tactus's `build_wp_loop` reads it: when `cond` is None but `original_cond` is Some AND soundness gates pass, treat the loop as cond:Some(original_cond). The existing cond:Some encoding then handles the rest — body obligations get `c` as a hyp under maintain_obl (the inserted `if !c { break; }` becomes a vacuous branch under contradictory `c ∧ ¬c` and discharges trivially), and use_obl gets `¬c` as the natural-exit fact.

  **Soundness gate (single-break check)**: Verus's lowering inserts exactly one break (the if-not-c-break). If the user's body has its OWN break(s), Verus preserves them alongside the inserted one — there are now multiple exit paths, and user breaks may fire when `c` is still true, so post-loop's `¬c` is not universally true. `count_breaks_targeting_this_loop` walks the body counting `BreakOrContinue { is_break: true }` that target this loop (unlabeled breaks inside nested loops target the nested loop, not this one; labeled breaks check the label). When count > 1, we refuse the recovery and fall through to cond:None encoding. User must encode post-loop facts via `allow_complex_invariants` + loop `ensures` (or rely on what invariants alone give).

  **Additional gates**: only fire recovery for unlabeled loops (`label.is_none()` — labeled loops would need cross-label break counting that's deferred), and only when `original_cond`'s cond_setup is empty (non-empty setup with calls/short-circuits would need scoping work for the cond's temp bindings to be in scope at maintain ctx).

  **Why upstream-field, not pattern-detect**: pattern-matching `if !c { break; }` at body[0..1] would be fragile — if Verus's lowering rearranges (extra wrappers, different positioning), detection misses silently and users see a UX regression. The upstream field is the *direct read* of information Verus already has at conversion time; no inference, no shape-drift to maintain. The field is also informational (AIR doesn't read it), so adding it doesn't risk changing AIR-side behavior — only enables Tactus's read.

  **What didn't have to mirror Verus's encoding** (this section's general theme): Verus's break-lowering exists because AIR/Z3 need that shape. Tactus has Lean, not AIR. Once we preserve the pre-lowering cond, Tactus's cond:Some encoding gives Lean-native natural-exit semantics without re-encoding AIR's Breakable as a predicate. Same family as #87's structure-update for `&mut x.f` (Lean's structural-update syntax replaces havoc-base+other-fields-unchanged), #93's first-class lambdas for closures (Lean function types replace axiomatized ClosureReq/Ens), and #128's ret-substitution at call sites (definitional `let` replaces ∀-with-equality glue).

  **Pinned by**: `test_exec_loop_isolation_false_fn_level` / `_loop_level` (basic acceptance), `_natural_exit` (the post-loop `i == n` case — the canonical motivation), `_outer_ctx` (outer fn precondition flows into body+after), `_user_break_falls_through` (soundness gate — multi-break loop still verifies under cond:None encoding without unsoundly assuming `¬c`), `_invariant_violation` (negative — invariant maintain obligation still fires).
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

* **Historical: new-mut-ref False-hypothesis silent miscompile (CLOSED 2026-05-26).** Prior to the BorrowMut elimination pre-pass, Tactus's caller-side new-mut-ref encoding had a soundness bug: in the inlined ensures of a callee taking `&mut` args, BOTH `*y` (post-state) AND `*old(y)` (pre-state) substituted to the SAME post-state existential. The substituted hypothesis became `post.deref = post.deref + 1` — vacuously False as an antecedent — making the surrounding implication `(False) → goal` trivially True regardless of goal. A wrong ensures like `*y == *old(y) + 999` would have "verified" via this False-hyp path. Four tests were passing this way: `test_exec_call_mut_arg_new_mut_ref`, `_use_after`, `test_exec_call_two_mut_args_new_mut_ref`, `test_new_mut_ref_pre_post_substitution_probe`. The principled fix — BorrowMut elimination — closes the bug at the architectural level (the encoding no longer has the indirection that masks pre/post distinction). Caught during the 2026-05-26 review pass when the principled fix made the False-hyp shape stand out: pre-fix `_tactus_mut_post_1.deref = _tactus_mut_post_1.deref + 1`; post-fix `_tactus_mut_post_1.deref = pre_state_value + 1`. The audit-via-architectural-improvement pattern.

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

  Audited 2026-05-11 (#149). The audit lens: *what makes a proof go through that the user can't see?* For `tactus_case_split`, the structural answer is: this isn't really automation — it's the proof-level counterpart to the user's source-level match/recursive structure. When a user writes `match k { ... }` or a recursive `fn count(s: Stack)`, they're implicitly asking for case analysis on `k` / `s`; the tactic just makes it explicit at the proof level. Tactic name visible in generated `.lean` (already more visible than Verus's Z3 path which subsumes case-splitting into the solver's heuristics with zero user-facing signal). Audit decided: **keep in the default closer**. The opacity-of-choice in multi-candidate scope is real but no current test exercises a case where the choice MATTERS (today all multi-datatype locals have the case-split close on one specific candidate).

  **User-explicit alternative — per-arm proof via `cases ... with`.** When the user wants the case reasoning at the proof level rather than via the closer, Lean's native `cases ... with | Foo x => tac | Bar y => tac` syntax goes through `proof { }` verbatim (FileLoader passes tactic text through). Each arm's tactic discharges only that arm's subgoal — the inline-per-case proof shape. Pinned by `test_exec_match_enum_with_per_arm_proof`. Usage:
  ```rust
  #[verifier::tactus_auto]
  fn kind_value(k: Kind) -> (r: u8) ensures r <= 100 {
      proof {
          cases k with
          | Foo x => simp_all; split <;> omega
          | Bar y => simp_all; split <;> omega
      }
      match k {
          Kind::Foo(x) => if x <= 100 { x } else { 0 },
          Kind::Bar(y) => if y <= 100 { y } else { 0 },
      }
  }
  ```
  Use this shape when: (a) different arms need different tactics (e.g., one needs `simp_all`, another needs `omega [some_lemma]`), or (b) you want the per-case reasoning visible at the proof level rather than hidden in the closer.
* **`HXor`/`HAnd`/`HOr`/`HShiftLeft`/`HShiftRight Int Int Int` instances are wonky-but-total for negative Ints (#130).** Defined via `Int.toNat` (which returns 0 for negative Ints), so `(-1 : Int) ^^^ x = (0 ^^^ x.toNat : Nat)` rather than the bitwise XOR of the two's-complement representations. Tactus only emits these operators on values it has bounded as non-negative (u-typed Ints with `0 ≤ x` hypotheses), so the wonky path is unreachable from emitted code. The instances are conditionally injected only into files using `assert(P) by(bit_vector)` (#130), so unrelated proof fns aren't exposed to the wonky semantics either. If a future Tactus path emits these on negative Ints, the wrong values would silently pass typecheck — file the issue and either tighten the rendering or define the instances via two's-complement BitVec semantics.

#### User-facing features not tested (or possibly broken)

* **`proof { … }` blocks inside exec fns — LANDED (#49).** Covered by `test_exec_proof_block_user_tactic`. Caveats: tactic runs at theorem level (see Soundness trade-offs); goal-modifying tactics affect the whole goal.
* **`assert(P) by { tactics }` — LANDED (#50).** Covered by `test_exec_assert_by_user_tactic`.
* **`assume(P)` warnings — LANDED.** `collect_assume_sites` (`sst_to_lean.rs:789`) walks the AST collecting user-written `assume(P)` spans and `generate::check_exec_fn` (line 312) emits an "unproved assumption" warning per site. The AST-walk avoids false positives on synthetic `StmX::Assume` injections from later passes (overflow checks, call-ensures, resolution-tracking). Pinned by `test_exec_assume_warning`. (An earlier draft of this catalogue claimed the warning was not wired — that was stale.)
* **Return in the `else` branch of an if** (where `then` falls through) — ✅ covered by `test_exec_return_in_else_branch` (#121 partial).
* **Return inside a loop body** — ✅ covered by `test_exec_return_inside_loop` and `test_exec_return_inside_loop_with_break`. Pins the Wp DSL's fn-exit semantics (Return writes `ctx.ensures_goal` regardless of nesting or `loop_ctx`).
* **Loops modifying multiple variables** — ✅ covered by `test_exec_loop_three_modified_vars` (#121 partial). `quantify_mod_vars` handles arbitrary-arity modified sets; tested with 3 modified vars.
* **Nested if where each branch contains a different loop** — ✅ covered by `test_exec_nested_if_with_loops_in_both_branches` (#121 partial). Pins that distinct loop ctxs in distinct branches walk independently.
* **Loop body ending in an early return** — ✅ covered by `test_exec_return_inside_loop_with_break`.
* **Bit-width coverage** — ✅ covered end-to-end via #76 (`test_exec_u16_add` / `_u64_add` / `_u128_add` / `_i16_add` / `_i32_add` / `_i64_add` / `_i128_add` plus matching `_overflow_fails` negatives).
* **Direct unit tests for `walk_loop` and `walk_call`** — ✅ covered via #126 (`wpctx_new_*`, `walk_loop_skips_init_for_ensures_kind_invariant`, `walk_loop_emits_init_for_at_entry_invariant`, etc.). The two largest walker functions now have direct unit tests in `sst_to_lean::tests` alongside the cheaper-variant coverage.
* **Name collision: callee's ret name vs caller-scope names** — ✅ pinned by `test_exec_call_ret_name_collision`. `walk_call` gensyms the ∀-bound ret to `_tactus_ret_<id>` rather than reusing the callee's source ret name, then substitutes the source name in the inlined ensures — so caller-side locals named identically are unaffected. Surfaced as a real shadowing bug during #78; fixed and pinned.
* **Zero-arg callee spec referencing the dummy param** — for a fn with no user params, Verus injects a `no%param` dummy; our `walk_call` substitutes `{no_param: Const(0)}`. If the callee's `require` / `ensure` ever syntactically references this dummy (they shouldn't, by Verus convention), we'd inline `0` for it — semantically correct but relies on the convention holding.
* **Non-constant `IntegerTypeBound` bit width** — `const_u32_from_sst` / `_vir` extract the bit width via `.expect("…non-constant bit width…")`. Verus's `IntegerTypeBound(kind, bits)` always has `bits` as a literal for concrete int types, but a const-generic context (`<const N: u32>` as bit width) would panic at codegen. Untested.
* **Empty `proof { }` / `assert(P) by { }` brace bodies** — ✅ pinned by `test_exec_proof_block_empty` and `test_exec_assert_by_empty`. The 2026-04-26 right-way pass (P0 fix) wired `walk_assert_by_tactus` to skip whitespace-only prefix pushes (proof-block path) and fall back to `simple_tactic()` when the user's tactic is whitespace-only (assert-by path), so the obligation still verifies via the default closer.
* **Enum accessor fns for types with non-Inhabited field types** — `datatype_to_cmds` emits accessor bodies using `default` for unreachable match arms (other variants). For field types lacking `[Inhabited α]` (user-defined types without a derived instance), Lean elaboration fails. The `emit_accessors: bool` flag skips accessor synthesis in the proof-fn entry path — spec fns reference such types routinely and use native Lean match, not accessors. For an exec fn matching on an enum with non-Inhabited-field'd variants, we'd emit accessors that fail to elaborate. All current test enums have Int/Nat/Bool fields (auto-Inhabited). Untested for user-defined types.
* **Generic calls don't verify trait-bound / where-clause constraints** — `#53`'s substitution accepts any `typ_args` without checking callee-side bounds. For callees whose body only uses type-level references to the type parameter, this is fine. For callees that rely on bounds for operations (e.g., `T: Ord` enabling `<` on T values), the callee's spec might assume properties we can't guarantee for the instantiation. Current generic exec fn tests are identity-like; no bound-dependent exec callees exercised.
* **`assert forall|v| P by { tac }` via Tactus path — upstream-blocked by Verus poly panic.** The #50 / #49 infrastructure goes through `ExprX::AssertBy` which can carry `vars`. Our Tactus short-circuit handles `vars = []` (plain assert-by and proof blocks). The forall variant with non-empty `vars` panics in Verus's poly encoding pass (`vir/src/poly.rs:462`) — the AssertBy + Ghost wrap doesn't carry the binder information through to where poly expects it. Documented as a comment in `tactus.rs` at the test-skip site (no `Err(_)` check possible against an upstream panic). Workaround: pull the forall into a separate proof fn and `assert` the application.
* **Tactus tactic referencing loop-local variables** — see the "tactic-text prepending runs at theorem level" soundness trade-off. Probed (#121, 2026-05-11) and pinned by `test_exec_assert_by_omega_in_loop_body`: an `assert(P) by { omega }` inside a loop body DOES work for the common case where the tactic name-resolves against bound vars (loop-modified `i` + fn-param `n` both become binders in the maintain theorem). What still doesn't work — and remains untested for lack of an idiomatic shape — is a tactic that references a hypothesis by a *user-controllable name* like `h_inv`. Hyp frames get codegen-internal names, not user-controlled ones; there's no stable way for the user's tactic to refer to an invariant hypothesis directly. Omega/simp_all sidestep this by iterating over the available hypotheses themselves.
* **Generic datatype with uninhabited type param** (#108 edge) — upstream-blocked, pinned by `test_exec_generic_datatype_uninhabited_type_param_upstream_blocked`. The original concern was that `List<Empty>` would fail `Inhabited (List Empty)` synthesis at the call site. Probe established this is structurally unreachable through normal Tactus paths: Verus rejects `enum Empty {}` itself with "datatype must have at least one non-recursive variant," so an uninhabited type never reaches Tactus. The conditional-deriving fix the entry previously named is therefore not currently warranted. If Verus ever lifts the no-empty-enum rule (e.g., adds support for `!` / `Infallible` / explicitly empty enums), the test surfaces as a flippable Err and the Inhabited concern returns; until then, this is a Verus-side restriction, not a Tactus one.
* **Generic datatype with trait-bounded type params** (#108 edge) — ✅ pinned by `test_exec_call_recursive_generic_datatype_trait_bound`. `enum TBox<A: Tag> { Leaf(A), Node(Box<TBox<A>>) }` declares a trait bound; `height_fn_for_datatype` and `multi_variant_accessor_defs` ignore `dt.typ_bounds` — bounds aren't threaded to the generated `T.height` / accessor defs. The structural height path doesn't need the bound (height counts shape, not values), and Lean has no encoding of the user trait `Tag` to ask about, so the bound silently drops. Verus still enforces it on the Rust side (instantiations must satisfy the bound), so callers that try to use it on an unsatisfying type are rejected pre-Tactus. Datatypes where the bound *would* matter at the Lean level (e.g., one where the height fn called a method gated on the bound) remain untested — but that pattern would already need a different mechanism (height is currently always structural by construction).
* **Generic recursive datatype with cross-instantiation recursion — LANDED.** `enum Mut<A> { Plain(A), Recurse(Mut<u8>) }` — the recursive arm has type `Mut<u8>`, not `Mut<A>`. Lean's parameter-style strict-positivity check rejects this (`(kernel) arg #2 of 'Mut.Recurse' contains a non valid occurrence of the datatypes being declared`). Tactus detects cross-instantiation at codegen time via `has_cross_instantiation_recursion` and switches the emission for affected datatypes from parameter-style to indexed-style: `inductive Mut : Type → Type 1 where | Plain : ∀ {A}, A → Mut A | Recurse : ∀ {A}, Mut Int → Mut A`. `deriving Inhabited` doesn't work for indexed-style, so a manual `Inhabited` instance is emitted alongside the inductive (`datatype_inhabited_instance_cmd` picks a non-recursive base variant and applies `default` to each of its fields). Both styles coexist in the same .lean — uniform-recursion datatypes (`List<A>`, `Tree`, etc.) keep the parameter-style + `deriving Inhabited` path. Pinned by `test_exec_call_recursive_generic_datatype_cross_instantiation`.
* **`Pattern::Or` with cross-branch capture in alpha-rename** (#116 edge). For a match arm with `(Var(x) | Ctor(y))` where one alt binds `x` and another `y`, and substitution would capture `x` only on the first alt, our `rename_in_pattern` walks both alternatives uniformly. The Lean spec for `Or`-patterns requires each side to bind the same variable set; a rename that touches one side's binder must touch the other's matching binder too. Our walker handles this correctly because the rename map is shared across the walk, but a degenerate `Or` with truly disjoint bindings (e.g., `(Var(x) | Wildcard)`) followed by a body that references `x` is well-formed Lean only when both alts bind `x`. Realistic Verus output doesn't produce this shape; we'd handle it correctly if it arrived.
* **Multi-line `def` signatures in `TactusPrelude.lean`** (#118 edge) — pinned by `extract_prelude_names_multi_line_def_shapes`. Probe established what actually works and what doesn't: `def name\n  : Type := body` works (name is on the same line as `def`, so line-1 extraction succeeds). `def name {A : Type}\n  [Inhabited A] : T A := body` works (take_while on `name {...` stops at the brace). `def name :=\n  body` works. `noncomputable\ndef name : T := body` works (line 2 falls through to the bare `def NAME` matcher). The single failure mode is bare `def\n` separated from the name (`def\n  name : T := body`) — unidiomatic Lean (no one writes it that way), so a parser robustness pass for it is theoretical-not-urgent. The earlier DESIGN entry's prediction (that `def name\n  : Type := body` would fail) was incorrect; the test pins the actual surface.
* **Stale `LEAN_PATH` after `lake update`** (lake-bypass edge). `cached_lean_path_for_lake_project()` resolves once per test-binary process via `OnceLock`. If the user updates the lake project (adds/removes Mathlib packages) and re-runs tests in the same process, the cached `LEAN_PATH` won't reflect the new packages. Restart the test binary to clear. Documented in the harness's docstring.
* **`lift_if_value` chain-lift only fires for let chains** (#119 edge). When `inner_body` is `Match`, plain `Var`, or any non-`Bind(Let)` shape (other than top-level `If`, which is the rejected unsafe case), `lift_if_value` falls through to render-as-is. Conservative: can miss lift opportunities but never produces a wrong-scoped reference. The chain-lift gate `inner_is_let_chain` is the structural distinguisher.
* **Closures with user-written `requires` / `ensures`** — ✅ pinned by `test_exec_closure_with_requires` (`|x: u8| requires x < 100 { x + 1 }` — body uses the assumed precondition to discharge the overflow check) and `test_exec_closure_with_ensures` (`|x: u8| -> (r: u8) ensures r == x { x }` — body must satisfy the ensures). The catalogue had claimed "we didn't manage to write a clean test" but #121's probe (2026-05-11) found the right surface syntax: `requires` goes between the param list and the body with no `->`, `ensures` requires the `-> (r: T)` return-binding before the `ensures`. The body verification scope from Slice C of #93 processes both correctly via `exec_closure_body_stms`.
* **Datatype SCCs of size > 3** (#109 edge) — ✅ pinned at depths 4, 5, and 10 by `test_exec_four_element_datatype_scc` (A → B → C → D → A), `test_exec_five_element_datatype_scc` (P → Q → R → S → T → P), and `test_exec_ten_element_datatype_scc` (E0 → E1 → ... → E9 → E0). The Tarjan implementation is generic over SCC size; 4+ cycles go through the same `mutual { inductives } end` + accessors-out + `mutual { heights } end` emission path. The 10-cycle test runs in ~6.8s (vs ~5s for 4/5 cycles), so Lean's mutual-block compilation cost at depth 10 is *not* the catalogue's previously-named latent concern. Depths beyond 10 remain unpinned, but the linear progression at 4 → 5 → 10 with near-flat compile time means concern only kicks in at much larger depths if at all.
* **`ScopeKind::Other` positive mis-categorization** (#98 ScopeKind edge). The structural lock makes adding a new `ExprNode` variant a compile error in `walk_children` / `map_children` / `scope_kind`, forcing the contributor to categorize. But they could still *positively* lie — write `ScopeKind::Other` when the new variant introduces a binder. The type system can't catch a wrong-but-explicit choice. Documented in the section header comment for `ExprNode::scope_kind`. Pinned-by-test for the existing variants via `scope_kind_categorizes_each_variant`; future binder variants only get pinned once tested.
* **AssertBitVector with non-trivial SST shapes** (#130 edge) — ✅ pinned by `test_exec_assert_bit_vector_with_fn_call`, fixed via #147 (2026-05-09). Probe surfaced a real codegen panic ("unresolved `id_u8`") and diagnosis revealed two latent bugs: (1) `dep_order::seed_worklist` only walked `require` / `ensure`, never the function body — so spec fn calls inside body-level assertions never reached the preamble dep set. Bug applied to *any* body-level spec fn reference, not just bit_vector; bit_vector triggered it via Verus's pre-injected `Assume(ens)`. (2) `spec_fn_to_ast` reused `fn_binders` (the proof/exec helper that adds `h_<name>_bound` refinement hyps as binders), which gave spec-fn defs the wrong type signature (`Int → Bound → Int` instead of `Int → Int`), breaking call sites that pass only the value. Both fixed: `seed_worklist` now also walks `pf.body`; `spec_fn_to_ast` calls a new `fn_binders_without_bound_hyps` helper. Bound checking for spec-fn params still happens at theorem-call sites where the corresponding hyps exist via `fn_binders` on the calling proof/exec fn. Pinned by `test_exec_assert_bit_vector_with_fn_call` (bit_vector path) and `test_exec_plain_assert_with_spec_call` (plain assert path) — same fix surface, two shapes.
* **Proof-fn trait methods — ✅ LANDED 2026-05-15** (mode-dispatch in
  `trait_to_ast`). Proof-fn trait methods render as Prop-typed class
  fields (Mathlib's `mul_assoc`/`one_mul` idiom) rather than as
  function-typed class methods. The type is `∀ params, <ensures>`
  for unit-return cases and `∀ params, { r : RetTy // <ensures> }`
  for non-unit-return. Instance bodies provide a tactic proof; the
  caller accesses the lemma via typeclass dispatch (`have _ :=
  HasZero.val_is_zero t`). See "Trait class and instance emission"
  for the full mechanics, plus "Trait class+instance emission:
  deferred edges" for what remains. Pinned by
  `test_proof_fn_trait_method_emission_probe` and 8 sibling tests.
  Termination on RECURSIVE proof-fn trait methods is still deferred
  (class fields don't accept `termination_by`).

#### Tactic / automation limitations

* **`tactus_auto`'s default toolbox is `rfl | decide | omega | simp_all | tactus_case_split`.** Exec-fn obligations needing `nlinarith`, `ring`, `polyrith`, `aesop`, `positivity`, etc. fall through to the `fail` branch — unless a per-fn override is set (see below). Proof fns *can* use any Mathlib tactic in their `by { … }` block.
* **`omega` is uniquely intro-aware among the default tactics.** Tactus emits each obligation theorem in open form: `∀ (binders), (bound hyps) → (let frames) → (hypothesis chain) → goal`. `omega` walks under the leading `∀`s and `→`s automatically, picks up all hypotheses, and reasons about them. Most Mathlib tactics (`nlinarith`, `linarith`, `ring`, `polyrith`, `positivity`, `field_simp`) operate on the *current* goal state without intro-ing — so writing `assert(P) by { nlinarith }` against an open-form goal sees `∀ i, ...` and treats `i` as a bound variable, not as a fact-in-scope. Users hitting this write `intros; nlinarith` (or `intros; linarith` / `intros; ring`) — the explicit intro peels the binders into the hypothesis context so the nonlinear tactic can engage. **This is intentional Lean / Mathlib design**, not a Tactus bug. The body-assert pattern (see above) avoids the issue locally: place `assert(P) by { intros; nlinarith };` inside the body at the point of friction; the asserted hypothesis closes the outer obligation via `simp_all` from a flat hypothesis, no intro shuffling needed at the maintain step. Documented as folklore 2026-05-17 after surfacing in tutorial work on iterative-vs-recursive numeric specs.
* **Spec fn calls in goal position need explicit unfolding.** The default toolbox handles spec fn calls in *hypothesis* position fine (the hypothesis enters the context as-is and the proof obligation rarely needs to inspect it). In *goal* position — e.g., `id_u8(i+1) == (i+1)` as a loop-invariant maintain step where `id_u8` is a `noncomputable def` — `simp_all` doesn't unfold non-`@[simp]` defs and `decide` doesn't reduce through `noncomputable`. **Two workarounds, both pinned 2026-05-10:**

  **(1) Body-assert pattern (preferred, no syntax extension needed).** Place `assert(invariant_expr) by { simp_all [f] };` at the point where the obligation fires — END of loop body for maintain (so `i` is post-assignment), BEFORE loop for init, end of fn body for postconditions. The asserted hypothesis enters the obligation's OblCtx; the obligation's goal closes via the asserted hyp. `simp_all [f]` is the complete-proof shape because the assert's own theorem has all surrounding context as preconditions (`<hyps> → P`), so the tactic must intro + unfold + close in one shot — `simp_all [f]` does all three. Pinned by `test_exec_body_assert_discharges_invariant`. Discoverability is preserved by the existing error UX: failing tactus_auto shows the goal and source location, telling the user exactly what proposition to assert and where.

  **(2) Fn-level tactic prefix (simpler for trivial cases).** `proof { try unfold f }` at the top of the fn body. Tactus's tactic-prefix mechanism applies the proof block to EVERY theorem the fn emits (init/maintain/use/postcondition); the `try` is load-bearing because bare `unfold f` fails on theorems whose goal doesn't mention `f` (e.g., the invariant init theorem proving just `i ≤ n`). `try unfold f` no-ops where `f` doesn't appear and unfolds where it does. Per-fn override `#[verifier::tactus_tactic("(try unfold f); tactus_auto")]` works the same way. Pinned by `test_exec_loop_invariant_with_spec_call_try_unfold`.

  Both workarounds use existing Tactus surface (no parser extension required). The body-assert pattern is more targeted (one assert per failing obligation, located at the obligation site); the fn-level prefix is more uniform (one fn-level annotation, no per-obligation thinking). Choice depends on whether you want unfolding for everything or just specific obligations.
* **Per-fn tactic override (LANDED, #81).** `#[verifier::tactus_tactic("…")]` replaces `tactus_auto` as the default closer for the marked fn's emitted theorems. The argument is any Lean tactic string (e.g., `"ring"`, `"nlinarith"`, `"first | tactus_auto | tactus_usize_bound"`). Doesn't affect `assert(P) by { user_tac }` sites — those always use the user-supplied tactic. Empty strings rejected at parse time.
* **`tactus_usize_bound` tactic (LANDED, #82).** Discharges goals over `usize_hi` / `isize_hi` (`2 ^ arch_word_bits` / `2 ^ (arch_word_bits - 1)`) by `rcases arch_word_bits_valid; subst; simp only [usize_hi, isize_hi]; first | decide | omega`. Composes via `tactus_first` so users can layer it: `#[verifier::tactus_tactic("first | tactus_auto | tactus_usize_bound")]`. Without this, USize/ISize arithmetic obligations needed manual `cases arch_word_bits_valid` blocks.
* **Mathlib auto-tactics unused by default for exec fns.** Exec-fn `tactus_auto` is intentionally minimal to keep verification predictable; extending the default toolbox is a design call. Per-fn override is the per-fn opt-in.

#### Architecture debts (working-but-not-ideal)

* **Two parallel expression renderers — shared leaves extracted, deeper unification rejected.** `to_lean_expr.rs` (~495 lines, proof fn / callee spec inlining) and `to_lean_sst_expr.rs` (~565 lines, exec fn bodies) render structurally different trees: VIR-AST's `Block`/`Match`/`Ctor`/`PatternX`/`PlaceX` don't cross to SST; SST's `CheckDecreaseHeight`/`CallFun::InternalFun`/flattened statement sequence don't cross to VIR-AST. The shared rules — op tables, constant rendering, `Clip` coercion direction, binder construction — live in `expr_shared.rs` so divergence is a compile error. Full unification (trait over source-expression type, or routing callee specs through SST) was investigated and rejected; see the dedicated § "Two parallel expression renderers" above for the analysis.
* **Two-pass over loop bodies.** `build_wp_loop` calls both `collect_modifications` and `build_wp` on the body. *Audited 2026-05-11 (#117) — keep as-is.* `collect_modifications` is structural-only — it cares about 4 of the ~15 statement variants `build_wp` walks (`Assign` / `Block` / `If` / `Loop`) and ignores the rest. Fusing would mean threading a `&mut ModCollector<'a>` through `build_wp`'s signature across 7 production call sites (entry, Block-sequential, If-then, If-else, ClosureBody, Loop-body, two cond_setup wraps); the recursive arms that don't structurally modify state would still have to thread it because they recurse into children that might. Every future statement variant would have to consider both concerns. The perf saving is one tree traversal per loop body — realistic body sizes 10-100 stmts, dominated by downstream Lean checking, not Rust compilation. The redundancy is also bounded in the other direction: `collect_modifications` runs only on loop bodies (not the fn-level body), so a non-loopy fn does zero collection passes.

  Post-hoc extraction from the built Wp tree was also considered: Wp::Let conflates mutation-as-shadowing (`is_init: false` assignments) with new-binding lets, so walking the Wp tree can't distinguish "external mod" from "local let" without information that the pre-pass already has natively. **Conditions for revisiting**: (a) a profile flags this as load-bearing on a real codebase, or (b) Verus upstream stashes pre-computed mod sets on `StmX::Loop` (orthogonal change, eliminates the pass entirely), or (c) a refactor of `build_wp` makes the threading natural — e.g., a general `WpCtx`-style accumulator that all statement variants already touch. None apply today; clean separation wins.
* **Sanity-check allowlist auto-derived from `TactusPrelude.lean` (#118).** `extract_prelude_names` parses the prelude text at first call and caches the result via `OnceLock`. Adding a new `axiom NAME` / `def NAME` / `noncomputable def NAME` / `syntax "NAME"` / `macro "NAME"` / `elab "NAME"` to `TactusPrelude.lean` automatically updates the sanity allowlist — no `sanity.rs` edit required. Pre-#118 the list was a hardcoded `matches!` arm prone to drift. Pinned by `extract_prelude_names_recognises_current_prelude` (the auto-derived set still contains every name the legacy hardcoded arm did) and `extract_prelude_names_handles_each_form` (each prelude declaration form is recognised).
* **Sanity check returns Err, not panic (landed 2026-05-12).** `debug_check` originally panicked on unresolved references, which killed the test harness process and prevented graceful error reporting. Now it returns `Result<(), String>` and callers (`check_proof_fn`, `check_exec_fn`) propagate as `CheckResult::Failed`. Test pinning becomes possible: probe tests can assert specific sanity-error patterns via `=> Err(_)`. Pre-fix, the panic was either masked by accidental cmd ordering or by test harness signal handling — neither was reliable.
* **Artifact written before sanity check (landed 2026-05-12).** `pp_commands` + `write_lean_file` now run BEFORE `debug_check`, so the generated `.lean` is always on disk for inspection (per the path mentioned in error messages) — even when sanity rejects. Pre-fix, sanity-rejection meant no artifact was written; users couldn't `cat` the file to see what Tactus generated. Inverting the order makes debugging easier without changing the error path.
* **Expected VIR variant list for coverage is hand-maintained.** `tactus_coverage.rs` lists variants we expect to see. Macro-deriving from the enum would need Verus-upstream `strum` derives — not feasible without vendoring changes.
* **`_tactus_d_old` not gensym'd** — see its dedicated section.
* **`OblCtx::with_frame` uses `im::Vector` (LANDED 2026-05-09).** Originally `Vec<CtxFrame>`, with `clone()` cost O(N) per `with_frame` call → O(N²) total memory across deeply-nested recursion. Switched to `im::Vector<CtxFrame>` (RRB-tree with structural sharing): `clone()` is O(1), `push_back` O(log N). The walker pattern `let new_obl = obl.with_frame(f); recurse(&new_obl)` keeps its API verbatim; the dependency adds `im = "15"`. Same session also closed an adjacent allocation pattern: `loop_stack: &[&WpLoopCtx]` → `&LoopStack<'p>` linked-list (`enum LoopStack { Empty, Cons(&WpLoopCtx, &LoopStack) }`) where each nested loop's `Cons` cell lives on the caller's stack frame, no heap.
* **`substitute` boilerplate — LANDED via #98 (2026-05-05).** Four helpers in `lean_ast.rs` concentrate per-variant structural recursion: `walk_children`/`map_children` for ExprNode, `walk_pattern_children`/`map_pattern_children` for Pattern. The five Expr walkers (`substitute_impl`, `collect_free_vars`, `collect_all_names`, `strip_span_marks_node`, `mentions_free_var`) and the two Pattern walkers now handle only the variants whose semantics differ from "uniformly recurse." Per-walker shrinkage was significant (strip_span_marks_node 70→5 lines, collect_all_names 60→25, collect_free_vars 65→45, substitute_impl 125→75); net file +94 because the helpers themselves are sizeable, but the structural win dominates: walk_children and map_children are exhaustive (no catch-all), so a new ExprNode/Pattern variant is a compile error there, forcing one edit instead of five walker edits.

  **Binder convention promoted to compile-time enforcement (#98 follow-up).** Originally the three scope-tracking consumers (`substitute_impl`, `collect_free_vars`, `collect_all_names`) used `_ => walk_children(...)` fallthroughs for non-special variants. A future binder ExprNode variant could silently slip through and mis-track scope. The fix: a `ScopeKind<'a>` enum (`Var(name) | Let{...} | Quantified{kind, binders, body} | Match{...} | Other`) and an `ExprNode::scope_kind()` method that dispatches every variant. Both `scope_kind()` and the consumer matches are exhaustive (no `_ =>`). The structural lock: a new ExprNode variant compile-errors in `scope_kind()`, forcing categorization; if the contributor adds a new `ScopeKind` variant, every consumer compile-errors, forcing them to decide scope semantics for the new shape. The contributor *could* still mis-categorize a binder as `ScopeKind::Other` (the type system can't tell them they're wrong), but that's a positive lie rather than a forgotten arm. A `QuantifierKind` enum (Lambda/Forall/Exists discriminator) lets the substitute_impl Quantified arm rebuild via `kind.build(bs, body)` instead of three separate arms.

  3 new unit tests pin the helpers' shapes (149 total).
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

     **Audited 2026-05-11 (#150) — keep as-is.** The earlier
     framing called this "over-deriving" with reference to
     single-variant types not needing the accessor `default`
     fallback. The audit revised that framing: `Inhabited` is
     more broadly load-bearing than just accessor synthesis.
     `GetElem!`-style indexing (`xs[i]!` for `BinaryOp::Index`
     and `s.data[i.toNat]!` in `Tactus.strGetChar`) also
     requires `[Inhabited α]` on the element type. Any user
     datatype that ever flows through panic-on-OOB indexing
     needs the instance — including single-variant structs.
     So the "over" in over-deriving was the conservative case,
     not the necessary case.

     Visibility audit: the `deriving Inhabited` clause IS
     visible in the generated `.lean` (user can read it). User
     doesn't write it, but the result isn't hidden — same
     category as auto-emitted accessor fns or `T.height`
     companion fns. Substrate-class auto-emission, documented
     here.

     **If narrowing ever becomes necessary** (e.g., a user
     datatype whose Inhabited derivation Lean rejects —
     zero-variant enums are Verus-upstream-blocked; recursively
     uninhabitable shapes are theoretically possible but
     would also break the user's exec code that constructs
     them), the gate would be: emit when (a) multi-variant
     with non-Inhabited-derivable field types, OR (b) any field
     position reaches `BinaryOp::Index` / `Tactus.strGetChar`
     downstream. The (b) gate requires cross-fn analysis
     making the narrowing non-trivial — another reason the
     unconditional emit stays.

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
     args, _)` regardless of `args` length; the recursion check
     (originally `field_is_self_recursive`, generalised to
     `field_recursive_target` per #109) matches when the field's
     path is in the parent's SCC regardless of args (recursion is
     on the structure of the datatype, not on A). `height_fn_for_datatype` emits `def T.height {A : Type}
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

  **Mutually recursive datatype SCCs — LANDED via #109.**
  `enum Tree { Branch(Box<Forest>) }` + `enum Forest { Cons(Box<Tree>) }`
  now emit correctly: `dep_order::order_datatypes` runs Tarjan's SCC on
  the field-type reference graph; SCCs of size >1 produce a `mutual ...
  end` block of inductives, per-type accessors outside the block, and a
  second `mutual ... end` block of height fns. `field_recursive_target`
  (renamed from `field_is_self_recursive`) accepts the SCC path set, so
  `Tree.height` calls `Forest.height` for Forest-typed fields rather than
  silently treating cross-type fields as non-recursive. `Inhabited` derives
  inline on each inductive — Lean accepts deriving inside a mutual block
  and produces conditional instances. Sanity check (`sanity.rs` Mutual
  arm) predefines `Datatype` names alongside `Def`/`DefCurried` so
  cross-type field references resolve. Generate.rs adds a transitive
  closure over field-type refs (`collect_references` doesn't walk into
  variant fields by itself) before grouping. Pinned by
  `test_exec_mutually_recursive_datatypes` (basic SCC emission) and
  `test_exec_call_recursive_over_mutual_datatype` (recursion over an SCC
  member exercises cross-type height calls in the termination obligation).

  **Explicit deferrals (still rejected with clear message):**
  - **Recursive function fields** (`struct S { f: FnSpec(int) →
    Option<S> }`). Verus has a special axiom
    (`recursive_function_field` in `datatype_height_axioms`) for
    this; we don't mirror it.
  - **Lexicographic `decreases a, b` — LANDED via #110.** See
    "Loop-shape restrictions" entry above for the encoding.

  **Cross-fn-SCC mutual recursion with cross-type decreases — LANDED via
  #109 stretch.** When fns A and B mutually call each other and have
  `decreases` on different SCC members (A on Tree, B on Forest), the
  CheckDecreaseHeight obligation now correctly emits `<cur_T>.height cur
  < <prev_T>.height prev` — each side picks its OWN type's height fn
  rather than reusing `cur`'s for both (the pre-fix bug, which produced
  `Forest.height` applied to a Tree-typed value and failed Lean's type
  check). The comparison typechecks because both height fns return Nat;
  semantic soundness comes from the mutual height block — `Tree.height
  (Branch f) = 1 + Forest.height f`, so `Forest.height f < Tree.height
  t` for `t = Tree.Branch f`. Pinned by
  `test_exec_cross_fn_scc_cross_type_decreases` (positive) and
  `test_exec_cross_fn_scc_nondecreasing` (negative — same-arg recursion
  fails as expected).

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

  **`&mut a.b.c` (deeper field paths) LANDED via #144.**
  `MutTargetRaw::Field` extended to carry `field_oprs:
  Vec<&FieldOpr>` (peel order, outermost-first = deepest-mutated-
  first). `extract_mut_target` rewritten as a peel loop that
  collects field oprs through any depth; single-variant gate
  applied at each level. `push_post_call_frames` Phase 4 builds
  nested structure-updates inside-out — for `&mut a.b.c` emits
  `let a := { a with b := { a.b with c := <fresh> } }`. Same
  "no havoc encoding needed" win as #87.

  **`&mut t.<i>` (tuple field) LANDED via #145 + #146.**
  Originally a separate `MutTargetRaw::TupleField { base, index,
  arity }` variant; the variant was retired in `73d1dd6` (see
  "Mixed tuple-and-struct paths" below) and folded into
  `MutTargetRaw::Field { field_oprs }` with per-step `Dt::Path`/
  `Dt::Tuple` dispatch. Lean's `{ x with f := v }` syntax doesn't
  compose with `Prod`, so the rebind uses Lean tuple syntax
  `(t.1, fresh)` (sugar for `Prod.mk a b`) — distinct from
  anon-ctor `⟨a, b⟩` which fails to elaborate at let-bindings
  without a type hint. New `ExprNode::Tuple(Vec<Expr>)` AST variant
  pretty-prints as `(a, b, c)`; replaces the prior `ExprNode::Anon`
  rendering for `Dt::Tuple` ctors at `expr_shared::ctor_node` (the
  latent bug where every tuple let-binding had been failing to
  elaborate was masked because no exec-mode tuple let-binding test
  existed pre-#145). #146 added `tuple_field_accessor(arity, n)`
  helper: arity-2 i=0 → `1`; arity-3 i=1 → `2.1`; arity-4 i=2 →
  `2.2.1`; arity-N last position → `2` repeated N-1 times. Lean's
  right-nested `Prod` (`(a, b, c) : Int × (Int × Int)`) needs
  the multi-segment accessor for elements past the second; the
  existing `field_access_name` returned `(n+1).to_string()`
  which was correct for arity-2 only — Tactus had no arity > 2
  tuple test before #146 to catch it.

  **Mixed tuple-and-struct paths LANDED via `73d1dd6` (2026-05-11).**
  `&mut s.tup.0` (struct field containing a tuple) and `&mut t.0.f`
  (tuple slot containing a struct) are real shapes that the prior
  `TupleField`-vs-`Field` split silently rejected — the recursive
  Field peel ignored `Dt::Tuple` at depth, and the top-level tuple
  special case required the base to be a bare Var. Fix: drop the
  `TupleField` variant; `MutTargetRaw::Field { field_oprs }`
  already carries per-step `FieldOpr.datatype`, so the rebind loop
  dispatches on it inline (`Dt::Path` → Lean structure update,
  `Dt::Tuple` → tuple ctor rebuild). Path steps may now interleave
  freely. Pinned by `test_exec_call_mut_arg_struct_then_tuple`
  (struct-then-tuple), `_tuple_then_struct` (tuple-then-struct),
  `_mixed_path_siblings_preserved` (both struct's other field AND
  tuple's other slot survive the rebind).

  **Explicit deferrals (still rejected in `build_wp_call`):**
  - **`&mut v[i]`** (Index L-value) — **cross-crate-trait-emission-
    blocked**, NOT spec-inlining-blocked and NOT rebind-shape-
    blocked. Probe `test_exec_call_mut_arg_vec_index_probe`
    (2026-05-17) confirmed: in `new-mut-ref` mode, `&mut v[i]`
    desugars to `vec_index_mut(&mut v, i)` whose `&mut` arg is
    Var-shaped, so `MutTargetRaw::Var` handles it with no new
    variant. `vec_index_mut`'s spec IS cross-crate-inlined (the
    `seq.Seq.update Int (view ...) i (...)` term appears in the
    generated goal). What blocks verification is cross-crate
    `View` trait emission bugs: (A) standalone `view.view` axiom
    collides with the `view.View.view` class method; (B) the
    `View (Vec T A) (Seq T)` instance is body-less; (C) a pre/
    post substitution bug aliases `final(vec)` with the post-
    state existential in one position. All three sub-tasks of
    #122 cross-crate trait+instance emission, not #106. In legacy
    mode `&mut v[i]` is upstream-blocked outright ("index for &mut
    not supported", `rust_to_vir_expr.rs:3284`).
  - **Multi-variant enum field mutation** — **upstream-blocked
    at Verus's mode check**. Verus rejects `ref mut` patterns:
    "The verifier does not yet support the following Rust feature:
    &mut types, except in special cases." Direct `&mut foo.f` for
    enum-typed `foo` isn't expressible in Rust without unsafe;
    the only viable shape (pattern binding `if let Foo::A { ref
    mut val }`) is rejected upstream. Pinned by
    `test_exec_call_mut_arg_enum_field_upstream_blocked`. If Verus
    ever lifts `ref mut`, the test surfaces as flippable Err and
    Tactus would need a match-and-rebuild encoding (Lean's
    `match foo with | Foo.A x y => Foo.A fresh y | other => other`
    — the wildcard arm keeps the match exhaustive even when
    semantically unreachable).
  - **Mixed tuple-and-struct paths** (`&mut s.tup.0`,
    `&mut t.0.f`) — LANDED via `73d1dd6` (2026-05-11). The
    earlier `MutTargetRaw::TupleField` variant was retired in
    favour of `MutTargetRaw::Field { field_oprs: Vec<&FieldOpr> }`
    whose rebind loop dispatches per step on `FieldOpr.datatype`
    (`Dt::Path` → Lean structure update; `Dt::Tuple` → tuple
    ctor). Path steps may now interleave freely. Pinned by
    `test_exec_call_mut_arg_struct_then_tuple`,
    `_tuple_then_struct`, `_mixed_path_siblings_preserved`.
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

* **Cross-crate verification** — narrower than originally framed; see audit results next. The 2026-05-12 audit (#122 probes 1-6) established that Verus's `merge_krates` already brings imported crates' fns into the merged `vir_crate` Tactus receives, and `export_crate` preserves `pub open spec fn` bodies. Most "cross-crate" scenarios work today:
  - Probe 1-3 (`pub open spec fn` calls from vstd): work end-to-end. The standalone def emits via dep_order's normal walk.
  - Probe 4 (`Option<u8>` via `vstd::prelude::*`): works.
  - Probe 6 (local `pub uninterp spec fn`): works after the 2026-05-12 body-less emission fix (now emits as `Command::Axiom`).

  The genuine remaining gap (Probe 5, `vstd::seq::Seq`): external_body types currently emit as empty `structure` rather than as opaque types. See "Trait class+instance emission: deferred edges" above for the soundness concern. The `CrateDecls.lean`-per-crate-file infrastructure originally envisioned is NOT what's blocking — `merge_krates` does the work. The narrower fix (opaque-type emission for external_body) is a more targeted piece of work.

  Tasks still tracked under cross-crate umbrella:
  - **#125 cross-crate trait method decls** — when the trait method decl's `Fun` isn't in `fn_map` (genuinely cross-crate from a non-vstd-prelude path), `spec_source` returns Err. Currently rare in practice because vstd's traits aren't usually trait_method_impl'd in user crates that Tactus verifies.
  - **External-body type opaque emission** — see deferred-edges section above.
  - **Dynamic dispatch via `dyn Trait`** — same cross-crate rejection path as #125.
* **`#[verifier::heartbeats(N)]` attribute** — per-fn Lean `maxHeartbeats` override. DESIGN.md mentions; not wired through `vir::ast::FunctionAttrsX`.
* **Lean version pinning / CI matrix.** `lean-toolchain` is pinned to `v4.25.0`; tactic behaviour could shift on upgrade. No automated regression against multiple Lean versions.
* **Per-module `.lean` file generation.** Current design emits one file per fn (`target/tactus-lean/{crate}/{fn}.lean`). At scale, per-module would amortize preamble and olean caching; HANDOFF notes it as future work.

#### Considered surface extensions (rejected, with notes for future)

Designs we explored, prototyped to varying depths, and consciously chose not to land. Each entry records what we tried, why we stepped back, and what conditions might justify revisiting. **Not currently planned**; the body-assert pattern + `try unfold` prefix (documented under "Tactic / automation limitations" → "Spec fn calls in goal position need explicit unfolding") cover the same use cases at zero implementation cost.

* **Per-obligation proof attachment via `invariant P by { tac },` syntax** (#148, prototyped + reverted 2026-05-10). User writes the proof inline at the invariant clause; codegen attaches it as the closer for that invariant's INIT and MAINTAIN theorems. Motivating use case: spec fns in invariant goal position (e.g., `invariant id_u8(i) == i` where `id_u8` is `noncomputable def` and `simp_all` can't unfold it without an explicit hint).

  **What we tried:**
  - **Stage 0 (parser change)** — added `Specification.tactics: Vec<Option<TacticBy>>` parallel array in syn-verus, gated on `Context::Expr` to avoid hijacking fn-signature `proof fn … by { fn_tactic }`. Landed; full e2e suite (322 tests) green. Two sanity tests (`test_exec_invariant_by_tac_parses_stage0`, `test_exec_invariant_by_tac_mixed`) confirmed the syntax parses end-to-end without affecting other code. *Note: these test names are referenced for forensics only — the tests were reverted along with the rest of Stage 0; grep won't find them in the tree.*
  - **Stage 1 (proc-macro desugaring)** — visit_expr_while_mut / visit_expr_loop_mut would synthesize `assert(P) by { tac };` body-assert stmts (one BEFORE the loop for INIT, one at end of body for MAINTAIN), reusing Tactus's existing `assert(P) by { tac }` machinery. Implementation hit a parser interaction we didn't fully diagnose: simple test cases that worked under Stage 0 alone failed when Stage 1's syntax.rs changes were added. Likely a span-handling subtlety in the synthesized Assert AST nodes; not chased.
  - **Stages 2+ (pipeline threading alternatives)** — sketched: VIR `LoopInvariant.tactus_proof: Option<TactusSpan>` field threaded through proc-macro → rust_to_vir → SST → sst_to_lean. Estimated ~150-250 lines across 5-6 files including VIR shape change. Cleaner-typed than parallel arrays, but real cross-cutting cost.

  **Why rejected:**
  - The user-visible win is modest. Body-assert (`assert(invariant_expr) by { simp_all [f] };` placed before the loop and at end of body) achieves the same outcome with two extra lines per spec-fn-using invariant. For realistic exec fn counts this isn't crippling.
  - Parser-extension friction interacted with Verus's existing `proof fn … by { fn_tactic }` syntax in subtle ways. The `Context::Expr`/`Context::Item` gating worked for the simple cases but the Stage 1 desugaring hit a non-obvious failure mode. Implementation cost was migrating from "easy" to "real engineering" mid-investigation.
  - Maintenance surface vs reward. Even Stage 0 alone (parser captures `tactics` field, ToTokens drops it) adds upstream-rebase friction: every Verus rebase needs to verify `Specification`'s shape change doesn't conflict, plus the hand-edited `gen/clone.rs` Range<usize> workaround needs to survive. Without a downstream consumer, that's pure cost.
  - Two complementary workarounds already exist and are documented (see "Spec fn calls in goal position need explicit unfolding"). Users have working paths.

  **Conditions for revisiting** (any one of these would shift the cost-benefit):
  - Real users report body-assert as a significant UX pain point in a multi-fn / multi-invariant codebase
  - A clean implementation path emerges that doesn't require pipeline threading (e.g., source-level scanning at codegen time via tree-sitter; proc-macro desugaring with a different shape that avoids the parser interaction)
  - Verus upstream adds similar syntax for non-Tactus reasons, making the parser change a no-op rebase
  - Spec fns in goal position become much more common (e.g., a major refactor of vstd that pushes them into more invariants)

  **Don't revisit just to "complete the surface."** The detour through Stage 0/1 confirmed that the body-assert mechanism is fully expressive; the parser-extension's value is purely readability. Until that readability win is genuinely load-bearing for someone, the right answer is the one we have.

  Reverted commits: `a803bd0` (parser), `2d51b32` (sanity tests), `802dbc0` (deferred-doc).

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
* **`TypX::Boxed` / `TypX::Decorate` are the canonical transparent wrappers for self-referential datatype fields.** Shared via `peel_typ_wrappers` (in `to_lean_type.rs`), used by `is_int_height`, `decrease_height_datatype`, and `field_recursive_target` (the SCC-aware successor to `field_is_self_recursive` per #109). Mirrors `typ_to_expr`'s rendering (which peels both to produce Lean-level types). If Verus adds a new transparent wrapper for Rust `&Self` / `Box<Self>` / `Arc<Self>` / etc., one edit to `peel_typ_wrappers` updates all three call sites — without it, recursive-field detection would fail silently (field treated as non-recursive → `height = 1` for the variant → false termination obligation → recursion verifies where it shouldn't). **No shape-drift test** — would manifest as `test_exec_call_recursive_datatype_termination` regressing past the current "match-case-split" gap into a verified-but-wrong state.
* **`UnaryOp::MutRefCurrent` / `MutRefFuture(_)` / `MutRefFinal(_)` are the canonical new-mut-ref op variants** (depended on as of 2026-05-17 fix for Bug D's same-crate case in `42228d9`). `rewrite_varat_for_mut_params` in `sst_to_lean.rs` matches these explicitly: `MutRefCurrent(Var(p))` → `Var(<p>_at_pre_tactus)` (pre-state); `MutRefFuture/Final(Var(p))` → `Var(p)` (post-state). Without this, the catch-all `ExprX::Unary(_, inner) => expr_to_node(inner)` in `to_lean_expr.rs` would collapse all three to bare `Var(p)`, aliasing pre/post in inlined ensures. If Verus renames or restructures these variants, the rewrite falls back silently to the transparent passthrough and the substitution bug returns. **No shape-drift test today** — synthesizing the VIR-AST is involved; would manifest as `test_new_mut_ref_pre_post_substitution_probe` regressing.
* **`ExprX::Multi(MultiOp::Chained(ops), [a0, a1, ..., aN])` mirrors `ast_simplify`'s lowering** (LANDED 2026-05-09). The VIR-AST renderer (`to_lean_expr.rs`'s Multi arm) reproduces ast_simplify's expansion locally: pair-up adjacent operands with their op into binary comparisons, conjoin via `and_all`. Pre-fix the arm rendered as `LExpr::anon([a0, ..., aN])` (Lean tuple literal) — the comment said "tuple construction, chained conjunction, etc. — Render as Lean's anonymous constructor `⟨a, b, c⟩` — correct for tuples", and the "etc." was load-bearing. Reachable specifically because proof fns route through the *pre-simplify* krate (per the verifier doc) so Multi is still present at render time; exec-fn callee inlining goes through the simplified krate where ast_simplify has already expanded. Pinned by `test_chained_compare_in_proof_fn` and `test_chained_compare_in_proof_fn_ensures` (both fail loudly with type-mismatch pre-fix). If `ast_simplify` ever changes its Chained-expansion shape (e.g., short-circuiting or different binary-op pairing), the renderer needs to mirror the new shape — no shape-drift test pins the equivalence directly, only the user-facing outcome.

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

*Audited 2026-05-11 (#152) — keep.* Neither reshape changes
what's proven: `P1 ∧ P2 ∧ P3` ↔ proving each separately;
`let x := e; goal` ↔ `goal[x := e]` after `obl.wrap`
reconstructs. The restructuring buys per-conjunct error
localization (each conjunct's Postcondition / LoopInvariant /
LoopDecrease SpanMark drives the theorem name + error label
independently), per-theorem caching (Verus's hash-per-theorem
cache hits unchanged conjuncts on edits), and smaller
individual Z3 obligations (each `simp_all` / `omega` runs on
one conjunct, not the whole tree). The split IS visible in
output (user reads the generated `.lean` and sees N theorems
for an N-clause ensures); same substrate-class category as
`deriving Inhabited` and accessor synthesis — visible result,
downstream-justified, not hiding work.

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
* `is_mut_ref_par(&Par)` (SST) / `is_mut_ref_param(&Param)` (AST) —
  the AST/SST twins for "is this an `&mut` parameter?" Both check
  legacy mode (`is_mut: true`, plain T typ) and new-mut-ref mode
  (`is_mut: false`, `MutRef<T>` typ). Centralising the predicate
  keeps `walk_call`'s mut_args collection (in `build_call_mut_args`)
  and the per-param subst-map structure (in `add_param_subst_entries`)
  in lockstep — divergence would silently miscompile new-mut-ref-
  shaped callees whose params reach the second consumer as
  `is_mut: false, typ: MutRef<T>` (extracted 2026-05-09 review pass).

**Two-site `value_subst` consultation — sync risk.** Render-time
substitution at `ReadPlace+Local` happens at TWO entry points in
`to_lean_expr.rs` that must agree:

1. `expr_to_node`'s `ExprX::ReadPlace(place, _)` arm — early-return
   when `place.x = PlaceX::Local(v)` and `value_subst` hits. Handles
   the direct case (`ReadPlace(Local(h), _)`).
2. `place_to_expr`'s `PlaceX::Local(ident)` arm — same lookup,
   different entry. Reached when `Local` is nested inside `DerefMut`,
   `ModeUnwrap`, `Field`, `Index`, etc. — the outer `ReadPlace`'s
   early-return doesn't match because `place.x` isn't `Local`, so the
   fallback `place_to_expr(&place.x, …)` recurses through the place
   structure to reach `Local` inside.

Both sites call `ctx.lookup_subst_raw(name)` and return its value
verbatim. If a future change updates one consult without the other,
nested-Place caller args (typical shape: `*h` lowered to
`ReadPlace(DerefMut(Local(h)))`) would silently skip the
substitution and render bare — the user-facing symptom is the
"unresolved `h`" sanity check failure pinned by Cluster A. No
compile-time check enforces the sync; if a third site emerges
(e.g., `PlaceX::Field`-rooted-in-Local), it'd need the same lookup.
A shared helper would centralize this — flagged for cleanup when
the third site appears.

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

**Fail-loud assertions for unreachable shapes.** A weaker form of
shape-drift detection: when Verus's pipeline shouldn't produce a
particular shape (e.g., tuples have positional numeric field names,
so `(Dt::Tuple, non-numeric field)` is upstream-impossible), the
renderer uses `unreachable!` / `assert!` with a diagnostic message
naming the fix site rather than a defensive fallback that would
silently produce wrong output. Examples (extracted 2026-05-09):

* `field_access_name`'s `(Dt::Tuple(_), None)` arm — was
  `_ => sanitize(raw)` (would silently produce a wrong field
  name); now `unreachable!` with a "probable Verus rebase shape
  drift, please open an issue" message.
* `tuple_field_accessor`'s `arity < 2` branch — was a defensive
  `(n + 1).to_string()` fallback; now `assert!(arity >= 2, ...)`.

Same triangle as before (test, helper, destructure) but with the
"test" leg replaced by an inline runtime assert when no synthesizable
SST shape exists to construct in a unit test.

The triangle these form:
* Explicit destructures catch *field additions* at compile time.
* Shared helpers catch *divergence across consumers* at edit time.
* Shape-drift tests catch *semantic shifts* at test time.

Each closes a different hole.

### Trait class and instance emission (landed 2026-05-12)

Each Verus trait maps to a Lean `class`; each `impl Tr for T` maps
to a Lean `instance`. The emission shape is governed by three
co-dependent decisions: which classes to emit, which instances to
emit, and what bodies to render for class defaults and instance
methods.

**Class emission gate** (`generate.rs` trait loop): emit `class Tr`
if EITHER `refs.traits` contains it (proof body or typ_bound brought
it into scope) OR any instance of `Tr` will emit
(`traits_with_emitted_impl`, derived from the trait_impls gate
below). The OR captures the structural co-dependency: an emitted
instance references the class, so the class MUST emit too.

**Instance emission gate** (`generate.rs` trait_impls loop): emit
`instance : Tr T` iff BOTH:
* `Tr` is in `refs.traits` (something brought the trait into scope —
  via typ_bound, Dynamic-dispatch call site, or the exec-callee-spec
  walk that picks up trait method decl typ_bounds).
* `T` is in `refs.datatypes` (the implementor type is referenced).

For non-Datatype implementors (primitives, generics, tuples), the
second check is vacuously true.

Pre-2026-05-12 the gate was `refs.traits.contains` alone, which was
correlated-by-accident with method-reach: traits only entered
`refs.traits` when an impl method body was walked, so the implicit
gate was "any impl method reached → emit all impls." Body-less spec
fn emission (#147 follow-up) broke that correlation, surfacing the
latent design flaw. The trait+implementor gate makes the structural
property explicit. An intermediate Rule Y gate ("any method_impl
reachable from proof fn") was tried and rejected: it failed for
default-inheriting impls (`impl Foo for Q {}`), where Verus's
resolution at the call site routes through the trait method decl —
no specific impl method appears in needed_fn_set.

**Class structure** (`to_lean_fn::trait_to_ast`):
* `ClassMethod` carries `name`, `ty`, optional `default: Option<Expr>`,
  and `termination_by: Vec<Expr>`.
* For spec-mode methods with a trait-side default body, `default`
  renders the actual body via `vir_expr_to_ast`. Lean unfolds class
  defaults during typeclass dispatch — the body is load-bearing for
  spec methods.
* For exec/proof methods, `default` renders the placeholder
  `default` (Lean's `Inhabited`-typeclass-provided value). Two
  reasons: (1) rendering exec bodies via `vir_expr_to_ast` panics
  on `Assign` / `Loop` / `Return` (exec-mode constructs the spec
  renderer doesn't handle), (2) the body isn't load-bearing —
  `walk_call` inlines specs, not bodies via typeclass dispatch.
* `termination_by` is rendered only for spec methods (exec/proof
  bodies are placeholders so don't need termination).

**Instance structure** (`to_lean_fn::trait_impl_to_ast`):
* Methods with `body = None` are filtered entirely — they inherit
  from the class default. For an empty impl (`impl Tr for T {}`),
  this yields `instance : Tr T where` with no methods listed; Lean
  dispatches via the class.
* For `body = Some` methods: spec methods render actual body via
  `vir_expr_to_ast` (load-bearing); exec/proof methods render the
  `default` placeholder.

**Call-site rendering: class-qualified for `Dynamic` / `DynamicResolved`** (landed 2026-05-17). `to_lean_expr::call_to_node` renders trait method calls via `trait_method_ref(fun)` (producing `Trait.method`) for both `Dynamic` and `DynamicResolved` call kinds. Goals/ensures/requires referring to `t.method()` thus emit `Trait.method t` — typeclass dispatch finds the instance and resolves to the impl. Pre-2026-05-17 `DynamicResolved` rendered as `lean_name(&resolved.path)` (the bare impl-method path), so goals contained mixed bare/class-qualified forms. Class-qualified everywhere unifies the surface.

**Generic disambiguation via TypeAnnot wrap.** For class-method calls, each value arg and the call's return position get wrapped in `(... : T)` when the type is concrete (no `TypX::TypParam` / `Projection`). Lean's class-method auto-binding infers Self + assoc types from value args, but for traits with extra type params (`Container<T>`-style generics) or generic impls (`Wrapper for Box<int>`), auto-binding can't infer T from value args alone and defaults result literals to `Nat`. The annotations force top-down elaboration so the expected type constrains the metavariable. `typ_contains_param` gates the annotation so generic positions inside class declarations don't render `Self%` / `T%` (which fail the sanity check).

**Duplicate emission is canonical Lean.** TraitMethodImpl spec fns emit as BOTH standalone defs AND Instance methods. This is not a code smell — it's the canonical Lean idiom per [the reference manual § "Instance Declarations"](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/): instances aren't available for synthesis during their own definition, so an impl method whose body references a sibling spec method can't use the class-dispatched form (both bare `method` and `Class.method` fail mid-construction). The convention is "define a helper in the type's namespace, then reference it in the instance definition." Tactus's standalone-def emission IS that helper. Verified direct-Lean by probe `/tmp/test_instance_sibling.lean` — both forms fail; only a standalone def (or an inline literal) resolves.

**Instance method bodies use `strip_class_qualifier` to rewrite to bare forms.** The impl's body renders via `vir_expr_to_ast` which produces class-qualified refs (`Class.method`) by default. Before being placed inside the Instance's method body, `strip_class_qualifier(body, trait_short, sibling_methods)` walks the LExpr and rewrites `Class.method` → `method` (the bare standalone-def name) for each sibling method of this impl. This way the same `vir_expr_to_ast` call produces class-qualified text for goals/ensures and bare text for instance bodies, with the difference applied at the boundary that knows whether the rendering will land inside an instance.

**User-side: proof tactics unfold the class method.** `unfold value` no longer works (the standalone def's name is unqualified `value`, but the goal's call is class-qualified `HasValue.value`). Users write `unfold HasValue.value` or `simp_all [HasValue.value]` — explicit at the proof site. Per Tactus's design principle #1 (transparency), the trait+method name is visible in the proof; no `@[simp]` auto-emission. For impl bodies that boil down to a constant or simple expression, the canonical closer is `unfold Class.method; rfl` (or `; decide` / `; trivial` for decidable or Prop cases). For goals where unfolding leaves an irreducible instance projection (`instFooBar.1 args`), use `show <unfolded form>; rfl` to bypass the projection.

Sources confirming the design:
* [Lean Reference Manual § "Instance Declarations"](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/) — "instances are not available for instance synthesis during their own definitions; they are first marked as being available for instance synthesis after they are defined." Also: "By convention, these recursive functions have the name of the corresponding method, but are defined in the type's namespace."
* [Mathlib4 — `Algebra/Group/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Algebra/Group/Basic.lean) — examples of instance bodies that reference standalone helpers in the type's namespace alongside inline library-function compositions.

**Shared `call_inlining` abstraction** (`lean_verify/src/call_inlining.rs`):
* `spec_source(callee, fn_map) -> Result<&FunctionX, &Fun>`:
  resolves `TraitMethodImpl → kind.method`. Returns `Err(method)`
  for the cross-crate case where the trait method decl isn't in
  the map. `sst_to_lean::resolve_callee` propagates the error
  (emission can't proceed without spec_callee); `dep_order` falls
  back to `callee`.
* `CallInlinedClauses { requires, ensures }` holds the VIR-AST
  clauses Tactus inlines at every call site. `requires` is
  `spec_callee.require`; `ensures` is `spec_callee.ensure.0` plus
  `callee.ensure.0` when `callee` is a `TraitMethodImpl` (#86
  impl-strengthening — caller gets the conjunction of trait and
  impl contracts).
* `collect_inlined_at_call(callee, spec_callee) -> CallInlinedClauses`
  is the single source of truth. Both `walk_call` (emission) and
  `collect_references` + `order_spec_fns` (refs collection +
  ordering) consume this. Adding a new inlined clause kind happens
  in one place; drift between dep walk and emission is structurally
  prevented.

**Dep walk follows exec-callee specs**: when the worklist hits an
exec/proof callee (in `all_fn_map` but not in `spec_fn_map`), walk
its `require`/`ensure` clauses via `collect_inlined_at_call` for
transitive spec-fn refs. The body is NOT walked — it's not inlined
at call sites, only the specs are. For `TraitMethodDecl` entries
with `has_default: true`, the body IS walked (it becomes a class
default, which Lean elaborates via typeclass dispatch — refs inside
must be in the preamble).

**Sanity check predefines class methods in scope**: before checking
any default body, all class method names are added to the binder
scope. Class defaults can reference each other (standard typeclass
self-reference pattern: `main := fun self => self.helper`), so the
scope must be primed.

**Pinned tests**:
* `test_trait_two_impls`, `test_assoc_type_basic`, etc. — existing
  trait tests pass under the new gate.
* `test_exec_call_trait_default*` — empty impls inheriting defaults
  verify via class defaults; instances emit with no methods listed.
* `test_inlined_ensure_references_trait_spec_method` — typeclass
  dispatch in #86-strengthened inlined ensures (`Foo.predicate b`)
  resolves via the instance.
* `test_trait_default_body_references_other_trait_method` — Case A
  pinned as Err, see deferrals below.

### External-body type opaque emission (landed 2026-05-12)

Types declared `#[verifier::external_body]` (canonical examples:
`vstd::seq::Seq`, `vstd::set::Set`, `vstd::map::Map`; user-defined
types follow the same shape) emit as opaque axioms rather than empty
`structure` declarations. Before this change, the empty-struct
emission gave every external_body type a unique inhabitant (`T.mk`),
so any two values collapsed via `cases x; cases y; rfl` — including
distinct ground terms like `s.push x` and `s`, a real soundness gap.

**Shape**:
```lean
axiom seq.Seq : Type → Type
@[instance] axiom seq.Seq.instInhabited (A : Type) : Inhabited (seq.Seq A)
```

For non-generic external_body: `axiom Foo : Type` + `@[instance]
axiom Foo.instInhabited : Inhabited Foo`. Type-arg currying matches
Lean's idiomatic `List : Type → Type` convention.

**Discriminator**: `dt.transparency == DatatypeTransparency::Never`
(`rust_to_vir_adts.rs` sets this for direct `external_body` and for
`external_type_specification` proxies). Empty-fields is implied but
transparency is the load-bearing signal.

**Why two axioms not one**:
* Type-only axiom closes the soundness gap (no equations between
  opaque ground terms; `cases` on an axiom-typed term fails because
  the type has no constructors).
* Inhabited axiom is required when an external_body type is a field
  of another datatype. Tactus emits accessor fallbacks `| _ =>
  default` for multi-variant enums, which needs `[Inhabited (T A)]`
  in scope. Without the Inhabited axiom, `enum Wrapper { Has(Opaque),
  None }` would fail to elaborate.

**Why not `noncomputable instance ...` with a `Classical.choice`
witness**: the choice-based shape (B in the design pass) reuses the
existing `Command::Instance` machinery with no AST changes but
emits 3 commands per type. The chosen `@[instance] axiom` shape
emits 2 commands and is the most direct expression of "this type
has an inhabitant by stipulation." Trade-off: one new field
(`attrs: Vec<String>` on `Axiom`, mirrors `DefCurried`). `@[instance]
axiom ...` is valid Lean 4 syntax (verified before threading
through; attributes apply to all declaration kinds).

**Downstream effect: Inhabited noncomputability propagation**.
External_body Inhabited instances are axioms with no executable
code. A parent datatype whose `deriving Inhabited` would call
`Opaque.instInhabited.default` to construct its default value fails
Lean's compiler IR check. Fix: when any variant field of `dt`
references an external_body datatype directly,
`datatype_decl_cmd` drops `Inhabited` from `derives` and
`datatype_inhabited_instance_cmd` emits a manual
`noncomputable instance` instead (picking a variant whose fields
don't reference external_body if one exists, otherwise falling
back to using `default` for each field — noncomputable instance
accepts axiom-backed defaults).

**Detection scope: outermost field type only**. Nested generic
references (e.g., `Vec<Opaque>` as a field) don't trigger the
gate — Lean's polymorphic Inhabited (`Vec.nil`) doesn't construct
an Opaque value at this site. Only DIRECT field types matter
(`Has(Opaque)` does trigger; `Has(Vec<Opaque>)` does not).

**Pinned tests**:
* `test_external_body_soundness_gap_probe` — empty-struct exploit
  (`cases x; cases y; rfl` proving `∀ x y : Opaque, x = y`) now
  fails to verify. Pinned as Err.
* `test_external_body_distinct_applications_collapse_probe` —
  spec-fn-axiom-applied terms also don't collapse. Pinned as Err.
* `test_external_body_embedded_in_enum` — multi-variant enum with
  Opaque field still elaborates via the manual noncomputable
  Inhabited path. Pinned as Ok.
* `test_cross_crate_probe_5_seq_in_spec` — vstd::seq::Seq emits as
  opaque axiom (no longer empty struct); closer behavior unchanged
  (still Err for the documented axiomatic-equality reason, not
  for "unknown constant"). The "latent finding" note in the test
  comment is now resolved.

### Trait class+instance emission: deferred edges

* **Case A: trait default body whose ensures references another trait
  spec method.** Pinned by
  `test_trait_default_body_references_other_trait_method`. The
  structural emission is correct — class declaration with default,
  instance with the impl's spec method body, dep walk reaches the
  right places. The remaining failure is the closer (`tactus_auto`)
  can't unfold `Foo.predicate q` in typeclass-method position:
  `try unfold predicate at *` targets the standalone def name,
  not the typeclass-method form. Same family as the existing "spec
  fn in goal position needs unfold" gap (documented under "Tactic /
  automation limitations") but the unfold-target is different.
  Forward path: extend `tactus_auto`'s toolbox with a tactic that
  unfolds typeclass-method calls by rewriting via the resolved
  instance, OR provide a user-controllable per-trait-method unfold
  hint.

* ~~**External-body type latent soundness concern.**~~ **LANDED 2026-05-12.**
  See "External-body type opaque emission" below for the resolved design.

* **Proof-fn trait methods — LANDED 2026-05-15.** `trait_to_ast` now
  mode-dispatches on method kind. For `Mode::Proof`, the class method
  emits as a **Prop-typed class field** (Mathlib's `mul_assoc`/`one_mul`
  idiom):

  ```lean
  class HasZero (Self : Type) where
    val : Self → Int
    val_is_zero : ∀ (self : Self), val self = 0   -- Prop field
  ```

  And the instance provides a tactic proof:

  ```lean
  noncomputable instance : HasZero S where
    val := fun (self : _) => 0
    val_is_zero := fun (self : _) => by
      <user-provided tactic from the impl's by { ... } body>
  ```

  Callers with `<T: HasZero>` bound access the lemma via typeclass
  dispatch: `have _ := HasZero.val_is_zero t` brings the instantiated
  ensures into scope.

  **Three pieces in the implementation:**

  1. **`proof_fn_method_type`** in `to_lean_fn.rs` — builds
     `∀ (params...) (req_hyps...), <ensures>` for unit-return proof fns,
     `∀ (params...), { r : RetTy // <ensures> }` for non-unit-return
     (rendered via the structured `ExprNode::Subtype { name, ty, pred }`
     AST node; the corresponding `ScopeKind::Subtype` arm in
     `substitute_impl` / `collect_free_vars` / `collect_all_names` /
     `sanity::check_expr` handles `name` as a binder over `pred`).
     Uses `class_method_value_binders` (not the full `fn_binders`)
     because the trait's typ_params and bounds are the class's
     responsibility, not re-introduced per method — mirrors Mathlib's
     pattern where `mul_assoc : ∀ a b c : G, ...` doesn't re-bind
     `(G : Type)` or `[Mul G]`.

  2. **`strip_class_qualifier`** — Lean rejects `ClassName.method`
     references inside the class declaration itself (the class isn't
     fully declared at that point). Mathlib uniformly uses unqualified
     sibling references. The strip pass walks the rendered LExpr via
     the structural `map_children` walker, replacing `Var("HasZero.val")`
     with `Var("val")` when `val` is a known sibling method of the
     current class. Targeted prefix-only strip — `OtherTrait.method`
     and free-standing fn refs survive correctly.

  3. **`render_by_block`** — handles tactic body indentation for
     inline `by` blocks. `read_tactic_from_source` dedents the body to
     column 0, but Lean requires `by`'s body to be on the same line OR
     indented past `by`'s column. We re-indent every line by 2 spaces
     to satisfy the indentation rule.

  **Plumbing.** A `tactic_bodies: HashMap<Fun, String>` is built once
  in `verifier.rs` via `build_tactic_bodies_map` (one pass over all
  proof fns with `tactic_span`, reading each via the existing
  `read_tactic_from_source` helper) and threaded through
  `check_proof_fn` / `check_exec_fn` → `krate_preamble` →
  `trait_to_ast` / `trait_impl_to_ast`. Five signature additions, one
  helper.

  **Trigger requirement** for the trait+impl emission gate (learned
  during probe construction): the `(refs.traits ∩ refs.datatypes)`
  instance gate (`generate.rs:199-221`) only fires when something
  brings the trait into scope — a typ_bound on a generic param or a
  Dynamic-dispatch call. A tactus_auto fn that takes only `&S` for a
  concrete `S: impl Provable` is NOT sufficient; the trait+impl
  silently don't emit and a probe that doesn't carry the bound
  passes for the wrong reason. This is principled gate behavior (no
  dead-code emission), not a bug; probes must include a generic with
  the bound.

  **Pinned tests** in `tactus.rs`:
  * `test_proof_fn_trait_method_emission_probe` — Ok. Concrete
    `impl Provable for S`; tactus_auto fn with `<T: Provable>` bound.
    Class emits as Prop-typed field; instance body is the tactic.
  * `test_proof_fn_trait_method_default_body_probe` — Ok. Trait with
    default tactic body; empty impl inherits via class default.
    Class default body emits as `by <tactic>` inside lambda.
  * `test_proof_fn_trait_method_ensures_inaccessible` — Ok (FLIPPED
    from Err on 2026-05-15). The probe that confirmed the previous
    "lemma content is lost" gap now confirms the lemma IS accessible.
    Proof fn caller with `<T: HasZero>` bound extracts the lemma via
    `have _ := HasZero.val_is_zero t` and `omega` closes the goal.
  * `test_proof_fn_trait_method_non_unit_return_deferral` — Err.
    Pins the non-unit-return case as a deferral; see TODO below.
  * `test_proof_fn_trait_method_multiple_ensures` — Ok. Trait method
    with multiple ensures clauses; renders as `∀ params, P ∧ Q`.
  * `test_proof_fn_trait_method_with_requires` — Ok. Requires clauses
    render as additional binders (`_h_req_<i> : <req>`); caller
    discharges by passing a proof.
  * `test_proof_fn_trait_method_mutual_methods` — Ok. Two proof-fn
    methods in the same trait, both referencing a sibling spec
    method. Tests that strip handles multiple Prop-typed fields.
  * `test_proof_fn_trait_method_free_standing_spec_ref` — Ok. Proof-
    fn ensures references a free-standing spec fn (not a sibling
    trait method). Strip helper correctly leaves the reference
    qualified; ordering puts the spec fn before the class so the
    reference resolves.
  * `test_proof_fn_trait_method_other_trait_ref` — Ok. Ensures
    references methods of a DIFFERENT trait via typ_bound on a
    generic param. Strip is targeted to current class only.

  **Two supporting fixes landed alongside the main work:**

  * **Dependent binder handling in `sanity.rs`.** Pre-fix, the
    sanity check's Forall/Lambda/Exists walker treated binders as
    non-dependent: it checked all binder types under the outer
    scope, then added all names at once. For `∀ (self : Self)
    (h : P self), ...`, this failed because `P self` was checked
    before `self` was in scope. Fixed to check binders left-to-
    right, adding each name to scope before the next binder's type.

  * **Class ordering in `generate.rs`.** Pre-fix, classes emitted
    BEFORE spec fns. That worked when classes only had method type
    signatures (no spec fn refs); the Prop-typed proof-fn class
    field shape changed this — class fields can reference free-
    standing spec fns in their ensures. Split-by-mode ordering:
    classes WITHOUT proof-fn methods emit before spec fns (old
    behavior, supports spec fn → class typeclass dispatch); classes
    WITH proof-fn methods emit after spec fns (new requirement,
    supports class → spec fn ensures references).

  **Limitation: true cyclic class↔spec-fn dependencies.** If a
  class `C` has a proof-fn ensures referencing spec fn `F`, AND `F`
  has a body referencing class method `C.method` via typeclass
  dispatch, there's a true cycle. The split-by-mode ordering can't
  handle this — `F` needs `C` in scope, `C` needs `F` in scope.
  And Lean's `mutual` block rejects mixing classes and defs
  (verified 2026-05-15: `error: invalid mutual block: either all
  elements of the block must be inductive/structure declarations,
  or they must all be definitions/theorems/abbrevs`). So even a
  full topological sort with mutual-block emission can't handle
  this cycle — the resolution requires source-level restructuring
  (factor out the cycle, e.g., parameterize the spec fn body with
  the class method as an explicit argument). No current test
  exercises this; flag for future work if it surfaces.

  **Non-unit return proof fns — LANDED 2026-05-15.** The class field
  type for `proof fn extract() -> (r: int) ensures r == E` renders as
  `∀ params, { r : int // ensures }` (subtype). The instance body
  emits as `fun (params...) => ⟨vir_expr_to_ast(body), by first | rfl
  | simp_all⟩`: the impl's body expression IS the witness; rfl/simp_all
  closes the equality with the ensures' RHS.

  **Two important constraints + their resolutions:**

  1. **Verus's `by { }` body syntax doesn't fit non-unit returns.**
     FileLoader sanitizes the brace body to spaces, so for a fn
     declared as returning `int`, the sanitized body has type `()` and
     Rust rejects with E0308. So non-unit return proof fns must use
     regular Verus-style bodies (just an expression). They're verified
     by Verus's Z3 path; Tactus's class+instance emission picks up the
     body via `vir_expr_to_ast` for the witness.

  2. **Inside instance bodies, sibling field refs aren't in scope.**
     Verified 2026-05-15 via `/tmp/test_instance_self_ref.lean` —
     `val self` inside an instance body errors with "Unknown
     identifier `val`", and `Foo.val self` errors with "failed to
     synthesize `Foo E`" (the instance is being constructed, no
     instance yet to dispatch through). Only the standalone def of
     the called spec method works.

     Resolution: `dep_order::seed_impl_proof_method_bodies` pre-seeds
     all impl proof-fn method bodies (non-unit return) into the
     worklist. This ensures the spec methods called from those bodies
     emit as standalone defs in the preamble, BEFORE the instance.
     The unqualified spec method name then resolves to the standalone
     def at instance-body emission time.

     Over-emit is harmless: standalone defs that nothing else
     references are inert dead code in the preamble.

  **Pinned tests:**
  * `test_proof_fn_trait_method_non_unit_return_literal` — body is a
    literal value with no sibling refs. Simplest case.
  * `test_proof_fn_trait_method_non_unit_return_sibling_ref` — body
    references a sibling spec method (`self.target()`). Exercises
    the dep_order pre-seeding path.

  **Standalone recursive proof fns — LANDED 2026-05-15 (Case 11
  part 1).** `proof_fn_to_ast` now reads `f.decrease` and populates
  `Theorem.termination_by` (mirroring `spec_fn_to_ast`); the pp emits
  `termination_by <expr>` after the tactic body (or `(e1, e2, ...)`
  for lex). Verus's `decreases n` flows through as a faithful
  translation — Verus has already certified termination, we just
  pass the measure to Lean. Pinned by `test_proof_fn_with_decreases_noncrecursive`
  (decreases on non-recursive proof fn, emission doesn't break trivial
  case) and `test_proof_fn_recursive_with_decreases` (recursive proof
  fn whose tactic body invokes itself via `have _ih := rec_trivial
  (n - 1)`). Generated Lean has `termination_by n` after `:= by` block;
  Lean's well-foundedness check uses it for the recursive call.
  Lean often auto-infers for simple structural cases (`n - 1` on Nat),
  but the explicit clause is required for Collatz-shape or non-obvious
  measures — and is structurally cleaner regardless.

  **Still deferred — recursive proof-fn TRAIT methods.** Class methods
  in Lean don't accept `termination_by` clauses directly (verified
  2026-05-15). If a proof-fn trait method has `decreases n` and its
  tactic body recursively invokes the method via typeclass dispatch,
  Lean can't auto-infer termination AND can't accept the explicit
  clause inside the class declaration. Fix involves either rendering
  recursive proof-fn trait methods through Lean's `mutual` block with
  explicit well-founded measures, or emitting them as separate
  top-level theorems instead of class fields (which would lose the
  typeclass-dispatch property the current shape provides). Untested;
  flag for future work.

* **Recursive default bodies — upstream-blocked.** A trait default
  body that calls itself. Probed 2026-05-17: Verus rejects with
  "trait default methods do not yet support recursion and decreases".
  The Tactus-side question (whether `termination_by` on a class-field
  default body would be accepted by Lean) is structurally unreachable
  through normal Tactus paths today. Pinned by
  `test_trait_recursive_default_upstream_blocked`. If Verus ever
  lifts this restriction, the Tactus-side handling will need probing
  (see #148 area for related class-field termination concerns).

* **Associated-typed default bodies — ✅ pinned.**
  `test_trait_assoc_typed_default_probe` (2026-05-17) — trait with
  `type Output`, default method returning `Self::Output`, concrete
  `int` instantiation. Renders cleanly through
  `typ_maybe_projection_to_expr`'s bare-`Output` translation. Works.

* **Generic impls (`impl<T> Foo for Vec<T>`) — ✅ pinned.**
  `test_trait_generic_impl_probe` (2026-05-17) — `impl<T> Container
  for Wrap<T>` with concrete `Wrap<u8>` in the touches fn. The
  implementor short_name (`Wrap`) reaches the
  `refs.datatypes ∩ refs.traits` instance gate correctly. Works.

* **TraitMethodImpl with body=None and no trait default.**
  Structurally invalid (Verus rejects "impl missing required method").
  `trait_impl_to_ast` skips body=None methods silently — if this
  state ever reaches Tactus (Verus bug, pipeline change), Lean
  would catch the missing-method-in-instance error directly. No
  `debug_assert` today; add if/when motivated.

* **Pure exec-call-with-spec-fn-in-ensures probe missing.**
  `test_inlined_ensure_references_trait_spec_method` exercises the
  exec-callee-spec walk via the trait method context. A simpler
  probe (exec fn `A` calling exec fn `B` whose ensures references a
  free-standing spec fn) would more directly pin the abstraction
  outside the trait setup. Worth adding if any change to the dep
  walk is suspected.

### Transparent-wrapper peel vs trait dispatch (LANDED across Phase 1 + Phase 2 + β refactor + U2)

Reference-like decorations (`&A`, `Box<A>`, `Rc<A>`, `Arc<A>`) are
now preserved as distinct Lean types via the `Tactus.Ref` / `Box` /
etc. wrapper structures in `TactusPrelude.lean`. Phase 1 (`f5362bb`,
2026-05-20) introduced the opaque wrapper types. Phase 2 (`831a293`,
2026-05-20) made `typ_to_expr` emit them. The β refactor (six
commits across 2026-05-24, capped by `d9476e6`) closed the cluster
of test failures the wrapper architecture surfaced. **U2** (2026-05-25,
four-edit refactor capped by `d9f7944`) unified the body-shadow + lift
mechanism into a single bidirectional use-site coercion, closing the
trait method class field type cluster and the multi-layer wrapper gap
in one structural change.

Pinned by `test_non_forwarding_blanket_over_ref_probe` (was Err
pre-Phase-2, flipped Ok post-Phase-2). The β refactor restored
6 cluster A failures around recursive datatypes + 3 wrapper-aware
call-site coercions that Phase 2 broke. U2 restored 7 trait method
class field type failures + closed multi-layer `&Box<u8>`-style
wrapper handling (pinned by `test_proof_fn_multi_layer_wrapper_probe`
+ `test_trait_method_multi_layer_param_probe`). See the U2 + β
refactor session entries in HANDOFF.md for the full mechanics.

#### Original gap (preserved for context)

Pre-Phase-2, Tactus peeled reference-like decorations at every site
that called `peel_typ_wrappers` / `type_short_name` — including the
dispatch site for trait method calls. This silently produced the
wrong answer when a blanket impl over a transparent wrapper had
*non-forwarding* behaviour.

**The gap, concretely.** A user crate writes:

```rust
impl<A: Foo + ?Sized> Foo for &A {
    spec fn foo(&self) -> int { (**self).foo() + 1 }
}
```

Verus's spec semantics say `(&h).foo() = h.foo() + 1` for any
`h: Foo`. Tactus peels `&h → h` at the call site, dispatches to
`Foo h`'s concrete instance, returns `h.foo()` — the `+1` is
silently dropped. The probe demonstrates this with `(&Holder{v:7}).foo()`
which should equal 8 but reduces to `7 = 8` (⊢ False).

For *forwarding* blanket impls (every blanket in vstd today —
`View for &A`, `Box<A>`, `Rc<A>`, `Arc<A>` all have body
`(**self).view()`), Tactus's peel coincidentally produces the
right answer: the inner type's instance returns the same value
the blanket would have. **The gap is silent until someone writes
a non-forwarding blanket** — which user code is fully able to
do, no vstd involvement required.

**How Verus avoids this.** `vir::context::DECORATE = true` (the
default). At the SMT *value* level, decorations are peeled (both
`&A` and `A` are `Poly`). But at the SMT *type-ID* level
(`sst_to_air::monotyp_to_id`), decorations are preserved as a
two-component tag — `&A` gets `(REF, basic A)`, `A` gets
`(NIL_SIZED, basic A)`. Trait dispatch in Z3 keys off the
type-ID, so `View (REF A)` and `View A` look up different
instances. The blanket impl's axiom bridges from the decorated
type-ID to the inner: `view((REF A), r) = view(A, deref r) + extra`.

In Tactus's Lean target, instance resolution dispatches by
literal type matching — there's no separate type-ID channel to
exploit. The analog is real distinct Lean types: emit `Ref`,
`MutRef`, `Box`, `Rc`, `Arc` as opaque wrapper-type axioms in
the prelude, render decorations through them at type sites, and
add deref ops at value sites.

**Why this isn't blocking today.**

- vstd's blanket impls are all pure forwarding — Tactus's peel
  gives the right answer for everything vstd does.
- The most visible cross-crate symptom is
  `test_exec_call_mut_arg_vec_index_probe` (Err), but its
  immediate failure mode is *emission noise* (unresolved
  references to standalone defs that never got emitted), not
  the underlying semantic gap. A targeted filter on cross-crate
  blanket-over-typ-param instances would unblock vec_index
  without addressing the semantic gap; that filter would be a
  documented triage, not a fix.
- No user-reported issue from a non-forwarding blanket impl in
  the wild. The gap is real but currently latent.

**The proper fix shape**, captured here so a future session can
start warm:

1. **Prelude wrapper types.** Add to `TactusPrelude.lean`:
   ```lean
   axiom Ref : Type → Type
   axiom MutRef : Type → Type
   axiom Box : Type → Type
   axiom Rc : Type → Type
   axiom Arc : Type → Type
   ```
   Plus `[Inhabited (Ref A)]` etc. (also axioms — opaque). Plus
   value-level deref ops: `axiom Ref.deref : ∀ {A}, Ref A → A`,
   similarly for the others.

2. **`typ_to_expr` Decorate arm.** Stop peeling for the
   reference decorations (`Ref`, `MutRef`, `Box`, `Rc`, `Arc`).
   Render each as `<WrapperName> <inner>`. Keep peeling `Boxed`
   (Verus's poly encoding — genuinely transparent in Lean's
   native polymorphism) and probably keep peeling `Ghost`/
   `Tracked` (verification metadata, not runtime types).

3. **Expression renderer.** `*r` for `r: &A` emits `Ref.deref r`
   rather than collapsing to bare `r`. `&x` for `x: A` emits
   `Ref.mk x` (or whatever Verus's lowering produces — likely a
   no-op coercion in spec mode that the renderer needs to make
   explicit). Audit `UnaryOp::Deref` and the new-mut-ref
   `MutRefCurrent`/`MutRefFuture` rewrite to land on a
   consistent lowering.

4. **Audit `peel_typ_wrappers` use sites.** Distinguish:
   - *Structural-identity peels* (keep): `is_int_height`,
     `decrease_height_datatype`, `field_recursive_target`. These
     ask "is the underlying datatype recursive / int / etc." —
     decorations are irrelevant.
   - *Rendering-equivalence peels* (remove): `type_short_name`,
     `typ_to_expr`. These determine how the type appears in
     emitted Lean — decorations matter for dispatch.

5. **`type_short_name` returns clean names for wrappers.** Once
   un-peel lands, `&A → "Ref"`, `Box<A> → "Box"`, etc. The
   "never `impl__N`" principle (DESIGN.md "Implementation
   locality") becomes structurally enforced for blanket impls
   over references — they get clean `Ref.Foo.impl.foo` etc.
   names automatically.

6. **`#55`/`#94`/`#107` `&mut` infrastructure audit.** Mut-ref
   support uses `varat_pre_name` and a normalization pass that
   maps new-mut-ref shapes to legacy. With `MutRef A` as a
   distinct type, these passes need re-checking to confirm the
   pre/post substitution machinery interacts cleanly. Probably
   the existing rewrite still works (it operates on `Var(p)`
   structure regardless of whether `p`'s type is `T` or
   `MutRef T`) but worth verifying.

7. **Test fallout.** Many existing tests bind `&self` and would
   see their generated Lean signatures change. Plan for
   multi-pass test triage. Most should still verify (no
   semantic change for forwarding cases), but the generated
   Lean shape changes meaningfully.

**Phasing (LANDED):**

- **Phase 1** (`f5362bb`, 2026-05-20): added wrapper type axioms
  (Tactus.Ref / Box / Rc / Arc / MutRef) to `TactusPrelude.lean`.
- **Phase 2** (`831a293`, 2026-05-20): `typ_to_expr` Decorate arm
  emits wrapper types instead of peeling. `test_non_forwarding_blanket_over_ref_probe`
  flipped Ok.
- **Wrapper-arch follow-on** (2026-05-23 + 24): mut-ref collapse
  (`bffaf65` + `6b1f298`), wrapper-aware height fns (`ca8f979`),
  binder naming cleanup (`c3d2eda` + `da63c45`), termination_by
  sizeOf for recursive height fns (`b52b67a`). 376 → 419 tests.
- **β refactor** (2026-05-24, 6 commits capped by `d9476e6`):
  closed the 6 cluster A failures and recovered 3 strslice/
  inlined_ensure regressions. 419 → 425 tests. See HANDOFF.md.
- **U2** (2026-05-25, 4-edit refactor capped by `d9f7944`): unified
  body-shadow + lift into bidirectional use-site coercion. Closed
  the 7 trait method class field type failures + multi-layer wrapper
  gap (`&Box<u8>`-style params). 425 → 434 tests, 0 regressions.

#### U2 mechanism

Four coupled edits in `to_lean_expr.rs` + `to_lean_fn.rs`:

1. **`apply_ref_coercion_if_needed` is bidirectional.** When
   `expr.typ` has MORE wrappers than structural — insert
   `Tactus.X.mk` wraps (existing behavior). When `expr.typ` has
   FEWER wrappers — insert `.deref` chain via `apply_deref_chain`.
   The two directions are symmetric: use sites bridge in whichever
   direction is needed.

2. **`structural_typ` for `ReadPlace` is binder-aware.** When the
   inner Place is `Local(v)`, returns `binders.get(v)` (the
   binder's typ from BinderCtx) instead of `p.typ`. Reflects the
   actual Lean-level typ of the rendered variable, accounting for
   whether a body shadow was applied (BinderCtx records post-shadow
   typs at construction time).

3. **`needs_param_deref` restricted to `&mut` only.** Mutation-
   encoding cases (legacy `is_mut: true`, new-mode `MutRef<T>`,
   `Decorate(MutRef, _, _)`, BorrowMut locals) still need shadow
   because `*x = e` lowers to `let x := e` in Lean (the shadow IS
   the mutation encoding). `&`-only references (Ref/Box/Rc/Arc) no
   longer get the shadow — the bidirectional coercion handles
   use-site needs at the use sites.

4. **`binder_ctx_from_params` records post-shadow typs.** For
   params that WILL be shadowed (`&mut`), strip one outer ref
   decoration via the new `strip_one_ref_decoration` helper so
   structural_typ reflects the Lean-level reality. For non-shadowed
   (`&`-only) params, record the typ as-declared.

Plus parallel fixes at projection sites that don't go through the
lift:

* **`UnaryOpr::Field` / `UnaryOpr::IsVariant`** in
  `to_lean_expr.rs`: fields belong to the inner type, not the
  wrapper. Insert `.deref` chain based on `lean_level_wrap_count`
  (binder-aware for Var-shaped inner).

* **`PlaceX::Field`** in `place_to_expr`: same fix on the parallel
  Place renderer (reached via ReadPlace → place_to_expr). Uses
  `place_lean_wrap_count` helper.

* **Non-structural binops** (`Tactus.strGetChar`, `Bool.xor`, etc.):
  in `to_lean_expr.rs` Binary arm with `binop_to_ast` returning
  `None`, peel both operands via `count_ref_decorations` — mirrors
  the SST-side β refactor fix at the same arm.

#### What U2 changed semantically

* **Body context for `&`-only params**: no longer body-shadowed. The
  binder stays wrapper-typed throughout; use sites apply `.deref` (for
  field/variant access) or pass through (for method calls expecting
  wrapper).
* **Class field type for trait proof methods**: no longer needs the
  missing shadow site (A''). The bidirectional lift sees binder-typ ==
  expr-typ for the `ReadPlace(self, ImmutBor)` case and emits `self`
  directly — no over-wrap.
* **Multi-layer wrappers** (`&Box<u8>`, etc.): work uniformly. The
  bidirectional lift counts depth and inserts the right number of
  derefs/wraps. No special-casing of single vs multi-layer.
* **Generated Lean is cleaner**: many `let p := p.deref; ... Tactus.Ref.mk p ...`
  shapes collapse to just `p` because the binder is wrapper-typed
  and use sites need wrapper-typed args.

#### Why this is the right shape

Pre-U2 the architecture had three asymmetries that needed
maintenance per case:

1. Body context (shadow stripped, lift restored) vs class field type
   (no shadow, lift over-wrapped).
2. Exec fn rendering (post-β: no `&` shadow, use-site coercion) vs
   proof fn rendering (still has `&` shadow + lift).
3. Single-layer (covered by current helpers) vs multi-layer (latent
   gap requiring shadow + structural_typ changes together).

Post-U2 all three collapse to one rule: *the binder records the
Lean-level wrapper depth; use sites insert derefs or wraps as needed
to bridge*. The shadow's purpose narrows to "mutation encoding only,"
which is what the body-shadow `let x := x.deref;` is fundamentally
for (the mutation form `*x = e` lowers to `let x := e`, and the
shadow makes x's Lean type match e's inner-value type).

**Patterns and conventions that emerged from the β refactor**
(worth carrying forward to future wrapper-aware encoding work):

* **`cases h : <term>` for case-split with propagation.** When
  case-splitting on a TERM (e.g., `local.deref`) rather than an
  fvar, the bare `cases <term>` form discharges the variant at the
  case-split site but does NOT substitute occurrences of `<term>`
  elsewhere in the goal. The `cases h : <term>` form names the
  discharged-term equation as a hypothesis (`h : <term> = Variant
  ...`), enabling subsequent simp_all / rewrite to substitute
  through aliased let-bindings. Discovered closing cluster A;
  load-bearing for the wrapper case in `tactus_case_split`.

* ~~**η-reduction as substitution bridge.**~~ ~~**Selective peel based
  on callee.kind.**~~ Both patterns are SUPERSEDED by the right-way
  fix (`7d2a537`, 2026-05-24): callee-spec inlining now suppresses
  the `apply_ref_coercion_if_needed` lift at `ExprX::ReadPlace`
  sites via the `vir_expr_to_ast_for_inlining` entry point + the
  `READPLACE_LIFT_ENABLED` thread-local in `to_lean_expr.rs`. With
  the lift gone in the inlining context, no peel is needed —
  substituted-args flow through unchanged and match the callee's
  expected param type directly. The kind-discriminator (proxy for
  the structural property) is eliminated. Standalone rendering
  keeps the lift (default flag value), so proof/spec/trait-impl-
  method bodies are unchanged.

* **Non-structural-only blanket peel → structural min-depth
  reconciliation (refined 2026-05-29, commit `1852605`).** The
  original `d9476e6` rule was "never peel structural operands"
  (`==`, `+`, `*`, `≤`, ...) — peel only non-structural binops
  (those routed via `non_binop_head` to head fns like
  `Tactus.strGetChar`, which need inner-typed args). That rule was
  *too conservative*: Verus keeps `*p` (for a `&T` param) at the
  reference typ `&T` with the deref implicit, so a structural binop
  can receive mismatched operand depths — `p : &u8` (depth 1) `≤`
  `100 : u8` (depth 0) renders `p ≤ 100`, comparing `Tactus.Ref Int`
  to `Int` (a Lean type error; `test_exec_call_site_ref_to_bare_probe`).
  Structural binops now **reconcile operands to a common (min) wrapper
  depth** — peel the deeper operand(s) to the shallower. Equal-depth
  operands (the common case: `s1 == s2` for two `&T` params, `r == b`
  after `let r := b`) are untouched (min == both → zero peels), so this
  is a strict refinement, not a reversal. The body/ensures symmetry that
  `d9476e6` worried about (it broke `nested_wrapper` when ensures peeled
  but the body's `let r := b` stayed uncoerced) is preserved by the
  **paired return-expr coercion**: `build_wp`'s `StmX::Return` arm
  coerces the returned value to the declared ret typ (`WpCtx::ret_typ`),
  so body and ensures meet at the same depth (`nested_wrapper` now
  renders `r := b.deref.deref` on both sides — type-correct, still
  `rfl`). The two changes are a unit: binop reconciliation needs the
  return coercion to stay sound. Non-structural binops still peel their
  operands fully (their head fns want inner-typed args). Pinned by
  `test_exec_call_site_ref_to_bare_probe` (flipped green) +
  `test_exec_nested_wrapper_probe` (stayed green).

* **Use-site coercion at projection sites** (U2). Fields and
  IsVariant discriminators belong to the inner type, not the
  wrapper — so the renderer inserts `.deref` chains based on
  `lean_level_wrap_count(inner, binders)` before projecting. The
  helper is binder-aware so it sees the actual Lean-level wrapper
  depth (which may differ from `inner.typ` when Verus's SST has
  spec-collapsed derefs). The PARALLEL Place-side fix in
  `place_to_expr` uses `place_lean_wrap_count` — same shape,
  different node type. The two parallel renderers (`ExprX` and
  `PlaceX`) both need their Field arms updated together; a future
  shared-helper refactor would tighten this. See "Two parallel
  expression renderers" — they're parallel by construction.

* **Mutation shadow is for mutation, not for wrappers** (U2). Pre-
  U2 the body shadow `let p := p.deref;` was applied to every
  wrapper-typed param ("&-only" and `&mut` alike) on the theory that
  bodies want to operate at inner-typed level. Post-U2 the shadow
  is reserved for `&mut`-style mutation cases, where `*x = e` lowers
  to `let x := e` and the shadow makes x's Lean type match e's
  inner-value type. For read-only references, the shadow was
  decorative — the bidirectional lift handles the bridge at use
  sites without changing the binder's Lean-level type.

**Known follow-up items** (left for future sessions):

* **Shape-drift guard for the wrapper name list in `tactus_case_split`.**
  The literal `Tactus.Ref / MutRef / Box / Rc / Arc` list in the
  elab tactic (`TactusPrelude.lean`) parallels `decoration_wrapper`
  in `expr_shared.rs`. If a contributor adds a new wrapper type to
  the prelude, both sites need updating. No compile-time check
  catches divergence. A unit test that scans both lists and asserts
  agreement would close this gap.

* **Typed `non_binop_head` return.** Currently `non_binop_head(op)
  -> &str` returns just the head fn name. The SST renderer's
  non-structural binop arm applies `apply_deref_chain` to BOTH
  operands by `count_ref_decorations(arg.typ)` because all current
  `non_binop_head` targets (`Tactus.strGetChar`, `Bool.xor`, …)
  happen to want inner-typed args. The "peel both unconditionally"
  shape is a heuristic that matches today's table by coincidence.
  A typed return — e.g., `non_binop_head(op) -> NonBinopHead {
  name, arg_kinds: [InnerInt|InnerBool|InnerString|Wrapper|...] }`
  — would let the renderer derive each operand's peel from
  declared types. A future head fn that wanted wrapper-typed args
  would express that structurally instead of silently being
  over-peeled. Small refactor; only ~3 entries in the table today;
  no current failure mode would flip but adding new entries
  becomes less error-prone.

* **Shared Field-projection helper for `ExprX::Field` + `PlaceX::Field`**
  (U2 follow-up). Both renderers' Field arms now apply binder-aware
  `.deref` chains via parallel helpers (`lean_level_wrap_count` for
  ExprX inner, `place_lean_wrap_count` for PlaceX base). The shape
  is the same; the helpers differ only because the AST node types
  differ. A shared trait-or-helper would prevent divergence if
  one site is updated and the other isn't. Discovered during the
  U2 iteration — the bug initially landed in `ExprX::Field` alone
  and only after running tests did we discover the parallel
  `PlaceX::Field` path needed the same fix. Not blocking; flagged
  for cleanup when a third Field-projection site appears or when
  a related bug surfaces from divergence.

* **Multi-layer wrapper probes pinned but not the only test.**
  `test_proof_fn_multi_layer_wrapper_probe` and
  `test_trait_method_multi_layer_param_probe` exercise `&Box<u8>`
  (2-layer) via `**b` access. Deeper depths (`&&Box<u8>`,
  `&Box<Box<u8>>`, etc.) are not yet exercised; the bidirectional
  lift's count-based logic should handle arbitrary depths
  structurally, but no test pins this. Worth a probe at depth 3+
  if a real use case surfaces.

* **`vir_expr_to_ast_for_inlining` thread-local still needed**
  (vs eliminated by U2). The `READPLACE_LIFT_ENABLED` thread-local
  from the β refactor's right-way fix remains in place. Even with
  U2's binder-aware structural_typ, the inlining context has an
  empty BinderCtx (substitution happens post-rendering), so
  structural would fall back to `p.typ` (bare) and the lift would
  over-wrap substituted args. The thread-local correctly suppresses
  this. Removing it would require coordinating the substitution
  with a synthetic BinderCtx populated from the caller's arg typs —
  not currently motivated, but a candidate for future cleanup if
  the inlining pipeline is restructured.

  **Status update 2026-05-26: typed substitution closed the β
  over-wrap concern at the architectural level.** Once
  `value_subst` carries `(LExpr, source_typ)` pairs at call-site
  inlining and the renderer's `apply_ref_coercion_if_needed`
  bridges from `source_typ` to `expr.typ`, the over-wrap case the
  thread-local was suppressing no longer fires: the substituted
  value is always at its actual Lean typ, and the inner bridge
  brings it to the inner expected typ regardless of caller typ
  shape (bare or wrapper-typed). The thread-local remains in place
  for `READPLACE_LIFT_ENABLED`'s structural purpose (skipping the
  `ReadPlace` lift when the inlining context's BinderCtx is empty
  and value_subst doesn't hit), but the over-wrap concern that
  originally motivated it is gone. Could be removed if a future
  refactor unifies the inlining and standalone-rendering paths
  with one BinderCtx convention. Lower priority than it was.

**Alternatives considered + rejected** (2026-05-20):

- **Filter cross-crate redundant blanket impls** (small
  triage). Skips instances whose Self peels to bare typ-param
  and whose body is pure forwarding. Would unblock the
  vec_index probe by removing emission noise. **Rejected as a
  standalone landing** because (a) it doesn't address the
  underlying semantic gap, and (b) the gap surfaces in user
  code too, not just vstd. If a future session needs the
  vec_index unblock urgently and the un-peel work hasn't
  landed, the filter is reasonable as documented triage.
- **Skip the cross-crate blanket impls entirely** (no filter,
  just don't emit). Cleaner-looking output but loses the
  bound-derivability story — emit-time decisions about which
  instances to declare get coupled to assumptions about which
  call sites will dispatch through them. Rejected.
- **Inline forwarding instance bodies** (replace standalone
  forward-call with direct inline body). Tried for Bug A
  (2026-05-17 session); broke 5 proof-fn tests whose tactics
  expected one-step `simp_all [Trait.method]` unfolding.
  Rejected then; still rejected.

### Blanket-impl assoc-type passthrough (Bug B, LANDED 2026-05-19)

Blanket impls like vstd's

```rust
impl<A: View> View for &A {
    type V = A::V;
    spec fn view(&self) -> A::V { (**self).view() }
}
```

express assoc-type passthrough via projections — `<A as View>::V`
appears in the impl method's return type, the assoc_type_impl's
value, and the instance's positional V slot. The outParam encoding
we emit for traits (`class View (Self : Type) (V : outParam Type)`)
makes V a *unification variable*, not an *accessor* — so a literal
`View.V A` rendering of the projection is malformed.

**Two-step fix.** Implementation split into orthogonal pieces, each
small and standalone.

*Step 1 (`bbadec0`): VIR-level type-aware sibling rewrite.* The
prior LExpr-level `strip_class_qualifier` rewrote every
`Trait.method` ref in an instance method body regardless of the
call's receiver. Correct for non-blanket impls (the only call to
`Trait.method` IS on Self), wrong for blanket impls where the
body's `View::view(self.0)` dispatches on `self.0 : A` — a
different instance, NOT a sibling self-reference. New
`rewrite_self_sibling_calls` walks the body at VIR level and checks
the call's first-arg type against `ti.trait_typ_args[0]` (peeling
transparent `Decorate`/`Boxed` wrappers); rewrites only when they
match. Non-blanket impls render exactly as before — backwards-
compatible. Blanket impls keep class dispatch for cross-instance
calls.

*Step 2 (`6f22676`): per-impl projection substitution.* New module
`impl_subst.rs`. `ImplSubst { fresh_binders, fake_bounds,
proj_map }` is built once per impl from the union of impl signature
typs — trait_typ_args, assoc_type_impl values, each method's
ret/param typs. For each `<X as T>::N` projection where X is in
`impl_typ_params` and there's a `Trait(T, [X, ...])` bound,
allocate a fresh `_tactus_assoc_<X>_<N>` binder, synthesise a
`GenericBoundX::TypEquality(T, [X], N, TypParam(fresh))` bound, and
record the projection→fresh-binder mapping. Apply at:

- `trait_impl_to_ast` (instance side) — extend binders with
  `fresh_binders`, prepend `fake_bounds` to `ti.typ_bounds` before
  `trait_bounds_to_ast`, rewrite `trait_typ_args` and
  `assoc_types[i].typ` via `rewrite_typ`.
- Impl method standalone def emission via `maybe_augment_impl_method`
  in `generate.rs`'s `FnGroup` iteration — augmented `FunctionX`
  flows unchanged through `spec_fn_to_ast`.

**The "fake TypEquality bound" insight.** `trait_bounds_to_ast`
already iterates bounds looking for matching `TypEquality` entries
and appending their typs to the rendered trait-arg list (that's the
existing mechanism for `where A::V = SomeType` constraints).
Synthesising a `TypEquality` with `TypParam(fresh)` on the RHS
piggybacks on that machinery — the fresh-binder TypParam flows
through the same path as any user-written equality, with no new
code in the bound renderer. The data flow stays explicit (no
thread_local, no ambient `@[simp]` on standalones); existing
machinery does the load-bearing work.

**Scope: signature only.** Bodies are NOT walked. The body of
`view` is `self.0.view()` which renders to `View.view self.val0`
— no projection in the rendered Lean (Lean infers V from class
dispatch via the augmented `[View A _tactus_assoc_A_V]` bracket).
Signature-only scope kept the rewrite localised to two
`trait_impl_to_ast` call sites and the spec_fn-impl-method path —
no invasive changes to `vir_expr_to_ast` or the SST renderer.

**Generated Lean.** For `impl<A: View> View for Wrap<A>`:

```lean
noncomputable def impl__0.view (A : Type) (_tactus_assoc_A_V : Type)
  [View A _tactus_assoc_A_V] (self : Wrap A) : _tactus_assoc_A_V :=
  View.view self.val0

noncomputable instance {A : Type} {_tactus_assoc_A_V : Type}
  [View A _tactus_assoc_A_V] : View (Wrap A) _tactus_assoc_A_V where
  view := fun (self : _) => View.view self.val0
```

Pinned by `test_view_blanket_impl_probe` (same-crate Wrap blanket
impl). Unit-tested in `impl_subst::tests` (10 tests covering
`build` for the typical cases, including dedup, multi-typ-param,
and skip cases for non-typ-param projections and non-matching
bounds; plus `rewrite_typ` for identity and replacement cases).

**Walked considered alternatives** (documented for the next time
someone considers a uniformly-nice fix):

* **V-as-field encoding** (switch class to `class View (Self : Type)
  where V : Type; view : Self → V`). Loses outParam's instance-search
  behavior — Lean's elaborator doesn't reduce class field projections
  during typeclass search, so `OfNat (View.V (Wrap Holder)) 7` fails
  to synthesize even though the projection definitionally equals
  `Int`. outParam is load-bearing, not decoration.

* **Forward-call instance bodies** (always emit instance method as a
  thin forward to the standalone def). Broke 5 proof-fn tests whose
  tactic bodies do `simp_all [Foo.predicate]` and expect one unfold
  to reach the impl body — forward-call inserts an extra
  `impl__N.predicate` step that simp_all doesn't chain through.
  Fixing this with `@[simp]` on standalones would violate DESIGN
  principle #1 (Transparency) by adding silent unfolding the user
  can't see.

Both alternatives ruled out by Lean semantics + DESIGN.md
principles before the targeted two-step fix landed.

#### Known UX limitation: `impl__N.method` naming leak

The standalone-def pattern (Tactus + Mathlib both use it) has a
user-visible cost: when a user's tactic unfolds a class method via
`simp_all [Trait.method]`, simp unfolds Counter.method via the
instance to the field body — which references the standalone def
(`impl__N.method` in Tactus's current naming). simp doesn't
auto-bridge that further unfold; the user must add
`impl__N.method` to their simp set.

The leakage surfaces in the goal state: `impl__0.raw { v := 3 } +
impl__0.raw { v := 3 } = 6`. The user reads the goal, recognises
the unfamiliar name, and (eventually) realises they need to add it
to the simp list.

Mathlib has the same problem in principle but with naturalish
names: `Bar.raw`, `Real.mul`, etc. — the standalones live in the
type's namespace and read as ordinary library functions. Tactus's
auto-generated `impl__N.method` reads as an obvious emission
detail and offers no hint about which trait/method/type it
belongs to.

**Considered fix: `@[reducible]` on impl method standalones
(probed 2026-05-19, RULED OUT).** Hypothesis: marking the
forwarders `@[reducible]` lets simp see through them as
"transparent aliases" (analogous to how `abbrev` works), so
`simp_all [Counter.method]` unfolds the class method via the
instance, lands on `impl__N.method`, and continues through to the
body. The hypothesis was wrong: Lean 4 `simp` doesn't delta-reduce
reducible defs by default. `@[reducible]` controls reducibility
for the *elaborator* and *typeclass search*; `simp`'s
normalization phase is more conservative and won't unfold a
reducible def absent an explicit `simp [name]` listing or
`@[simp]` annotation. Pinned empirically by the
`test_impl_method_sibling_call_in_body_probe` failing the same
way pre- and post-`@[reducible]` emission. `@[simp]` would work
but violates principle #1 (silent rewrite-rule extension); we
took the lesson and reverted.

**Landed 2026-05-19: rename impl method standalones to
`<Self>.<Trait>.impl.<method>`.** The user-side simp-listing
requirement remains (the chain `Counter.method → standalone-body`
still needs the standalone in the simp set), but the name is now
**discoverable from the goal state**: `MyList.Container.impl.length
{ n := 0 } = 0` reads naturally enough that a user can infer the
name to add. `impl__0.length` was a black-box synthetic name.

**The `impl` marker is load-bearing**, not aesthetic. Without it
(`<Self>.<Trait>.<method>`), inside `def Wrap.View.view`'s body
Lean's namespace resolution finds the def itself before reaching
the trait class method — `View.view` looked up at namespace
`Wrap` resolves to the def at `Wrap.View.view` (recursive
self-reference, wrong type). Adding `impl` as a middle segment
breaks the namespace chain at exactly the right place. Lean
climbs past `Wrap.View.impl` and `Wrap.View` (no `view`
declaration at either), reaches the outer `test_crate` scope,
and finds the class method.

**When this fires in real code:** ANY trait where an impl method
delegates to a sibling — `Container { length, is_empty }` with
`is_empty := length() == 0`, `Iterator { next, peek }`,
`Display { write, write_with_prefix }`, etc. Textbook Rust API
pattern. Pinned by
`test_impl_method_realistic_is_empty_probe`: tactic is
`simp_all [Container.is_empty, Container.length,
MyList.Container.impl.length]`. The third name is the standalone
def's path — discoverable from the goal state's
`MyList.Container.impl.length { n := 0 } = 0`.

**Collisions**: handled by construction for the common cases
(different traits → different paths; inherent vs trait → distinct
paths since inherent keeps Verus's `impl__N.method` emission). The
remaining edge case — `impl Foo<int> for Bar` and `impl Foo<bool>
for Bar` both mapping to `Bar.Foo.impl.method` — is detected
and falls back to `impl__N.method` for those impls. Logic in
`generate.rs::krate_preamble`'s `impl_name_prefixes` computation.

**Implementation locality**: the rename is contained to
`impl_subst.rs` (no thread_local, no krate-wide path mutation).
- `MethodContext::name_prefix: Option<Vec<Ident>>` carries the
  per-impl prefix (or `None` for collision fallback).
- `set_method_context` pre-renames `method_redirects` values to
  the renamed `Fun` so sibling-call rewrites produce the natural
  name without extra plumbing.
- `augment_function` rewrites the FunctionX's `name` field.
- `to_lean_fn::trait_impl_to_ast` consumes
  `subst.method_context.method_redirects` (the pre-renamed map)
  as its single source of truth for sibling redirects.
- Bug C's synth body (uninterp impl methods) consults
  `method_redirects` for the renamed `Fun`'s path.
- `to_lean_type::type_short_name` peels Decorate/Boxed/MutRef to
  derive the `<Self>` segment; falls back to `None` for shapes
  without a clean type name (closures, anonymous tuples), in
  which case the impl-method's prefix is omitted and it keeps
  the original `impl__N.method` path.

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

**15. Magic-string lens.** *For every string literal that appears in
two or more places with shared semantic intent, is it a `pub const`
referenced from all sites — or duplicated as a magic string?* Tests
asserting on error-message text are the canonical offender: the
error site and the test share the *meaning* of the message, so
phrasing edits should percolate from one to the other automatically.
The fix is a shared `pub const` (Tactus puts user-facing messages in
`vir::tactus_messages`); the anti-pattern is `.contains("the exact
phrasing I wrote in the error site")` in tests, which silently breaks
or — worse — silently tests something different when the error text
is edited.

*Categories the lens distinguishes:*
* **Tactus-controlled strings** (error messages we emit, theorem-name
  prefixes, attribute names) → extract `pub const`, reference from
  both emission and assertion.
* **Upstream-emitted strings** (Lean diagnostics like `"unsolved
  goals"`, Verus errors like `"postcondition"`) → outside our control;
  use stable substrings that survive upstream phrasing edits.
* **Dynamic-content strings** (e.g., `format!("got '{}'...", value)`) →
  extract a stable tag prefix as a `pub const`, use as the search
  substring; the dynamic part composes with it.

*Canonical hit*: the heartbeats error message was inline in both
`get_heartbeats_arg` and the negative test. Extracted to
`vir::tactus_messages::HEARTBEATS_ARG_ERR` (#123 review-pass,
2026-05-11) — phrasing edits now percolate to the test automatically.

#### Process

Land the work with tests passing, then run lenses 1–5 minimum.
Triage each finding (fix now / file follow-up / skip), do the
"fix now" list in a follow-up commit labelled "review (lens-name)".
Update this document for any caveat, deferral, or new lens that
surfaced.

When time allows, also run lenses 6–15. Even on code that passed
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

**Where this discipline applies (landed and outstanding).**
* **Deeper field paths** (`&mut a.b.c`) — LANDED via #144. Extends #87's structure-update pattern recursively: `let a := { a with b := { a.b with c := <fresh> } }`. No havoc encoding.
* **Tuple field mutation** (`&mut t.<i>`) — LANDED via #145 (arity-2) + #146 (arity > 2). Lean's `{ x with f := v }` syntax doesn't compose with `Prod`, but Lean's tuple syntax `(a, b, c)` does — it's `Prod.mk` sugar that infers from operands without a type hint. The rebind reads each unmodified slot via `tuple_field_accessor(arity, j)` (multi-segment for nested-Prod arity > 2: `.2.1`, `.2.2.1`, etc.) and substitutes `fresh` at the mutated slot. New `ExprNode::Tuple` AST variant; the latent rendering bug at let-bindings (`let t := ⟨x, 0⟩` failing to elaborate without context) was masked because no arity > 2 tuple test existed pre-#145.
* **Multi-variant enum field mutation** — upstream-blocked at Verus. Direct `&mut foo.f` for enum-typed `foo` isn't expressible in Rust without unsafe; the only viable shape (pattern binding `if let Foo::A { ref mut val }`) is rejected by Verus's mode check ("does not yet support &mut types"). If it ever lifts, the encoding is `match foo with | Foo.A x y => Foo.A fresh y | other => other` — a specific Lean idiom, not a havoc.
* **Closures (#93)** target Lean's first-class function types directly rather than encoding the FnOnce/Fn/FnMut hierarchy as Z3 axioms. Closure declarations bind `cid` to a real Lean lambda (`fun (x : T) => body`) via `Wp::LetRaw`; calls to spec closures lower to `App(f, args)`. Verus's synthesized `Assume(forall|x| ClosureReq(cid, x) ↔ ... ∧ ClosureEns(cid, x, body(x)) ↔ ...)` is dropped because the lambda binding IS the same fact structurally — no axiomatization needed. The only piece this encoding doesn't yet cover is exec-mode closure CALLS (Verus's `exec_nonstatic_call` desugar), which is upstream-blocked rather than encoding-shaped.
* **Indexed L-values (`&mut v[i]`)** — the rebind story is structural without any Tactus-side work, contrary to the earlier sketch. Verus's `rust_to_vir_expr` already desugars `&mut v[i]` (in new-mut-ref mode) to `vec_index_mut(&mut v, i)`, and `vec_index_mut`'s spec uses `final(vec)@ == old(vec)@.update(i, *final(element))` — `Seq::update` IS the "this index unchanged for j ≠ i" property structurally. The `&mut v` arg is Var-shaped, so `MutTargetRaw::Var` handles it; the ∀-path's existential post-state plus the inlined `Seq.update`-shaped ensures gives exactly the Lean-native encoding we'd want. No `Vector.set` encoding, no havoc, no new `MutTargetRaw` variant. The actual blockers (probed 2026-05-17) are cross-crate `View` trait+instance emission bugs — sub-task of #122. Plus a pre/post substitution bug in the inlined ensures.
* **Caller-side new-mut-ref mode (#107)** — synthetic `LocalDeclKind::BorrowMut` locals from Verus's `bump(&mut y)` lowering are folded into the existing `mut_param_names` set; same architectural pattern as #95 callee-side, applied one layer further. The structural insight: extend recognition rather than build new infrastructure.
* **Ret-substitution at call sites (#128)** — when a callee's ensures contains `r == E` (uniquely determining the return value), the caller's post-call frames *don't* need a `∀ ret, ret_bound → ensures(ret) → let dest := ret;` chain. Tactus replaces it with `let dest := E; (E_bound) → (ensures with ret := E) → …`, eliminating the ∀-quantifier entirely. Verus's Z3 path emits the ∀ because SMT can't natively substitute a logical variable with a witnessing expression — the ensures clause acts as the substitution glue. Lean substitutes definitionally via `let`. Same fact, structural rather than asserted. Beyond aesthetics: the ∀-Prop shape blocked `tactus_auto`'s default closer (omega rejects ∀-Prop). #128's substitution path makes cond_setup goals (function-call-in-loop-cond) close under the default closer with no override needed — see "Ret-substitution at call sites (#128)" below for the full encoding details.
* **loop_isolation=false's natural-exit fact (#127)** — Verus's `ast_to_sst` break-lowers `while c { body }` with isolation=false to cond:None + inserted `if !c { break; }`. AIR's `Breakable` primitive preserves state across the break, giving post-loop access to the natural-exit fact `¬c`. Lean's kernel has no control-flow-with-state-preservation primitive; we can't mirror AIR's encoding directly. Instead: preserve the pre-lowering `(cond_setup, cond_exp)` in upstream `StmX::Loop.original_cond`, and have Tactus's `build_wp_loop` recover the cond:Some shape from it (under single-break and label/setup gates that preserve soundness). The existing cond:Some encoding then gives the natural-exit fact via standard while semantics — Lean-native, not a re-encoding of AIR's primitive. The structural insight: don't reproduce a target-specific primitive; preserve the source-level info that the primitive was reconstructing.
* **Old context swap for pre-state substitution (2026-05-26)** — Verus's SMT encoding for `*old(h)` in inlined ensures uses an uninterpreted `MutRefCurrent` function call whose meaning is fixed by the call's post-axiom. Z3 reasons symbolically: `MutRefCurrent` of a forward-referenced state evaluates correctly when the surrounding constraint set forces it. Lean has no uninterpreted-function bookkeeping equivalent — collapsing `MutRefCurrent` syntactically loses the pre/post distinction. Mirror would mean defining a `MutRefCurrent` axiom in `TactusPrelude.lean` plus per-call equation hypotheses. **Lean-native answer**: `RenderCtx::value_subst` for post-state refs + `RenderCtx::value_subst_pre` for pre-state refs + `with_pre_state_subst()` that swaps the active map at the `ExprX::Old(_)` arm during the recursive render. Storage typs match between maps (both at the local's wrapper typ); only the value differs. Inside `Old`, every Var/ReadPlace lookup hits the pre-state map; outside, the post-state map. The pre/post distinction is encoded by which map is active, not by uninterpreted function semantics. See `with_pre_state_subst` in `expr_shared.rs` and the `ExprX::Old(_)` arm in `to_lean_expr.rs::expr_to_node`. Pinned by Cluster A's test artifacts (the difference between vacuous `post = post + 1` and semantic `post = pre + 1`); see the "Historical: new-mut-ref False-hypothesis silent miscompile" entry in § "Soundness trade-offs accepted" for what this fixed.
* **Typed render-time substitution + universal call-arg bridging (2026-05-26 cont.)** — Verus's SMT encoding handles "wrong typ at substitution slot" via Z3's untyped term language: bare values flow into wrapper-typed slots and Z3 just propagates without coercion. Tactus's Lean target uses real distinct types (`Tactus.Ref T` vs `T`), so substituting a bare-typed caller arg into a wrapper-typed callee slot produces a Lean type error. Mirror would mean post-render `lean_ast::substitute` plus an attempt to track types lexically (brittle, lossy at every substitution boundary). **Lean-native answer**: pre-render typed substitution via `RenderCtx::value_subst` (entries are `(LExpr, source_typ)`), where each lookup at a Var/ReadPlace site bridges from source_typ to slot_typ via `coerce_lexpr`. Combined with universal call-arg bridging — every fn call (class method, inherent method, regular fn, recursive call) consults `RenderCtx::fn_param_typs` and bridges each arg to the callee's expected param typ via `coerce_lexpr` — this codifies Rust's auto-borrow semantic explicitly in the generated Lean. The wrap is visible at the call site, no special-casing per dispatch kind. See `caller_arg_actual_typ` in `sst_to_lean.rs` (computes the rendered arg's actual Lean typ from caller's body-shadow context), `add_param_subst_entries` (populates typed `req_value_subst` / `ens_value_subst` maps), and the `coerce_lexpr` call in both renderers' `Call` arms. Closed Cluster A (`test_old_view_pre_post_substitution_probe`, `test_old_view_trait_dispatch_probe`) — generated Lean now reads `impl__0.view (Tactus.Ref.mk z)` instead of bare `impl__0.view z`, with the wrap explicit and identical for both inherent and trait dispatch.

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
