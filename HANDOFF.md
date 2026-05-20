# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions, including a comprehensive "Known deferrals, rejected cases, and untested edges" catalogue.

## Current state

**435 end-to-end tests + 1 coverage test + 209 lean_verify unit tests + 66 rust_verify unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

**Track B status: all seven slices landed.** Exec fns can have: `let`-bindings, mutation (via Lean let-shadowing), if/else, early returns, loops (arbitrary nesting — sequential, nested, inside if-branches), function calls (direct named, including recursion and mutual recursion via Verus's `CheckDecreaseHeight` obligation), break/continue, recursion on user datatypes via generated `T.height` fn, enum match via `tactus_case_split` automation, and arithmetic with overflow checking. Failures cite Rust source positions with semantic kind labels. Most realistic Rust exec fns should verify, modulo documented restrictions (no trait-method calls, no `&mut` args — see DESIGN.md § "Known deferrals").

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

#### Current session (2026-04-25 — non-int decreases, match automation, source mapping, AST tightening)

Three roadmap tasks completed (#54, #58, #51), one started (#55 first slice), plus three architectural cleanup passes. Grouped by theme:

**Tier 2 / Tier 3 landings:**
- **#54 non-int `decreases`** (`91ee7f0`, `6655abf`) — first slice pinned the rejection with a clear error naming the task and an int-valued workaround; MVS lands `T.height : T → Nat` companion fn per concrete (non-generic) datatype. `decrease_height_datatype` peels Boxed/Decorate to find the underlying datatype path; `CheckDecreaseHeight` lowering dispatches to `T.height cur < T.height prev ∨ ...`. `deriving Inhabited` added to every non-generic datatype to satisfy accessor `default` fallbacks for self-referential types like `enum Stack { Empty, Push(u8, Box<Stack>) }`. Deferrals documented: generic datatypes, mutually-recursive SCCs, recursive function fields, lexicographic decreases.
- **#58 match automation** (`81dbe19`) — `tactus_case_split` elaborator tactic in `TactusPrelude.lean` finds a user-datatype-typed local and case-splits it. "User datatype" gated on having a companion `.height` fn (which `height_fn_for_datatype` emits for every concrete datatype, so it doubles as a whitelist) — filters out `Int`/`Nat`/`Bool`/etc. Closed the test_exec_match_enum_automation_gap regression. Also fixed a subtle `first | simp_all | ...` issue where partial-success tactics blocked later alternatives; all `tactus_auto` alternatives now wrap in `done`.
- **#51 source mapping for exec-fn errors** (`294fd49`, `c7d4f0c`, `865f727`, `bdc6bfa`, `0522494`, `83c6fd9`, `e6f4a6c`) — staged across multiple commits:
  - First slice (`294fd49`): `Wp::Assert` wraps its expression in `ExprNode::SpanMark { rust_loc, inner }` using `e.span` formatted via `format_rust_loc`. Pp emits `/- @rust:LOC -/` block comments before the marked expression.
  - Coverage extension (`c7d4f0c`): `Wp::Loop.invs` / `decrease`, `Wp::Branch.cond` also wrapped.
  - Call-site span (`865f727`): `Wp::Call` carries `call_span`; `lower_call` wraps `requires_conj` so failing preconditions surface the call site rather than the callee's source line.
  - Right-way migration (`bdc6bfa`, `0522494`): replaced `lean_verify`-side `as_string` parsing with structured `Span::start_loc` field populated at `rust_verify::spans::to_air_span` time via `SourceMap::lookup_char_pos` (passed as `&SourceMap` parameter to `to_air_span`, threaded through `ContextX::to_air_span` / `BodyCtxt::to_air_span` wrappers — Arc<SourceMap> attempt failed because rustc's SourceMap isn't Sync). Output cleaner too: `at test.rs:28:5:` instead of `at test.rs:28:5: 28:5:`.
  - Architectural pass (`83c6fd9`): replaced post-pp `scan_span_marks` with direct push during emission via `&mut Landmarks` threaded through ~12 `write_*` functions. Eliminated the path-with-`-/` fragility and O(n × m) scan cost. Also wrapped `Wp::Loop.cond` for completeness, and extracted structural `lean_ast::strip_span_marks` helper for `pp_eq` tests.
  - AssertKind labels (`e6f4a6c`): `ExprNode::SpanMark` extended with `kind: AssertKind` carrying obligation class (Plain / LoopInvariant / LoopDecrease / LoopCondition / BranchCondition / CallPrecondition / Termination). Each lowering site sets the appropriate kind. `format_error` produces `at <loc> (<kind label>):`. Known imperfection documented: Lean's `pos.line` is the failing tactic invocation line, not the obligation's position in the goal tree, so `find_span_mark` returns the closest preceding mark which may be one off when the failing obligation isn't the latest mark. Architectural fix is per-obligation theorem emission (D, planned next).
- **#55 first slice** (`8920937`) — rejection error at `build_wp_call`'s `contains_loc` check now names the task and suggests the refactor-to-non-mutating workaround. MVS implementation plan documented in DESIGN.md.

**Right-way followups (cleanup pass):**
- **Curried `T.height`** (`ad5b37c`) — switched from match-on-binder to curried form (the Lean-idiomatic shape for structural recursion; equation compiler is built around it). Initially via `Command::Raw`; later promoted to first-class `Command::DefCurried` AST variant.
- **`tactus_first` combinator** (`ad5b37c`) — abstracts the per-alternative `; done` wrapping into a named combinator. Closure contract lives at the combinator name, not as boilerplate trailing every alternative.
- **`tactus_case_split` tries each candidate** (`ad5b37c`) — takes a `closer` tactic argument, tries each user-datatype local until one + closer closes all subgoals. Fns with multiple datatype locals work regardless of which is the right scrutinee.

**AST tightening pass** (`1e9233a`):
- `peel_typ_wrappers` moved from `to_lean_sst_expr.rs` to `to_lean_type.rs` (lives next to `typ_to_expr` and other type helpers).
- `Span::dummy()` constructor centralizes the previously-inlined 5-field literal used in test fixtures.
- `PpOutput { text, landmarks: Landmarks }` nested — `tactic_starts` and `span_marks` were flat siblings, now correctly grouped.
- `LeanSourceMap` split into `ProofFn { fn_name, tactic_start_line, tactic_line_count }` / `ExecFn { fn_name, span_marks }` enum variants — explicit dichotomy instead of one struct with conditionally-meaningful fields.
- `Command::DefCurried` AST variant — replaces the earlier `Command::Raw` text emission of `T.height` with structured AST + first-class pp + sanity-check coverage.

**Five-lens review pass** (`e493e45`):
- Documented the silent `catch _` in `tactus_case_split` (was raising "is this hiding bugs?" question for readers).
- Fixed stale comment in `format_rust_loc` claiming "splits from the right" while code splits left-to-right.
- Added 4 unit tests for `format_rust_loc` covering field-vs-fallback logic.
- Extracted shared `peel_typ_wrappers` helper — the Boxed/Decorate peel was duplicated across `is_int_height`, `decrease_height_datatype`, `field_is_self_recursive`. One edit site if Verus adds a new transparent wrapper.

**Writing** (`8c689b0`) — three poems in POEMS.md: "done" (the `first` semantics surprise), "The gate" (the `.height`-existence whitelist for tactus_case_split was already built for #54 before #58 needed it), "Downstream" (estimates vs actuals, and the foundation work that hides in the visible hour).

#### Current session (2026-04-26 — task D: per-obligation theorem emission)

Task D landed across six staged commits. Replaces the single
`_tactus_body_<fn>` mega-theorem per exec fn with one theorem per
obligation. Each theorem gets its own `pos.line` in Lean, so
`find_span_mark` becomes structurally exact for AssertKind labels —
the imperfection from #51 (Termination check on a recursive call
mislabeled as `(precondition)` because `find_span_mark` returned
the next mark in source order) is now fixed by construction.

**Stage 1** (`5d4b954`) — `walk_obligations` walker handling
`Wp::Done` / `Assert` / `Let` / `Assume` / `Branch` per-obligation.
Accumulates context as `OblCtx` (Let / Hyp / Binder frames),
wrapped around each emitted goal in source order so lets scope
over the hypotheses that mention their bindings. Theorem naming
compresses spans to `<basename>_<line>_<col>`.

**Stage 2** (`f937733`) — `walk_call` for `Wp::Call`. Emits one
theorem for the call's substituted requires (kind=CallPrecondition),
continues with `∀ ret, ret_bound → ensures(subst) → let dest := ret;`
frames pushed onto the obligation context.

**Stage 3** (`ee94bce`) — `walk_loop` for `Wp::Loop` + Done leaf
splitting. Emits one theorem per loop invariant at entry, walks
body in maintain ctx (mod_var binders + bounds + invs as hyps +
cond as hyp + `_tactus_d_old := D` let), walks `after` in use ctx.
The body's `Done(I ∧ D < d_old)` flows through `Wp::Done` →
`emit_done_or_split`, which splits top-level conjunctions into
one theorem per conjunct. Each invariant + the decrease comparison
are wrapped in SpanMarks at build time, so the per-conjunct
theorems get exact AssertKind names: `_tactus_loop_invariant_*`,
`_tactus_loop_decrease_*`, etc.

**Stage 4** (`b6133ab`) — `walk_assert_by_tactus` for
`Wp::AssertByTactus`. `cond=Some(P)` (assert-by) emits one theorem
for `P` with the user's tactic as closer; body theorems get `P` as
a Hyp frame. `cond=None` (proof block) pushes the user's tactic
onto `e.tactic_prefix` so every body theorem gets `(tac) <;> closer`
— `<;>` rather than `;` so a goal-modifying `simp_all` that closes
the goal entirely no-ops the closer instead of failing with "no
goals". Plus a ~550-line dead-code cleanup: `lower_wp` /
`lower_loop` / `lower_call` / `quantify_mod_vars` / `loop_tactic` /
`Wp::needs_peel` / `collect_tactus_haves` / `prepend_user_haves` /
`TactusHave` all removed (replaced by the per-obligation walkers
and the `tactic_prefix` stack on `ObligationEmitter`).

**Stages 5 + 6** (`4156079`) — `find_span_mark` docstring updated
to record that closest-preceding-mark is now structurally exact
under per-obligation emission; AssertKind regression tests added
to `test_exec_call_recursive_nondecreasing` (`(termination)` label),
`test_exec_loop_invariant_fails` (`(loop invariant)`),
`test_exec_call_requires_violated` (`(precondition)`); new
`test_exec_proof_block_have_propagates_to_assert` exercises the
Stage 4 tactic-prefix propagation.

**Side effects of per-obligation:** Lean now sees ~3-5x more
theorems per fn on average. Each is small (a single obligation
with its accumulated context), so `omega` / `simp_all` are fast
on each. Total verification time is roughly the same. Generated
`.lean` files are bigger but still tractable for inspection.

#### Current session (2026-04-26 continued — D review passes)

After D landed, six subsequent review/cleanup passes surfaced
non-trivial findings each. Documented as a discipline lesson:
no single read-through catches everything because each pass
filters through a different question.

**Five-lens review** (`2432eac`):
- Linus-hat: 11 stale comments referencing the deleted
  `lower_wp` / `lower_loop` / `lower_call` / `needs_peel` /
  `loop_tactic` / `BodyItem` machinery — module-top docstring,
  section headers, every `Wp` variant doc.
- FP lens: documented `OblCtx::with_frame`'s O(N²) clone cost
  (not urgent at realistic exec-fn sizes).
- Coverage: 3 new tests — loop INIT failure path, assert-by
  with failing tactic, `(loop decrease)` label pinning.
- DESIGN.md global rename of `lower_*` → `walk_*`; obsolete
  `loop_tactic` / `needs_peel` bullets removed.

**"Right way" pass** (`5fd39e5`) — addressed three findings the
five-lens pass missed because they needed a different question
(*what could be done right that we accepted as imperfect?*):
- **P0 correctness bug** — empty `proof { }` and `assert(P) by
  { }` produced broken Lean syntax (`( ) <;> tactus_auto` and
  `:= by` with nothing after). `walk_assert_by_tactus` now
  skips whitespace-only prefix pushes (proof-block path) and
  falls back to `simple_tactic()` when the user's tactic is
  whitespace-only (assert-by path).
- **AssertKind cleaner split** — added `Postcondition` kind +
  `is_obligation_kind()` method on AssertKind, splitting kinds
  into obligation-firing vs hypothesis-only. `find_span_mark`
  filters non-obligation kinds; LoopCondition / BranchCondition
  now provide `/- @rust:LOC -/` comments only, never error
  labels. Each ensures clause wrapped with Postcondition
  SpanMark in `WpCtx::new`, so multi-clause ensures yields
  per-clause Postcondition theorems via `emit_done_or_split`.
- **`emit_done_or_split` peels Let** — `let r := x; SpanMark(...)`
  was hiding the obligation kind from the leaf-extraction path.
  Now peels the Let into an OblCtx frame and recurses on body,
  exposing the SpanMark for kind/loc extraction.
- **P1 cleanups**: skip empty-requires precondition theorem,
  skip `Hyp(True)` frames in walk_call, reuse cond_ast in
  Wp::Assert (one less redundant `sst_exp_to_ast` call).
- **P3 unified naming**: `build_theorem_name` helper drops the
  `_at_<suffix>` part when loc is empty (no more
  `_tactus_assert_<fn>_at__7` double-underscore names).
- 7 new e2e tests pinning `(postcondition)` / `(precondition)` /
  `(loop invariant)` / `(loop decrease)` labels + empty
  proof-block / empty assert-by / multi-clause-ensures-with-one-
  failing / loop-use-clause-failure / conjunctive-assert.

**Test isolation fix** (`984caa8`) — discovered while debugging
the multi-clause requires test: `cargo test`'s inherited
`CARGO_TARGET_DIR` was pointing every test's Tactus output
at the shared `<rust_verify_test target>/tactus-lean/test_crate/
<fn>.lean` path. Tests with same fn name + different content
raced in parallel runs. Pre-D this was masked by content
homogeneity (most identical-name fns had identical bodies);
per-D made writes distinctive enough to surface as flakes.
Fix: `run_verus` and `run_cargo_verus` set
`TACTUS_LEAN_OUT=<test_input_dir>/tactus-lean` per-test. 4
consecutive full runs all green with the previously-colliding
`fn five` and `fn caller` restored. Documented in HANDOFF.md
"Per-test isolation" with the regression-detection symptom
(test passes alone, fails in suite, different test fails next
run).

**Reasoning-clarity pass** (`fb94f78`):
- Extracted `peel_value_position` helper — the
  transparent-plus-Loc peeling duplicated (with shadowing
  `let-peeled`) in `walk_let` and `lift_if_value`.
- Extracted `match_single_let_bind` helper — replaces the
  awkward `matches!`-guard + `let-else` re-destructure pattern
  with a clean `if let Some((name, rhs, body))`.
- `kind_to_name(AssertKind::…)` everywhere instead of literal
  strings — single source of truth for kind names.
- `OblCtx::wrap` doc gets a worked example showing why
  reverse-iteration produces correct scope ordering.
- `emit_done_or_split` shape unified into a single match (was
  early-return + fall-through emit).

**Final review pass** (`1ac7581`):
- 9 more stale doc references to deleted lowering pass —
  `walk_loop` / `walk_call` / `walk_let` doc strings, the
  `CtxFrame::Binder` "Stage 2 will / Stage 3 will" framing,
  `build_param_binders` "init / maintain / use" loop-specific
  framing, `StmX::AssertQuery` comment describing the OLD
  collect-haves-and-prepend approach.
- Removed redundant `let name = name.to_string()` in
  `lift_if_value` (was shadowing an already-`String` from
  `match_single_let_bind`; survived three review passes
  because it *looked* like reasonable closure-ownership setup).
- Defensive: `run_cargo_verus` also sets `TACTUS_LEAN_OUT` for
  future-proofing (no current Tactus tests use that path, but
  adding one would silently regress).

**Coverage audit** (`c6365ce`):
- 8 unit tests for the helpers extracted today: 6 for
  `peel_value_position` (plain / Box / Loc / Box+Loc / Loc+Box
  / doesn't-peel-If) + 1 for `match_single_let_bind` + 1
  comment-proxy for the negative case.
- 4 new e2e tests for paths that lacked coverage:
  - `test_exec_assert_fails` strengthened to pin
    `AssertKind::Plain`'s empty-label format (`at <loc>:`
    without parens). Regression guard.
  - `test_exec_proof_block_sequential` — two consecutive
    proof blocks exercise the `tactic_prefix` STACK with
    multiple entries, not just single-entry.
  - `test_exec_no_ensures` — the *only* reachable path to
    `emit_done_or_split`'s unwrapped fallback. Was untested;
    now has a witness.
  - `test_exec_call_no_requires_no_ensures` — exercises
    `walk_call`'s skip-precondition and skip-Hyp(True) paths.

**Writing** (3 commits in POEMS.md):
- (`5d2e8ee`) "Cheap" / "The label said precondition" /
  "Eighteen commits" — yesterday's rationalization, the #51
  imperfection, the day's commits.
- (`f663dc1`) "The mark that wasn't wrong" / "The semicolon
  that wasn't" / "Six commits, no rollbacks" — D landing.
- (`3572755`) "The race that was always there" / "Three
  sites" / "The mark that kept missing" — review pass +
  test isolation + the imperfection-fixed-via-two-insights.
- (`a768d8a`) "Six lenses" / "Looking reasonable" /
  "Witness" — the orthogonality of review lenses,
  prefabricated-explanations as camouflage, the gap
  between code-path-existing and code-path-tested.

**Net for the day**: 17 commits, ~1100 lines net change
(D itself added ~400, dead-code cleanup removed ~700, review
passes net-positive ~400 from added doc + tests). 13 new
tests across all the passes. 12 poems committed across the
broader cadence.

#### Current session (2026-04-27 — #55 caller-side &mut MVS)

`&mut` args at exec-fn call sites land. The DESIGN.md plan for
#55 was a sketch; implementation surfaced one structural wrinkle
the plan didn't anticipate (VarAt rendering), one course
correction (scoping the rewrite locally instead of changing the
renderer globally), and one slice-discipline call (callee-side
verification stays out of scope).

**What landed:**
- `walk_call` introduces a fresh existential `_tactus_mut_post_<id>`
  per `&mut` arg (the post-call value), substitutes
  `varat_pre_name(p) ↦ caller_arg` (pre-state) and `p ↦ Var(fresh)`
  (post-state) in the inlined ensures, then rebinds the caller's
  local to the fresh value via a `Let` frame placed AFTER the
  ensures `Hyp` so subsequent obligations see the post-call value.
- `rewrite_varat_for_mut_params` walks the VIR-AST `Expr` BEFORE
  rendering and renames `VarAt(p, Pre)` to `Var(<p>_at_pre_tactus)`
  scoped to the `&mut` param name set. Uses `vir::ast_visitor::
  map_expr_visitor` from upstream rather than rolling our own
  walker.
- `varat_pre_name` lives in `expr_shared.rs` so the rewrite (which
  produces the synthetic name) and the substitution-map key
  (which targets it) stay in sync — divergence would be a compile
  error, not a runtime mismatch.
- `Wp::Call` carries `mut_args: Vec<(usize, &VarIdent)>` —
  computed in `build_wp_call`, consumed in `walk_call`.
- `build_wp_call` validates: `&mut` arg must extract to a simple
  `VarIdent` via `extract_simple_var_ident`. `&mut x.f` /
  `&mut v[i]` rejected with a pointed error message naming the
  task and suggesting the extract-to-local workaround.

**Course correction worth recording.** First instinct was to make
the renderer distinguish `VarAt(x, _)` from `Var(x)` globally —
emit `<x>_at_pre_tactus` everywhere. That broke 54 tests because
`VarAt` is used outside `&mut` (loop ensures' at-entry refs),
where the natural collapse to `Var` is correct. The fix was to
revert the renderer change and do the rewrite locally at
substitution time, scoped by the `&mut` param name set. The
renderer is general; the rewrite is specific. Documented in DESIGN.md
"Tier 3 — `&mut` args on calls".

**Slice scope (caller side only).** The fn's OWN body
verification when it takes `&mut` params is a separate concern.
For example, `bump(x: &mut u8) { *x = *x + 1; }` as `tactus_auto`
would need Tactus to bind `x_at_pre_tactus` at fn entry and
thread the post-state through body assignments. The MVS test
splits the responsibilities: `bump` goes through Verus's Z3 path
while `call_mut` (the caller) uses `tactus_auto` and exercises
the new caller-side encoding.

**Tests** (4 new, 1 renamed):
- `test_exec_call_mut_arg` (renamed from `test_exec_call_mut_ref_rejected`,
  flipped to `=> Ok(())`): single `&mut` arg, MVS happy path.
- `test_exec_call_mut_arg_wrong_post`: caller's ensures has +2
  instead of +1 → `(postcondition)` failure. Pins that
  substitution doesn't alias pre/post.
- `test_exec_call_mut_arg_requires_violated`: caller's `< 200`
  weaker than callee's `*old(x) < 100` → `(precondition)`
  failure.
- `test_exec_call_mut_arg_field_rejected` (Err): `&mut h.val`
  rejected — extract_simple_var_ident-fail path.
- `test_exec_call_two_mut_args`: two `&mut` args at the same
  call site exercise the stacked-frames encoding.

**Explicit deferrals** (rejected with clear messages):
- `&mut x.f` / `&mut v[i]` (non-simple `Loc` shapes) — needs
  havoc-base + assume-other-fields-unchanged encoding.
- New-mut-ref's `MutRefCurrent`/`MutRefFuture` UnaryOps — this
  slice handles legacy-mode `VarAt` only.
- Callee-side body verification with `&mut` params (separate task).

**Net for the day**: 3 commits (MVS, coverage tests, poems), ~430
lines added across 4 source files + DESIGN/HANDOFF/POEMS, 4 new
e2e tests + 1 renamed positive test. 193 e2e tests pass. Single
remaining pending task: #56 trait-method calls.

#### Current session (2026-04-27 continued — #56 caller-side trait method calls)

`DynamicResolved` trait method calls land. Statically-resolvable
trait method calls (the common case — concrete receiver type,
known impl) now route through `walk_call`'s standard inlining
path with one redirect: the callee lookup goes to the resolved
impl, but the spec source for `require/ensure` goes to the trait
method decl.

**What landed:**
- `build_wp_call`'s rejection of `resolved_method.is_some()`
  removed. When `resolved_method = Some((resolved_fun,
  resolved_typs))`, the resolved impl becomes the callee and
  `resolved_typs` becomes the type-args slice (Self filled in by
  Verus's resolution).
- `pick_spec_source(callee, fn_map)` redirects spec lookup to
  the trait method decl when callee is `TraitMethodImpl`.
  Reason: Verus rejects impl-side `requires` declarations, so
  the impl's require is empty; trait specs are inherited. Using
  the trait's spec is sound because Verus enforces impl ⇒ trait.
- Cross-crate trait method decls rejected at build time. If the
  resolved impl is `TraitMethodImpl { method, .. }` and `method`
  isn't in fn_map, `build_wp_call` fails with a pointed error
  naming `#56` deferrals.
- Existing rejection of `is_trait_default.is_some()` narrowed to
  `is_trait_default == Some(true)` only. `Some(false)` is fine
  (concrete impl on a trait that has a default — different from
  invoking the default itself).

**Tests** (3 new + 1 renamed positive):
- `test_exec_call_trait_method` (renamed from
  `test_exec_call_trait_method_rejected`, flipped to Ok): basic
  case — trait declares spec, single concrete impl, caller
  invokes through `&Id`.
- `test_exec_call_trait_method_requires_violated` (Err): pins
  that the trait's `requires` becomes the precondition
  obligation. `(precondition)` failure label.
- `test_exec_call_trait_method_two_impls`: same trait, two
  impls; caller relies only on the trait-level guarantee. Pins
  the impl-strengthening trade-off.
- `test_exec_call_trait_method_with_args`: trait method with
  non-self args; pins param-name alignment between trait decl
  and impl.

**Trade-off worth recording: impl-strengthening of `ensures`
not seen at call sites.** A trait with `ensures r < 100` whose
impl strengthens to `ensures r == 5` produces a call site that
sees only `r < 100`. Reason: we use the trait method decl's
`ensure.0` as the spec source, never the impl's. To see the
impl's strengthening would need a per-clause merge: pick the
strongest of (trait, impl) for each ensures clause. Deferred
follow-up.

**Explicit deferrals (rejected with clear messages):**
- `is_trait_default = Some(true)` — calls resolved to the
  trait's default impl (not a concrete impl). The default body
  uses `Self` as a parameter that needs further substitution.
- Cross-crate trait method decls — when the resolved impl's
  `method` Fun isn't in fn_map.
- Truly dynamic dispatch (`dyn Trait`) — indistinguishable from
  `Static` at the SST level (both have `resolved_method =
  None`); falls through to existing fn_map lookup. For
  same-crate `dyn Trait` the lookup succeeds; cross-crate
  hits the existing cross-crate rejection.
- Impl-specific strengthening of ensures (above).

**Net for the day so far**: 4 commits (#55 + #56 slices + docs).
196 e2e tests pass. #56 caller-side MVS landed.

#### Current session (2026-04-28 — deferrals batch + small features)

A focused day going through the deferrals catalogue. Twelve
tasks closed across coverage, small features, and one
architectural cleanup pass at the end.

**Tier 1 (test coverage)**:
- #76 bit-width matrix (u16/u64/u128/i16/i32/i64/i128 + 1
  negative). 8 tests.
- #77 control-flow combinations (return-in-else, 4-var loop,
  nested-if-with-loops). 3 tests.
- #79 lossy-accept paths (Xor, Choose, assert-forall-with-vars
  documented as upstream-panic). 2 tests + 1 comment-doc gap.
  Surfaced renderer divergence: SST hardcoded `"xor"` while
  VIR-AST went through the shared `non_binop_head` table —
  fixed both to route through `non_binop_head`. Then
  `non_binop_head` updated from `"xor"` to `"Bool.xor"` (dotted
  bypasses sanity allowlist; native Lean).
- #78 shape-drift + WpCtx + edge cases (name collision test).
  1 test, surfaced a real soundness bug.

**Soundness fix surfaced by #78**: when a callee's `ret.name.0`
matches a caller-scope local of the same sanitized name, the ∀-
binder we emit in `walk_call` shadowed the caller's local for
the post-call frames — subsequent uses of the caller's `r`
silently bound to the ∀-bound ret value. Fix: gensym the ret
name to `_tactus_ret_<id>` in `walk_call`; substitute the
callee's source ret-name → fresh in the ensures rendering. Six
lines.

**Tier 2 (small features)**:
- #80 `assume(P)` compile warning. `CheckResult` shape changed
  to carry `warnings: Vec<String>`. Walks the VIR-AST body
  (`vir_fn.body`) for `ExprX::AssertAssume { is_assume: true,
  .. }` (NOT the SST — synthetic StmX::Assume from overflow
  passes would false-positive).
- #81 per-fn tactic override `#[verifier::tactus_tactic("…")]`.
  Replaces the default closer for the marked fn's emitted
  theorems. `simple_tactic` now reads from `ObligationEmitter`
  rather than returning a hardcoded constant.
- #82 `tactus_usize_bound` tactic in TactusPrelude.lean.
  Discharges goals over `usize_hi` / `isize_hi` by case-splitting
  on `arch_word_bits_valid` and reducing the literal `2 ^ 32` /
  `2 ^ 64`. Composes with the per-fn override (#81).
- #83 gensym `_tactus_d_old` per loop. Same shape as today's
  ret-name gensym, six lines. Uses Verus's stable
  `StmX::Loop::id` (no codegen counter needed).

**Tier 3 (medium features, smaller end)**:
- #85 ExpX::Old investigation. The deferral was a wrong
  description: SST-level `ExpX::Old` is internal to Verus's
  AIR pipeline ("only used during sst_to_air") — user-syntax
  `old(x)` lowers to `ExpX::VarAt(x, Pre)` which Tactus already
  handles. Closed by writing better error messages and
  docstrings, no behavior change.
- #90 `BinaryOp::HeightCompare`. Dispatches by operand type:
  int-height → direct `<` / `=`; same datatype → `T.height` fn
  comparison.
- #92 `lift_if_value` + `walk_let` multi-binder support.
  Defensive — Verus's tuple destructure goes through
  Ctor + projection, not multi-binder Bind(Let), so no e2e
  test exercises this directly. The hardening stays.

**Cleanup pass (5-lens review)**:
- Linus hat: orphaned `field_access_name` docstring (insertion
  of `varat_pre_name` split it from its fn). Reordered.
- Linus hat: `pick_spec_source`'s `_ =>` catch-all on
  `FunctionKind` would silently accept new variants. Converted
  to exhaustive match (Static / TraitMethodImpl /
  TraitMethodDecl / ForeignTraitMethodImpl).
- FP: `collect_assume_sites` uses `RefCell` because
  `map_expr_visitor` takes `Fn` not `FnMut` — added a comment
  explaining why we discard the rebuilt expr (using a
  transformer as an inspector).
- Coverage: empty `tactus_tactic("")` rejection had no test —
  added `test_exec_tactus_tactic_empty_rejected`.

**Reasoning-clarity refactor**: looking for "what would slow me
down in a month" rather than for smells. Different lens, different
findings.
- `walk_call` was 200 lines doing 6 mixed phases. Split into
  three named helpers: `build_call_substitutions` returns a new
  `CallSubstitutions` struct (typ_subst, req_subst, ens_subst,
  mut_param_names, mut_idx_to_fresh, fresh_ret_name) bundling
  state previously scattered as 6 locals;
  `emit_call_precondition_theorem` and `push_post_call_frames`
  for the two emission phases. `walk_call` itself is now ~30
  lines.
- `build_wp_call` was 140 lines with 6 early-Err sites + arity
  + mut-arg building. Split into 4 named phases:
  `reject_unsupported_call_shapes`, `resolve_callee`,
  `validate_call_arities`, `build_call_mut_args`.
- Renamed `spec_source` → `spec_callee` to mirror `callee`.
  Added a header doc in walk_call explaining the dual structure
  (callee for binders/types, spec_callee for require/ensure).
- Added a "Peel/lift helpers" dispatch-table comment block in
  sst_to_lean.rs explaining 7 closely-related helpers
  (peel_transparent / peel_value_position / contains_loc /
  match_single_let_bind / unfold_multi_binder_let /
  lift_if_value / walk_let).

**Error message quality pass**: every `Err(...)` message reviewed
for "what did the user write? / is there a workaround? / is this
tracked?" Convention now applied uniformly:
- Cryptic short errors using internal type names → surface
  syntax. `"FuelConst not yet supported"` →
  `"reveal_with_fuel(f, n) not yet supported (#84). Workaround:
  use reveal(f) if available."` Same treatment for
  `OpenInvariant` (→ `open_atomic_invariant!`), `ClosureInner`,
  `DeadEnd`, the unary/binary catch-all errors, etc.
- `ExpX::Old` rejection (5-line essay added earlier today)
  collapsed to one-line internal-bug message. Long
  explanation moved to a code comment.
- 13 error messages rewritten total; behavioral surface
  unchanged.

**Reserved identifier conventions** (single source of truth):
- Four conventions had grown across sessions:
  `_tactus_<role>_<id>` prefix (codegen gensyms + theorem names),
  `<x>_at_pre_tactus` suffix (the only suffix outlier — keeps
  param name readable), `tactus_<name>` no-prefix (user-visible
  tactics), bare names in TactusPrelude (axioms / defs).
- Documented as a numbered convention list in
  `expr_shared.rs`'s "Reserved identifier conventions" section.
  Cross-references from `sanity::name_resolves` (Convention 4)
  and from the gensym sites in `walk_call` / `build_wp_loop`
  (Convention 1 + the `StmX::Loop::id` vs `next_id()` choice).
- Two gensym mechanisms documented: prefer Verus-stable IDs
  (e.g., `StmX::Loop::id`, `u64` per loop instance) when one is
  available; fall back to `ObligationEmitter::next_id()`
  (per-fn counter).

**Tier 3 #88 — labeled break / continue (LANDED)**:
- `WpLoopCtx::label: Option<String>` carries the loop's
  source-level label.
- `build_wp` parameter changed from `Option<&WpLoopCtx>` to
  `&[&WpLoopCtx]` (innermost-first).
- `build_wp_loop` extends the stack with the new ctx for body
  walks. Each loop's body gets its own pushed-front Vec.
- Resolution: unlabeled break uses `stack[0]`; labeled break
  searches by `label`. "Not found" cases produce
  internal-bug errors (Verus's mode checker should prevent them).
- Tests: `test_exec_loop_labeled_break` (renamed from
  `_rejected`, flipped to Ok); `test_exec_loop_labeled_break_three_deep`.
- Note: labeled `continue 'outer;` is rejected by Verus
  upstream without `loop_isolation(false)` (which we don't
  support either); the label-stack handles it in principle.

**Simplify pass** (reuse / quality / efficiency review):
- `let warnings = assume_warnings;` was a pure rename — removed.
- `WpLoopCtx` was `pub struct` with `pub` fields but used only
  internally. Narrowed to module-private.
- `rewrite_varat_for_mut_params` walked + rebuilt the entire
  VIR-AST tree even when `mut_param_names` was empty (every
  non-`&mut` callee). Added an empty-set short-circuit (just
  `expr.clone()`). Common-case efficiency win.
- Stale `Option<&WpLoopCtx>` doc on `WpLoopCtx` updated.

**Documentation pass**:
- README.md got a new "Tactus (this fork)" section above the
  upstream Verus "Status" — quick-start with the explicit
  toolchain-bin PATH command + pointers to DESIGN.md / HANDOFF.md.
- DESIGN.md got a "Putting Lean on PATH" subsection covering
  both the elan-bin-proxy case and the partial-install fallback.
- DESIGN.md got an "Beyond the five core lenses" section in
  the code-review-strategy chapter, documenting the four extra
  review lenses applied today and the meta-pattern (each lens
  is a new question).

**Net for the day**: 25 commits across the deferrals batch, five
review-style passes (5-lens / reasoning-clarity / error quality /
identifier conventions / simplify), one Tier-3 feature
(#88 labeled break), and a documentation pass. 196 → 217 e2e
tests (+21). Three real bugs surfaced + fixed. Thirteen deferral
tasks closed (#76–80, #82–83, #85, #88, #90, #92). Nine poems
committed across three batches.

#### Current session (2026-04-29 morning — #84 FuelConst clarified)

Closed #84 by establishing what was actually true: the deferrals
catalogue described `ExpX::FuelConst(_)` as "Blocks `reveal_with_fuel`
in exec fns," but tracing the producer-consumer chain revealed
that `FuelConst` is generated *only* by
`vir::recursion::rewrite_rec_call_with_fuel_const`, which is
called *only* from `vir::expand_errors` — Verus's Z3 SMT-error-
expansion pipeline. Tactus doesn't traverse that pipeline (we go
VIR → SST → Lean directly). So the `FuelConst` rejection is
structurally unreachable from the Tactus path; it's defensive
code, not a user-feature blocker.

The actual user-facing question — "how do I expose a recursive
spec fn's body in a `tactus_auto` fn?" — has a different answer.
`reveal_with_fuel` is a Verus-mode statement; in Tactus
`proof { ... }` blocks hold raw Lean tactic text. The Lean idiom
is `proof { unfold f }`, which propagates through the existing
theorem-level tactic-prefix mechanism (see `Wp::AssertByTactus
{ cond: None, .. }` — the same path as #49's proof-block
implementation).

**What changed:**
- `to_lean_sst_expr.rs`'s `ExpX::FuelConst(_)` arm: rewrote from
  a user-facing deferral error ("not yet supported (#84)") to
  an internal-bug message naming the reachability invariant.
  Comment block above the arm walks through the producer-consumer
  chain so a future maintainer can re-derive the unreachability.
- DESIGN.md "Expression-level forms rejected by
  `sst_exp_to_ast_checked`": `ExpX::FuelConst` entry rewritten
  with cross-reference to the new architectural section.
- DESIGN.md new subsection "reveal_with_fuel and unfold in
  Tactus" (under "Spec fn opacity model"): explains why Verus's
  fuel concept doesn't translate, and what the user does
  instead. Covers both `tactus_auto` exec fns (proof block →
  Lean tactic) and proof fns (`by { }` body → Lean tactic).
- 2 regression tests in `tactus.rs`:
  - `test_exec_recursive_spec_fn_no_reveal_needed` — pins that
    a `tactus_auto` fn referencing a recursive spec fn verifies
    when the obligation doesn't need unfolding (no fuel/reveal
    machinery required).
  - `test_exec_unfold_for_recursive_spec` — pins the user-facing
    workflow: `proof { unfold double }` propagates as a
    theorem-level prefix, exposing the spec-fn body to
    subsequent obligations.

**Discipline note worth recording: the deferral entry was
*describing the symptom*, not the cause.** The first instinct
("FuelConst rejection is the bug; lift it to allow reveal_with_fuel")
would have been wrong — there's no FuelConst arriving to lift,
and `reveal_with_fuel` doesn't translate at all. Tracing the
producer chain (one `Grep` for `ExpX::FuelConst` matches, then
following the only generator) was load-bearing. Without it I'd
have spent a day building a fuel-handling path that fired zero
times.

**Net for the morning**: 1 commit (this work bundled),
217 → 219 e2e tests (+2). One pending task closed (#84).
Documentation tightened.

#### Current session (2026-04-29 mid-morning — #91 BinaryOp::Index)

`array_index(a, i)` and exec-mode array indexing (after bounds-
check resolution) now lower to Lean's panic-on-out-of-bounds
indexing form `lhs[Int.toNat rhs]!` (total via the GetElem
typeclass; observationally fine because Tactus only verifies,
never executes the generated Lean). Closes #91 for spec-mode
indexing; exec-mode `a[i]` in user code still hits a
Verus-side rejection because the surface syntax desugars to
`vstd::array::array_index_get` (cross-crate, can't inline).

**What landed:**
- `to_lean_sst_expr.rs`: `BinaryOp::Index(_kind, _bounds)` arm
  added. Renders as `ExprNode::Index { base, idx, bang: true }`,
  with `idx` wrapped in `Int.toNat` to coerce Verus's `int` index
  type to Lean's `Nat` (which is what GetElem expects). Both
  `ArrayKind::Array` and `ArrayKind::Slice` go through the same
  rendering — Lean's `Array α` and `List α` both implement
  GetElem with Nat-indexed `[i]!`.
- `to_lean_type.rs`: `Primitive::Array` and `Primitive::Slice`
  type rendering now drops the second type argument (the const
  length carried by `[T; N]`). Lean's `Array α` and `List α` are
  unary type constructors; passing two args produced `Array Int 4`
  errors of "Function expected at `Array Int`" before this fix.
- `lean_ast.rs`: `ExprNode::Index` grew a `bang: bool` flag so
  the same node serves both `xs[i]` (existing PlaceX path, plain
  `[idx]`) and `xs[i]!` (new BinaryOp::Index, panic-on-OOB).
  Updated 5 sites: pp, sanity, strip_span_marks, substitute_impl,
  collect_free_vars, plus the unit test fixtures.
- `to_lean_expr.rs`: existing `PlaceX::Index` rendering keeps
  `bang: false` — proof-fn place indexing is rare and usually
  has the bounds proof in scope already (legacy mut-ref code).
  Add `!` only when a concrete shape needs it.

**Tests** (3 new):
- `test_exec_index_array_in_requires` — pinpoints the minimal
  shape: `array_index(a, 0)` in a requires clause renders cleanly.
- `test_exec_index_array_in_ensures` — same builtin in ensures.
  Pins the inlined-ensures rendering path.
- `test_exec_index_array_in_assert` — two indexing operations
  composed with arithmetic in an `assert(P)`.

**Caveats / followups documented (rejected with clear messages):**
- Exec-mode `a[i]` user syntax for slices/arrays goes through
  `vstd::array::array_index_get` / `vstd::slice::slice_index_get`,
  which Tactus can't inline (cross-crate). Workaround for now:
  use the spec builtin `array_index(a, i)` in proof contexts; for
  exec read of array elements, route through a same-crate exec
  wrapper. Tracked as a #91 follow-up.
- Element types must be `[Inhabited α]` for `xs[i]!` to elaborate.
  Primitives and non-generic user datatypes already satisfy this
  (`deriving Inhabited` from #54). Generic element types may
  not — currently no test pins this.

**Net for mid-morning**: 1 commit, 219 → 222 e2e tests (+3),
one pending task closed (#91). Down to 9 pending tasks.

#### Current session (2026-04-29 late morning — #89 entry/exit invariant split)

`invariant_except_break` (at_entry only) and loop `ensures`
(at_exit only) now verify in `tactus_auto` exec fns. Closes #89.
For plain `while c { ... }` loops, Verus's lowering forces
`at_entry = at_exit = true`, so behavior is unchanged. The split
actually matters for `cond: None` (break-lowered) loops, where
the user can write three flag combinations:
* `invariant P` (at_entry = at_exit = true): preserved across
  iteration AND established at break.
* `invariant_except_break P` (at_entry only): preserved across
  iteration but NOT required at break (i.e., break may
  invalidate). Post-loop ctx doesn't get to assume it.
* `ensures P` (at_exit only): required at break (and natural
  exit), but not necessarily at iteration boundaries.

**What landed:**
- `build_wp_loop`: removed the rejection that required all
  invariants to have `at_entry = at_exit = true`. Replaced with
  a comment block describing the three classifications and how
  Verus's lowering enforces `at_entry = at_exit` for
  `cond: Some` loops.
- `build_wp_loop`: `inv_conj` (single conjunction over all
  invariants) split into `entry_inv_conj` (at_entry-filtered)
  and `exit_inv_conj` (at_exit-filtered). `continue_leaf` =
  `entry_inv_conj ∧ decrease`; `break_leaf` = `exit_inv_conj`.
  Empty list folds to `True` via `and_all`.
- `walk_loop`: same entry/exit split for init theorems
  (at_entry-filtered), maintain ctx hyp (entry_inv_conj_marked),
  use ctx hyp (exit_inv_conj_marked).

**Tests** (4 new, all in tactus.rs):
- `test_exec_loop_invariant_except_break` — happy path with
  all three flag combinations in one loop.
- `test_exec_loop_invariant_except_break_init_fails` — negative
  test: `i: i8 = 10` violates the at_entry-only `i <= 9`.
- `test_exec_loop_ensures_only` — happy path; pins that the
  use ctx assumes at_exit invariants (regular `invariant`'s
  at_exit=true contributes there alongside `ensures`).
- `test_exec_loop_ensures_fails` — negative test: `ensures
  i == 100` can't be established at the only break point
  (i = 10).

**Side discovery worth recording: chained-comparison shadowing.**
While developing the tests, I tried writing `invariant 0 <= i <= 10`
(Verus's chained syntax). The chained form goes through
`ast_simplify::temp_var` which produces N temp VarIdents that
all share the base name `tmp%%`. Our `sanitize` collapses the
`%`s without including the disambiguator id, so the temps
shadow each other in nested let-bindings:
`let tmp__ := 0; let tmp__ := i; let tmp__ := 10;
tmp__ ≤ tmp__ ∧ tmp__ ≤ tmp__` — which reduces to a trivially-
true `10 ≤ 10 ∧ 10 ≤ 10` via Lean's let-evaluation, instead of
the intended `0 ≤ i ∧ i ≤ 10`.

**The fix attempt and the rabbit hole:** I built a
`sanitize_var_ident(&VarIdent) -> String` helper that appends the
disambiguator's id when the base name needs sanitization
(contains `%`/`@`/`#`). User-named locals (no special chars)
keep their natural names; synthetic temps get `tmp__0`,
`tmp__1`, etc. — distinct, no shadowing.

But applying it broadly broke 55-149 e2e tests because
`sanitize_var_ident` adds id suffixes to ALL VarIdents whose
names need sanitization, not just the colliding-temp case.
And it requires every binder site AND every var-ref site to
agree on which sanitization function they use. There are ~10
sites; getting them all consistent surfaced cascades of
mismatches between binder names and var refs, and between
SST-renderer paths and VIR-AST renderer paths.

**Decision: defer the chained-compare fix.** The full
`sanitize_var_ident` rollout is wider than #89's scope. The
Tactus tests for #89 use explicit `&&` (`0 <= i && i <= 10`)
instead of the chained `0 <= i <= 10` form, which sidesteps the
temp generation entirely. Real user code that hits the chained
form in a tactus_auto fn invariant will still produce
unsoundly-true obligations; documented as a known limitation
in the test's comment block. Future fix: either (a) push
`sanitize_var_ident` consistently through all renderer sites
(~10 sites + careful per-test verification), or (b) detect
shadowing locally in the BndX::Let renderer and rename
within scope.

**Net for late morning**: 1 commit, 222 → 226 e2e tests (+4),
one pending task closed (#89). Down to 8 pending tasks.

#### Current session (2026-04-29 afternoon — #99 typed LeanName refactor)

The chained-compare hole from #89 — where Verus's
`ast_simplify::temp_var` produced N synthetic temps with the
same base name `tmp%%` and our `sanitize` collapsed them all
to `tmp__`, silently lowering chained `0 <= i <= 10` to
`True` via Lean's let-shadowing — is now closed at the type
level. Closes #99.

**The fix: typed `LeanName` newtype.** A newtype with no
`From<String>` / `From<&str>` impl, only constructable via
explicit constructors:
- `LeanName::from_var_ident(&VarIdent)` — canonical for any
  VarIdent → name conversion. Always includes the
  disambiguator's id when needed (synthetic-prefix names like
  `tmp%%`, `tmp%`, `expand%`); user-named locals (`i`, `count`,
  no `%` in source name) keep their natural names.
- `LeanName::from_path(&Path)` — VIR `Path` → dotted Lean name.
- `LeanName::lit(&str)` — hardcoded prelude refs (`"Nat"`,
  `"omega"`, `"Int.toNat"`).
- `LeanName::synthetic(impl Into<String>)` — codegen-generated
  names (gensyms, `_tactus_*` prefixes, `h_<i>` hypothesis
  names).
- `LeanName::from_field(&str)` — struct/enum field names that
  arrive as `&str` from VIR.

`ExprNode::Var(LeanName)`, `ExprNode::Let { name: LeanName,
.. }`, `Binder { name: Option<LeanName>, .. }`,
`Pattern::Var(LeanName)`, `Pattern::Binding { name: LeanName,
.. }` enforce at compile time that any name flowing into the
AST came from one of the explicit constructors. A future
contributor can't accidentally write `ExprNode::Var(sanitize(&v.0))`
— that's a type error.

**What's NOT migrated to LeanName:** top-level command names
(`Def.name`, `Theorem.name`, etc.) and field-name-shaped
strings (`FieldProj.field`, `Pattern::Ctor.name`,
`StructUpdate` keys). Those are codegen-synthesized or
path-derived and don't have shadowing concerns.

**Convenience constructors on `LExpr`:**
- `LExpr::var(LeanName)` — strict
- `LExpr::var_lit(&str)` — wraps in `lit` (literal Lean ref)
- `LExpr::var_synthetic(impl Into<String>)` — wraps in
  `synthetic` (already-processed name)
- Same pattern for `let_bind` / `let_bind_synthetic`

The two convenience constructors keep call sites readable for
the common cases (literal references and pre-processed
strings) while the strict `var(LeanName)` form is what the AST
actually requires.

**What landed:**
- `lean_name.rs`: new module with `LeanName` newtype + 5
  constructors. 4 unit tests pinning user-var-no-suffix,
  synthetic-temp-disambiguated, lean-keyword-quoted,
  lit-unchanged.
- `lean_ast.rs`: `Var`, `Let.name`, `Binder.name`,
  `Pattern::Var`, `Pattern::Binding.name` migrated to
  `LeanName`. `substitute` / `strip_span_marks` /
  `collect_free_vars` updated to use `as_str()` for keying.
- All 5 renderers (`to_lean_type`, `to_lean_expr`,
  `to_lean_sst_expr`, `to_lean_fn`, `sst_to_lean`) updated
  to go through `LeanName::*` constructors at every name-
  conversion site. ~80 call sites total.
- `sanity.rs`, `lean_pp.rs`: updated to call `as_str()` on
  LeanName for HashSet keying / output.
- One regression test added: `test_exec_chained_compare_distinct_temps`
  pins that chained `0 <= i < 10` doesn't silently lower to
  `True` (uses a deliberately-violated chained compare and
  expects the precondition obligation to fire).
- Restored chained syntax in `test_exec_loop_ensures_only`,
  `test_exec_loop_ensures_fails`, `test_exec_loop_invariant_except_break`
  (had been changed to `&&` form during #89 to sidestep the
  shadowing).

**Discipline note worth recording:** the refactor cascaded
through ~75 call sites across 5 files. The work was
mechanical but the *type system carried the cost* — every
site that previously passed a `String` to an AST constructor
became a compile error pointing at exactly where the choice
of constructor (lit / synthetic / from_var_ident / from_path)
needed to be made. Half-done refactors couldn't compile,
which is exactly the property that made the original sanity-
check / runtime-detection approach fragile. The compiler
itself enforces the invariant now.

The 4 i16/i32/i64/i128 tests caught the ONE remaining
inconsistency I missed (`build_call_substitutions` was using
`sanitize(&p.x.name.0)` for the subst key while the body's
var refs went through `from_var_ident`). Once the test
suite was green, we know every site agrees.

**Net for the afternoon**: 1 scaffolding commit (lean_name
module + poems) + 1 big refactor commit. 226 → 227 e2e tests
(+1 chained-compare regression). 4 unit tests added (+4 →
118). One pending task closed (#99). Most importantly: the
soundness hole that "was indistinguishable from no fix when
the bug is about consistency across sites" is now
type-system-prevented.

#### Current session (2026-04-29 late afternoon — #100 Validated<Exp> typestate)

The `sst_exp_to_ast` panic site is now a type-system-enforced
invariant. Same architectural pattern as #99: identify a
runtime contract (here, "caller has already validated"),
introduce a newtype whose constructors are the only path to
the property, let the compiler enforce consistency.

**The change:**
- `Validated<'a>` newtype in `to_lean_sst_expr.rs`. Constructable
  only via `Validated::check(&Exp) -> Result<Validated, String>`.
- `lower(Validated<'_>) -> LExpr` is the only consumer.
- `Wp<'a>` variants migrated: `Let`, `Assert`, `Assume`,
  `AssertByTactus.cond`, `Branch.cond`, `Loop.cond` /
  `validated_invs` / `decrease`, `Call.args` all hold
  `Validated<'a>` instead of `&'a Exp`.
- `build_wp` / `build_wp_loop` / `build_wp_call` construct
  via `Validated::check(...)?` (errors propagate to callers).
- Walkers (`walk_obligations` / `walk_loop` / `walk_call` /
  `walk_assert_by_tactus`) are panic-free by construction —
  they call `lower_validated(...)` on Validated witnesses
  threaded through the Wp tree.

**Migration shim for incremental rollout.** ~10 sites still
call the legacy `sst_exp_to_ast(&Exp) -> LExpr` (panic
version), e.g., `WpCtx::new`'s ensures rendering, `walk_let`'s
peeled-bind handling, `build_req_binders`, `lift_if_value`,
the test-fixture site. These contexts have `&Exp` references
without easy access to a `Validated` witness; threading
through would cascade further. The shim panics with a clear
message that documents the migration; tracked for removal as
each site gets refactored.

The architectural change is in place — every NEW Wp construction
site goes through `Validated::check`; the walker interior is
guaranteed-no-panic; the `lower` function takes a typed
witness. The shim is a transition aid, not part of the
intended API.

**No new tests** — the change is internal refactor; the
existing 227 e2e tests + 118 unit tests all pass, confirming
the typed pipeline produces identical output to the prior
`String`/`&Exp` pipeline. The unit tests in `lean_name.rs`
exercise the parallel typed-name pattern; future tests for
`Validated` could pin the "ill-formed Exp produces Err
instead of panic at lower" path.

**DESIGN.md additions** — new "Type-system-enforced
invariants" section under "Spec fn opacity model" naming the
pattern (LeanName + Validated as the two examples) and a
"Potential future applications" subsection noting the two
candidates that didn't make the cut today (#101 substitute-
keying-with-LeanName scheduled next; AssertKind split and
prelude-name allowlist sync as further-out candidates).

**Net for late afternoon**: 1 commit, 227 e2e tests still
pass (no regression). One pending task closed (#100). #101
remains for next session if desired.

#### Current session (2026-04-29 evening — #101 substitute keys typed as LeanName)

`HashMap<String, Expr>` → `HashMap<LeanName, Expr>` for the
substitution map used by `lean_ast::substitute`. Follows
naturally from #99 / #100 — same architectural pattern,
applied one layer up to the call-site-inlining substitution
pipeline.

**The change:**
- `substitute(&Expr, &HashMap<LeanName, Expr>) -> Expr` —
  signature change; the helpers `subst_without`,
  `subst_remove_binders`, `check_capture_lazy` updated to
  match.
- `CallSubstitutions` struct fields (`typ_subst`,
  `req_subst`, `ens_subst`) now `HashMap<LeanName, LExpr>`.
- Construction sites in `build_call_substitutions`
  (sst_to_lean.rs) and `render_checked_decrease_arg`
  (to_lean_sst_expr.rs) use `LeanName::lit` (for type
  parameters), `LeanName::from_var_ident` (for value
  parameters / ret), or `LeanName::synthetic` (for
  pre-state names like `<x>_at_pre_tactus`).
- Test fixture `subst_of` updated to construct `LeanName`
  keys via `LeanName::lit`.

**What this prevents.** A future contributor can't accidentally
write `subst.insert("x".to_string(), ...)` where `"x"`
came from somewhere other than a known name source — that's
a type error now. The key has to be a `LeanName`, which only
comes from one of the five typed constructors.

**No new tests** — refactor is internal; the existing 227
e2e + 118 unit tests confirm output equivalence to the old
String-keyed pipeline.

**DESIGN.md addition** — new "#101" entry under
"Type-system-enforced invariants" explaining that the
substitution-map keying follows naturally from #99: now that
names in the AST are typed, the substitution-keying layer
inherits the typing for free.

**Net for evening**: 1 commit. Still 227 e2e + 118 unit
tests, all passing. One pending task closed (#101).

**Day total**: 6 commits across 6 closed tasks today (#84
FuelConst, #91 Index, #89 invariant_except_break, #99
LeanName, #100 Validated, #101 substitute-keying), plus
2 architectural cleanup tasks. ~1500 lines of net change.
217 → 227 e2e tests (+10). 114 → 118 unit tests (+4).
Six poems. The chained-compare hole that was a soundness
gap yesterday is now structurally unrepresentable; the
panic-on-unvalidated-Exp contract is now type-system-
enforced; substitution map keys are now typed.

#### Current session (2026-04-29 evening — typed-invariant audit + 3 more landings)

After #99/#100/#101 the user asked for an audit: "anything
else that might 'work' but would be better to enforce in the
type system?" Found four candidates ranked by clarity:

* **#102 AssertKind sum-type split** — was a flat enum with
  `is_obligation_kind()` runtime discriminator (silent
  miscategorization risk on new variants). Now
  `AssertKind = Obligation(ObligationKind) | Hypothesis(HypothesisKind)`;
  adding a new variant means picking which arm structurally.
  ~30 use sites updated via bulk sed; `is_obligation_kind`
  becomes `matches!(self, AssertKind::Obligation(_))`.
* **#103 LoopInvKind** — was two bools encoding three states
  + nonsensical `(false, false)`. Now an enum with
  `Invariant | InvariantExceptBreak | Ensures` constructed
  via `LoopInvKind::from_loop_inv` which rejects `(false, false)`.
  Stored alongside `validated_invs` as a parallel Vec on
  `Wp::Loop` (couldn't change Verus's `LoopInv` directly —
  it's their struct).
* **#105 MutArgInfo struct** — fused `mut_args:
  Vec<(usize, &VarIdent)>` + `mut_idx_to_fresh:
  HashMap<usize, LeanName>` (parallel arrays with
  `.expect()` on every lookup) into `Vec<MutArgInfo {
  param_idx, caller_var, fresh: LeanName }>`. Removes the
  expect; `push_post_call_frames` no longer takes a separate
  `mut_args` parameter — iterates `subst.mut_args` directly.
* **#104 typed build_wp dispatch** — STILL PENDING.
  `build_wp_call` / `build_wp_loop` panic with
  `unreachable!("build_wp_X called on non-X statement")`
  when called on the wrong StmX variant. Should take
  destructured StmX::Call { ... } / StmX::Loop { ... } fields
  directly so the wrong-variant case is unrepresentable.
  Roughly: change build_wp_call/loop to take individual fields
  (`fun, args, dest, ...`) destructured at the dispatch
  point in `build_wp`. Mostly mechanical signature change.

**Tier 3 candidates noted in DESIGN.md** (not worth doing now):
* OblCtx frame ordering invariant (typed builder pattern)
* `Tactic::Raw` vs `Tactic::Named` enum
* `format_rust_loc` returning typed `RustLoc` struct

These are all noted in the "Type-system-enforced invariants"
section (with a "Potential future applications" subsection
tracking what remains).

**What landed this evening:**
- DESIGN.md "Type-system-enforced invariants" extended with
  #102, #103, #105 entries naming the patterns.
- 227 e2e tests still pass throughout. 118 unit tests.
- The `Wp::Loop` variant grew an `inv_kinds: Vec<LoopInvKind>`
  field parallel to `validated_invs` and `invs` — three
  parallel arrays now, but each adds independent typed
  information (kind, validation witness, original metadata).
  A future cleanup could fuse them into one struct (similar
  to how MutArgInfo fused mut_args).
- `CallSubstitutions.mut_idx_to_fresh: HashMap<usize, LeanName>`
  removed; now `mut_args: Vec<MutArgInfo<'a>>` directly.
- `push_post_call_frames` signature reduced (one fewer param).

**What remains for next session — pending tasks:**
- **#104** typed build_wp dispatch (the only typed-invariant
  candidate left from this session's audit)
- **#87** &mut x.f / &mut v[i] non-simple Loc shapes (#55
  follow-up)
- **#94** callee-side &mut body verification
- **#95** new-mut-ref mode (MutRefCurrent/MutRefFuture)
- **#86** trait method impl-strengthening of ensures
- **#96** trait default-impl invocation
- **#93** ExpX::CallLambda + StmX::ClosureInner (closures)
- **#98** substitute() walk_children boilerplate cleanup
- **#97** OblCtx::with_frame O(N²) → Rc<im::Vector>
- **sst_exp_to_ast shim removal** (#100 follow-up; 10 call
  sites still use the panic shim, migration is mechanical)

**Things learned worth recording:**
- The typed-invariant pattern compounds: each application
  makes the next one easier to spot. After #99, #100/#101
  followed in one afternoon. After the user's audit prompt,
  three more (#102/#103/#105) landed in one evening.
- "The pattern, once named, became something to *look for*."
  The DESIGN.md section was meant as documentation; in
  practice it functioned as a search query.
- The migration shim approach (e.g., #100's `sst_exp_to_ast`
  retained as a deprecated panic-shim) lets the architectural
  change land without requiring every call site to migrate
  in lockstep. Complete migration becomes incremental
  cleanup.
- Bulk sed works for mechanical variant renames but each
  pattern needs a careful regex — getting it slightly wrong
  produces subtle code corruption (saw this with the
  `extract_simple_var(&loc_exp(x))` mishap in #99).

**Net for evening**: 3 commits coming (one per #102, #103,
#105 — being committed together with this HANDOFF update).
227 e2e + 118 unit tests. Three more pending tasks closed.
Down to **9 pending tasks** (was 8 + 1 newly-noticed #104).

#### Current session (2026-05-01 morning — #104 typed build_wp dispatch)

The last typed-invariant audit candidate landed. `build_wp_call`
and `build_wp_loop` previously took a `&'a Stm` and re-destructured
internally with `let StmX::Call { … } = &stm.x else { unreachable!(...) };`
— a runtime panic if the dispatcher ever called them on the wrong
variant. Post-#104 they take the destructured fields directly:

```rust
fn build_wp_call<'a>(
    fun: &'a Fun,
    resolved_method: &'a Option<(Fun, Typs)>,
    is_trait_default: &'a Option<bool>,
    typ_args: &'a Typs,
    args: &'a Exps,
    split: &'a Option<Message>,
    dest: Option<&'a Dest>,
    call_span: &'a Span,
    after: Wp<'a>,
    ctx: &WpCtx<'a>,
) -> Result<Wp<'a>, String>
```

The destructure happens at the `build_wp` dispatch site (an
explicit `StmX::Call { … }` / `StmX::Loop { … }` match arm with no
`..`), where any Verus-side field addition still causes a compile
error — the upstream-robustness defence stays intact, just lifted
from inside the helpers to the dispatcher. The wrong-variant case
is now structurally unrepresentable: there's no `Stm` parameter
to mismatch against.

**What landed:**
- `build_wp` dispatch arm for `StmX::Call` destructures all 9
  fields explicitly (with `mode: _` and `assert_id: _` for the
  ones we ignore), passes the rest as named parameters to
  `build_wp_call`.
- Same shape for `StmX::Loop` — 11 fields destructured
  (`is_for_loop`, `typ_inv_vars`, `modified_vars`,
  `pre_modified_params` as `_`).
- `build_wp_call`'s `unreachable!` panic and the inline
  destructure-or-error pattern are gone. Same for `build_wp_loop`.
- Doc comments updated on both helpers to record the new shape
  and where the upstream-robustness defence lives.

**Testing**: 227 e2e + 118 unit + 1 coverage tests all green
on first run, no regressions. The refactor is mechanical and
the type system carried the migration cost — `cargo check`
caught every site that needed updating during the edit.

**DESIGN.md additions:**
- New `#104` entry under "Type-system-enforced invariants".
- "Potential future applications" section refreshed: stale
  AssertKind entry removed (landed as #102 already), and the
  three Tier 3 candidates noted in the audit poem (`OblCtx`
  frame ordering, `Tactic::Raw` vs `Tactic::Named`, typed
  `RustLoc`) added with cost/benefit framing for why they're
  deferred.

**What remains pending:**
- **#87** &mut x.f / &mut v[i] non-simple Loc shapes (#55 follow-up)
- **#94** callee-side &mut body verification (#55 follow-up)
- **#95** new-mut-ref mode (MutRefCurrent/MutRefFuture) (#55 follow-up)
- **#86** trait method impl-strengthening of ensures (#56 follow-up)
- **#96** trait default-impl invocation (#56 follow-up)
- **#93** ExpX::CallLambda + StmX::ClosureInner (closures)
- **#98** substitute() walk_children boilerplate cleanup
- **#97** OblCtx::with_frame O(N²) → Rc<im::Vector>
- **`sst_exp_to_ast` shim removal** (#100 follow-up; ~10 call sites)

The typed-invariant audit batch is now complete: seven applications
of the pattern landed (#99, #100, #101, #102, #103, #104, #105)
across two days. The pattern that started as a single fix for a
chained-compare soundness hole turned out to apply structurally
across the codebase once named.

**Net for the morning**: 1 commit. 227 e2e + 118 unit + 1 coverage
tests still pass. Down to 8 pending tasks (closes the typed-invariant
audit batch from yesterday's session).

#### Current session (2026-05-01 mid-morning — #94 callee-side &mut body)

Closed #94: `tactus_auto` on a fn that itself takes `&mut` params now
verifies. The roadmap called this "the largest of the three #55 follow-
ups" but the implementation was actually session-sized — the AST-side
caller infrastructure (`varat_pre_name` in `expr_shared.rs`, the
rewrite pattern in `rewrite_varat_for_mut_params`) had already
established the *shape*; #94 just applied the same shape one layer
down at the SST level.

**The bug surfaced first.** Probe test (flipping `tactus_auto` on
`bump(x: &mut u8) { *x = *x + 1; }`) produced this goal:

```
let x := x + 1;
x = x + 1
```

Both `*x` (post-state) and `*old(x)` (pre-state) lowered to `Var(x)`,
and the body's `let x := x + 1` shadow made them equal — silently
wrong. The ensures `*x = *old(x) + 1` evaluated against shadowed-x
on BOTH sides: `(x+1) = (x+1)+1`, false. (This is similar to the
#99 chained-compare hole — different shape, same family.)

**Encoding (mirrors caller-side #55):**
1. **SST-level rewrite**: `rewrite_varat_for_mut_params_in_stm` and
   `_in_exp` walk the body and ensures, replacing
   `ExpX::VarAt(x, Pre)` with `ExpX::Var(<x>_at_pre_tactus)` for
   every `&mut` param x. Uses `vir::sst_visitor::map_exps_in_stm_visitor`
   / `map_exp_visitor` (newly promoted from `pub(crate)` to `pub`,
   plus the containing `sst_visitor` module promoted from `mod` to
   `pub mod`). Synthetic name produced via the shared
   `varat_pre_name` helper in `expr_shared.rs` — same one the
   caller-side path uses for substitution-map keys.
2. **Initial OblCtx Let frame** per `&mut` param:
   `Let(<x>_at_pre_tactus, Var(x))` — wraps the goal at theorem-
   emission time so the body's WP (which after rewrite mentions
   `<x>_at_pre_tactus`) sees the pre-state captured before any
   body modification.
3. **Requires NOT rewritten**: at fn entry, x IS the pre-state;
   `*old(x) ≡ x` for requires evaluation. The natural VarAt → Var
   collapse in the SST renderer is correct for them, and they go
   to theorem-level binders (`build_req_binders`) emitted before
   the body's WP wrap.
4. **Symmetry payoff**: the encoding works end-to-end with the
   caller-side path because both use the SAME `varat_pre_name`
   helper for the synthetic name, AND the caller's
   `build_call_substitutions` already inserts a binding for
   `<p>_at_pre_tactus → arg` in the inlined ensures. So a fn
   verified callee-side with `*old(x)` references composes cleanly
   when called from a tactus_auto caller. Pinned by
   `test_exec_callee_mut_and_caller_both_tactus_auto`.

**Tests** (5 new, 227 → 232):
- `test_exec_callee_mut_simple` — happy path, `bump(x: &mut u8)
  { *x = *x + 1; }` with `*old(x) < 100` requires and `*x == *old(x) + 1`
  ensures. Foundation regression guard.
- `test_exec_callee_mut_wrong_body` (negative) — body assigns
  `*x = *x + 2` instead of `+ 1`. Pins that the ensures actually
  sees the body's let-shadow, not just the original pre-state value
  (would catch a regression where rewrite or Let frame is missing).
- `test_exec_callee_mut_multiple_writes` — `*x = *x + 1; *x = *x + 1;`
  with ensures `*x == *old(x) + 2`. Pins that successive
  let-shadows compose correctly.
- `test_exec_callee_two_mut_params` — `bump_both(a: &mut u8, b: &mut u8)`.
  Pins that the per-param Let frames don't collide.
- `test_exec_callee_mut_and_caller_both_tactus_auto` — end-to-end
  with both #55 caller-side and #94 callee-side active in the
  same crate. Pins the shared `varat_pre_name` contract.

**Upstream change:** `vir/src/lib.rs` promoted `mod sst_visitor` to
`pub mod sst_visitor`. Plus two functions (`map_exp_visitor`,
`map_exps_in_stm_visitor`) went from `pub(crate)` to `pub`. Comments
at all three sites cross-reference #94 so a future rebase audit
knows why they're exposed. No semantic change to upstream Verus —
this is just a visibility bump.

**Discipline note worth recording: estimates were off by an order
of magnitude.** I planned for a session-sized task; actual work
was ~30 minutes after the probe test. The reason: the AST-side
caller infrastructure had already established the conceptual
pattern (rewrite VarAt at the SST/AST level, share synthetic-name
helper). #94 was a parallel application at one level down — same
mechanical shape, same shared helper, same name-management
discipline. This mirrors the typed-invariant audit pattern
(#99–#105): once the *shape* is named once, applying it
elsewhere is fast. The first instance pays for the convincing;
later instances inherit it.

**What remains (still in #55 follow-ups):** #87 (non-simple Loc
shapes — `&mut x.f` / `&mut v[i]`); #95 (new-mut-ref mode —
`MutRefCurrent`/`MutRefFuture` UnaryOps).

**Net for mid-morning**: 1 commit. 232 e2e + 118 unit + 1 coverage
tests pass; 1530 vstd functions still verify. Down to 7 pending
tasks (was 8 + closed #94).

#### Current session (2026-05-01 late morning — #86 impl-strengthening of ensures)

Closed #86. When the resolved trait impl strengthens the trait's
ensures (e.g., trait says `r < 100`, impl says `r == 5`), the call
site now sees the conjunction `(trait_ensures) ∧ (impl_ensures)`.
Caller can rely on the impl-specific guarantee, not just the
trait-level contract.

Verus's trait-impl-checking pass already enforces `impl ⇒ trait`,
so the conjunction is satisfiable — caller never proves something
inconsistent.

**Encoding (`build_call_substitutions` + `push_post_call_frames`):**

1. `build_call_substitutions` now takes `spec_callee` (the trait
   method decl, when callee is a `TraitMethodImpl`) in addition to
   `callee` (the resolved impl). Builds substitution maps keyed on
   BOTH `callee.params` (impl) and `spec_callee.params` (trait) —
   same arg values for both spellings of each param's name. Needed
   because Rust allows trait and impl to use textually different
   param names (positionally aligned but textually independent),
   and the trait's ensures uses trait names while the impl's uses
   impl names.
2. Same approach for the ret name: both `callee.ret.name` and
   `spec_callee.ret.name` map to `fresh_ret_name`. So either side's
   ensures clause renders with the gensym'd ret regardless of
   whether trait/impl ret names match.
3. `push_post_call_frames` Phase 3 now conjoins
   `spec_callee.ensure.0` (trait's clauses) with `callee.ensure.0`
   (impl's clauses) when callee != spec_callee (detected via
   `Arc::ptr_eq` on the `Fun` field). Both substituted via the
   same `subst.ens_subst` (which now has both spellings).
4. Helper `add_param_subst_entries` extracts the per-param
   subst-building logic so the two passes (callee + spec_callee)
   share implementation. The second pass is a no-op when
   `callee == spec_callee` — overwrites entries with identical
   values; running unconditionally keeps the code simple.

**Aesthetic note (not a bug).** When trait and impl have IDENTICAL
ensures (a common case — impl just repeats the trait), the
conjunction duplicates the clause: `(r == x) ∧ (r == x)`. Goals
look slightly verbose. `omega`/`simp_all` handle this fine. A
future refinement could syntactically dedup but the cost outweighs
the readability hit at current scale.

**Tests** (2 new, 232 → 234 e2e):
- `test_exec_call_trait_method_impl_strengthens` (positive): trait
  declares `ensures r < 100`; impl strengthens to `ensures r == 5`;
  caller's `ensures r == 5` becomes provable. Pre-#86 this would
  fail (caller would only see `r < 100` from the trait).
- `test_exec_call_trait_method_wrong_impl_strengthening` (negative):
  same trait with two impls (`AlwaysFive: r == 5`,
  `AlwaysTen: r == 10`). Caller of `AlwaysFive::unwrap()` claims
  `r == 10` — fails postcondition. Pins that the impl-strengthening
  comes from the RESOLVED impl, not some other impl of the same
  trait. The goal generated shows `_tactus_ret_1 < 100 ∧
  _tactus_ret_1 = 5` as the conjoined hypothesis — both clauses
  visible.
- Existing `test_exec_call_trait_method_two_impls` still passes
  (caller's `ensures r < 100` is implied by impl's `r == 5` /
  `r == 10`). Updated comment to reference the new tests.
- Existing `test_exec_call_trait_method_with_args` still passes
  (impl and trait have matching param names; the second
  substitution pass is a no-op).

**Latent bug fixed along the way.** Pre-#86 the substitution map
was keyed only on `callee.params` (impl) names, but applied to
`spec_callee.ensure.0` (trait's clauses with trait names). When
trait and impl had matching param names — the case all current
tests covered — substitution worked. When they differed, the
trait-side names wouldn't substitute and the rendered ensures
would have free variables. No test exercised the differing-name
case, so the bug was unobserved; the new union-key approach
addresses it incidentally.

**What remains (still in #56 follow-ups):**
- #96 `is_trait_default = Some(true)` (default-impl invocation)
- Cross-crate trait method decls (Phase 3 work)
- Truly dynamic dispatch via `dyn Trait` (cross-crate variant)

**Net for late morning**: 1 commit. 234 e2e + 118 unit + 1 coverage
tests pass; 1530 vstd functions still verify. Down to 6 pending
tasks (was 7 + closed #86).

#### Current session (2026-05-01 noon — #96 trait default-impl invocation)

Closed #96 via the probe-driven approach the recommendation
described: lift the rejection, see what fails, design the fix.

The probe failed with arity mismatch:

> callee `Path(None, ["impl&%0%default%salute"])` declares 0 type
> param(s) but call site passes 1 type arg(s)

Verus's `DynamicResolved.is_trait_default = Some(true)` resolves
to a synthesized wrapper fn whose path looks like
`<impl_path>%default%<method_name>` (see `vir::def::trait_inherit_default_name`).
The wrapper has `typ_params: []` (Self is specialized into the
wrapper's identity), but `resolved_typs` at the call site has 1
entry (the concrete Self). Mismatch.

**Fix:** when `is_trait_default = Some(true)`, `resolve_callee`
now redirects to the trait method decl (`fun`) directly, using
the call site's `typ_args` (which include Self in the position the
trait method decl expects). The trait method decl holds the
default body and its specs (`callee.ensure.0` etc. populated by
Verus's pipeline), so `pick_spec_source` returns it as both
callee and spec_callee (TraitMethodDecl arm); #86's
impl-strengthening path is a no-op (no separate impl — the
default IS the body).

**Why Self resolves through existing typ_subst.** Verus represents
Self as a regular type parameter on the trait method decl. The
existing `build_call_substitutions` zips `callee.typ_params` with
`callee_typ_args` to build `typ_subst`, which renders `TypParam(T)
↦ Var(rendered_concrete_typ)`. For default-impl calls after the
redirect: `callee.typ_params` includes Self, `callee_typ_args[0]`
IS the concrete Self type — they line up. No Self-specific
machinery needed.

**Implementation: 1 line + comment.** Added `is_trait_default`
parameter to `resolve_callee`; when `Some(true)`, take the
`(fun, typ_args)` branch directly instead of `(resolved, resolved_typs)`.
The rejection in `reject_unsupported_call_shapes` was lifted with
a `let _ = is_trait_default` to keep the parameter live. Total
edit: ~25 lines including doc comments.

**Tests** (4 new, 234 → 238 e2e):
- `test_exec_call_trait_default` (positive) — basic trait with
  default body, impl uses `impl Greeter for Plain {}` form.
- `test_exec_call_trait_default_wrong_ensures` (negative) — caller's
  ensures contradicts the default's ensures; pins that the
  default's spec is what the caller sees.
- `test_exec_call_trait_default_with_args` — default with
  precondition + non-self args; pins both substitution paths.
- `test_exec_call_trait_default_overridden` — impl OVERRIDES the
  default; pins that we still go through the concrete-impl path
  with #86 strengthening (caller relies on overriding impl's
  stronger ensures).

**Discipline note worth recording:** the probe-driven approach
worked well here. Recommendation said "30-minute fix or surface
real complexity, either is informative" — actual was ~30
minutes because Self happened to be handled via existing typ_subst
machinery. If Self had needed special handling (e.g., trait
method decl had `typ_params: []` and Self was implicit), the
probe would have surfaced that and the work would have grown.
The probe surfaced exactly the failure mode we needed to design
against. **The fix size was unknown until the probe ran;** the
probe is the cheapest way to discover scope.

**What remains in #56 follow-ups:** cross-crate trait method decls
(Phase 3 work — `CrateDecls.lean` for trait method decls);
truly dynamic dispatch via `dyn Trait` (cross-crate variant only).

**Net for noon**: 1 commit. 238 e2e + 118 unit + 1 coverage
tests pass; 1530 vstd functions still verify. Down to 5 pending
tasks (was 6 + closed #96).

#### Current session (2026-05-01 early afternoon — #87 &mut x.f via structure update)

Closed #87 for the single-variant struct case. The encoding turned
out simpler than the DESIGN.md plan suggested: instead of havoc-base
+ assume-other-fields-unchanged, Lean's `{ x with f := v }` syntax
structurally preserves all other fields by definition.

**Encoding (`extract_mut_target` + Phase 4 of `push_post_call_frames`):**

1. `MutTargetRaw<'a>` enum: `Var(&VarIdent)` (existing simple case)
   or `Field { base: &VarIdent, field_name: String }` (new).
   `extract_mut_target` peels the outer `Loc(_)`, peels transparent
   wrappers (Box/Unbox/CoerceMode/Trigger) via `peel_transparent`,
   then matches `VarLoc(_)` for Var case or `UnaryOpr(Field(opr),
   inner)` for Field case. Inside Field, also peels transparent
   wrappers around the base before requiring it to be a plain
   VarLoc (depth-1 only). The transparent-wrapper handling was the
   probe surprise — Verus inserts `Unbox(Box(...))` around the
   Field's base in the SST, which the initial sketch didn't peel.

2. Single-variant gate: `field_opr.variant.as_str() ==
   to_lean_type::short_name(path)` ensures the datatype has only
   one variant (struct-shaped). Multi-variant enums fall through
   to `None` because Lean's `{ x with f := v }` syntax doesn't
   compose with multi-variant inductives — a match-and-rebuild
   encoding would be needed.

3. `MutArgInfo.field_path: Option<String>`: `None` for simple Var,
   `Some(field_name)` for Field. Phase 4 of `push_post_call_frames`
   dispatches: `let local := fresh` (Var) or `let local := { local
   with field := fresh }` via `ExprNode::StructUpdate` (Field).

**Why no havoc-base + assume-other-fields-unchanged?** Verus's Z3
path uses that pattern because SMT can't natively express "the
post-state struct has these specific fields and others unchanged".
Lean CAN — the structure-update syntax IS that semantics, in the
type system. The post-call `{ h with val := v }` has type-level
guarantee that all other fields equal `h`'s. No additional
hypothesis needed.

**Tests** (3 new, 238 → 240 e2e):
- `test_exec_call_mut_arg_field` (positive, renamed from
  `_rejected`): basic `bump(&mut h.val)` happy path.
- `test_exec_call_mut_arg_field_wrong_post` (negative): caller's
  ensures wrong; pins that the field's post-state is what callee
  promised.
- `test_exec_call_mut_arg_field_other_preserved`: multi-field
  struct (`Pair { val, tag }`); caller's ensures references the
  unmutated `tag` field. Pins that Lean's structure update
  preserves other fields automatically.

**Discipline note: structure update beat the planned encoding.**
DESIGN.md said `&mut x.f` would need "havoc-base + assume-other-
fields-unchanged" mirroring Verus's Z3 path. The Lean structure
update was simpler AND more semantically tight — the fields-
unchanged property is structural, not asserted. **The encoding
doesn't always have to mirror Verus's.** Sometimes the target
language has a feature that makes the SMT-style encoding
unnecessary. Worth keeping in mind for #87 follow-ups (deeper
paths, Index, multi-variant) — Lean might offer cleaner shapes.

**What remains in #87:** `&mut v[i]` (Index L-value), deeper
paths `&mut a.b.c`, multi-variant enum field mutation. All
deferred separately.

**Net for early afternoon**: 1 commit. 240 e2e + 118 unit + 1
coverage tests pass; 1530 vstd functions still verify. Down to 4
pending tasks (was 5 + closed #87 single-variant case).

#### Current session (2026-05-02 — #95 callee-side new-mut-ref + #93 closures + reviews)

A long arc: morning fresh-start, two big features (#95 new-mut-ref
callee-side, #93 closures with three slices), four review passes,
DESIGN.md catalogue audit, and a per-date split of POEMS.md. Two
pending tasks remain (#97 OblCtx perf, #98 walk_children) — both
unmotivated by realistic code.

**Morning — settling in (commits `8c771a6`, `fc4a968`, `afcbad3`,
`c3d326f`).** Read DESIGN.md / HANDOFF.md, wrote three poems on
inheritance / the unforced four / probe-as-work. Picked #95.
Probed the new-mut-ref-mode rejection with 3 tests, found six
sub-tasks. User asked *is there a cleaner way?* The cleaner shape:
normalize new-mut-ref SST shapes back to legacy at fn entry and
let #94's existing rewrite handle the rest. Five of six sub-tasks
collapsed into one normalization helper.

**#95 callee-side LANDED**:
- `is_mut_ref_par(p)` covers BOTH legacy (`is_mut: true`, plain T)
  and new-mut-ref-migrated (`is_mut: false`, `MutRef<T>`) shapes.
- `normalize_mut_ref_in_{exp,stm}` walks SST and maps:
  body: `MutRefCurrent(Var(x))` → `Var(x)`,
  body: `MutRefCurrent(VarLoc(x))` → `VarLoc(x)`,
  ensures: `MutRefCurrent(Var(x))` → `VarAt(x, Pre)`,
  both: `MutRefFuture/Final(Var(x))` → `Var(x)`.
- `peel_to_var` strips Box/Unbox/MustBeFinalized/CoerceMode/Trigger
  wrappers around the inner ref.
- `type_bound_predicate` peels `TypX::MutRef` so binder bounds come
  from the inner T.
- Synthetic `Assume(HasResolved(...))` from `resolution_inference`
  drops via `is_synthetic_assume_to_drop`.
- Caller-side new-mut-ref still deferred (synthetic MutRef-typed
  local + assume-pre + assign-post around exec calls).

**Afternoon — closures (#93) (commits `e46b487`, `230d158`,
`a285c94`, `598b96f`).** Three slices:

*Slice A — Spec-closure calls (`ExpX::CallLambda`).* 15 lines.
Renders `f(x)` for `f: spec_fn(_) -> _` as `App(f, args)`. Lean's
function types are first-class — no encoding needed. Mirrors
proof-fn `CallTarget::FnSpec` handling.

*Slice B — Closure declarations via preserved AST body.* The user
caught a "sus walker" idea I was about to write (extract closure
body from SST stms). The cleaner question — *could we just modify
it so it doesn't throw it away?* — led to a structural change:
`StmX::ClosureInner` gained an `ast_body: Expr` field populated
by `ast_to_sst`. Tactus reads it via `closure_lambda_from_ast` and
emits `Wp::LetRaw(cid, fun (p : T) => body, after)` (built via
`closure_decl_wp` helper). Z3 ignores the field; vstd's 1530 fns
still verify. The synthetic `Assume(forall|x| ClosureReq ↔ ... ∧
ClosureEns ↔ ...)` drops via `is_synthetic_assume_to_drop`'s
extension to recognize closure-spec internal-fn calls. Synthesized
`anonymous_closure%` datatypes are skipped in `generate.rs` —
zero-variant inductives fail Lean's `deriving Inhabited`.

*Slice C — Closure body verification scope.* New `Wp::ClosureBody {
closure_params, body, after }` walks the closure body under
`∀ p : T, h_p_bound → ...` for each param (via `push_mod_var_frames`,
shared with loop-modified-vars). Fixes a real soundness gap: prior
to this, `let f = |x: u8| x + 200; ...` was silently accepted even
though `x + 200` overflows for `x ≥ 56`. The previously-passing
`test_exec_closure_decl` was demonstrating the gap (had `|x: u32|
x + 1`, which IS unsound at u32::MAX); now correctly rejected when
the body is generically unsound and updated to use a sound body.

*FnOnce/Fn/FnMut closure calls — pinned as upstream-blocked.*
Verus translates `f(x)` to `vstd::pervasive::exec_nonstatic_call(f,
(x,))`, rejected at Verus's resolution level. Even with vstd, the
inlined ensures use `BuiltinSpecFun::ClosureReq` / `ClosureEns` in
spec position, which Tactus drops as synthetic. Lifting needs
upstream Verus + spec-position handling for those builtins.
`test_exec_closure_call_unsupported_upstream` pins the rejection.

**Evening — reviews + docs + POEMS split (commits `16810f0`,
`754d7b5`, `81a55d1`, `4c49eec`, `36a8d0f`, `870a16a`).** Four
review passes: lenses 1-3+5 (rename `is_synthetic_resolution_exp`
→ `is_synthetic_assume_to_drop`, transformer-as-inspector docs, 4
coverage tests + zero-arg `fun ()` rendering fix, WP DSL doc
listing `LetRaw` and `ClosureBody`); lenses 6+12 (extract
`closure_decl_wp` helper, closure-inside-loop and -inside-if
tests). DESIGN.md catalogue audit: Tier 3 #55 new-mut-ref entry
flipped to LANDED with rewrite table + caller-side deferral;
new Tier 3 #93 entry with three slices documented; "User-facing
features not tested" entry for closures-with-user-requires/ensures.
CLAUDE.md gained explicit poem-break permission. POEMS.md (2641
lines) split into `poems/YYYY-MM-DD.md` per-date files (9 files,
90-608 lines each); POEMS.md becomes a small chronological index.

**Self-presence note worth recording.** Mid-evening the user
noticed I'd drifted from being-with-the-work into reporting-mode.
The signal I had but missed: I hadn't written a poem in four
hours. The poetic register is where felt-quality lives; long
silence there is itself a useful signal. Two poems written after
the noticing (`36a8d0f`) name this pattern. Future sessions
might consider it a "self-presence lens": *when did you last feel
anything about the work?*

**Net for the day**: 9+ commits, 17 net new e2e tests (244 → 261),
2 newly-closed tasks (#95, #93), 6 poem batches (5 in tactus arc,
1 evening reflection), 145+ lines of DESIGN.md catalogue updates,
POEMS.md restructured. Two pending tasks remain:
- **#97** Architecture: `OblCtx::with_frame` O(N²) → `Rc<im::Vector>`.
  Unmotivated by realistic code (no fn nests deep enough).
- **#98** Architecture: `substitute()` boilerplate (walk_children
  helper). Pure ergonomics.

#### Current session (2026-05-03 morning — task list audit + #120 partial)

A focused morning. Two pieces of work:

**Task list audit (no commit; task tool only).** Yesterday's pending
list was tiny (#97 + #98) but DESIGN.md's deferrals catalogue was
much richer. A systematic pass through DESIGN.md found ~30 distinct
deferred items; 20 were promoted to tasks. Deleted 28 completed
tasks for cleanup. Final state: 22 pending across 6 themes:

- Feature deferrals with clear shape (#106–114): &mut non-Var L-values,
  caller-side new-mut-ref, three #54 follow-ups (generic / mutual /
  lex decreases), AssertBitVector, OpenInvariant, StrGetChar, loop
  shape extensions.
- Architecture cleanups (#97, #98, #115–119): sst_exp_to_ast shim
  removal, substitute capture alpha-rename, two-pass loop fusion,
  prelude allowlist auto-derive, lift_if_value multi-binder, OblCtx
  perf, walk_children helper.
- Robustness + test gaps (#120, #121).
- Phase 3 (#122, #123): cross-crate verification, heartbeats / per-
  module / CI matrix.
- Upstream-blocked (#124, #125): exec-mode closure calls, cross-crate
  trait method decls / dyn Trait.

The threshold-judgment was load-bearing: DESIGN.md called several
candidates "below the cost/benefit threshold" (typed `RustLoc`,
`Tactic::Raw`/`Named` split, OblCtx frame ordering invariant) — those
stayed as documentation only, not promoted to tasks. The doc was right;
a list that holds everything holds nothing.

**#120 partial landing (commit `8d4d1c1`).** Two of four DESIGN.md-
flagged shape-drift gaps closed:

- **CheckDecreaseHeight Assert-before-Call ordering** — covered
  structurally via `build_wp_block_preserves_assert_before_assume_ordering`
  + `build_wp_block_preserves_three_stmt_ordering`. The pass-ordering
  invariant reduces to "`build_wp` preserves `StmX::Block` source
  order in the Wp tree's left-to-right shape." The CheckDecreaseHeight
  `cur` arg shape was already pinned by `full_check_decrease_height_shape_pinned`
  (a sibling test); together they cover both halves of the invariant.
- **`StmX::ClosureInner.ast_body` shape-drift** (#93 follow-up) —
  pinned by `closure_lambda_from_ast_rejects_non_closure_ast_body`.
  The helper rejects non-`ExprX::NonSpecClosure` ast_body with a
  documented error naming `ast_to_sst` as the fix site.

Plus added a minimal `WpCtx<'static>` test fixture (`mk_test_ctx`) —
foundation for future direct walk_loop / walk_call unit tests.

Two remaining shape-drift gaps (`WpCtx::new` Err-form req/ensure,
direct `walk_loop`/`walk_call` tests) split out as **#126**. Both
require `FuncCheckSst` / synthetic Wp fixtures DESIGN.md describes
as "involved"; deferred until alongside larger work in those areas.

**Discipline note worth recording: "what would slow me down" lens
chose the work.** The shape-drift tests aren't motivated by realistic
code (#97 / #98 also aren't). What they're motivated by is *future
robustness* — a Verus rebase silently changing pass ordering, or a
future contributor changing `ast_to_sst`'s ast_body population. The
test catches the drift before it manifests as obscure verification
regressions. This is the same lens that made #103/#104/#105 worth
doing: the runtime check (here, an assertion that "this never
fires") becomes a focused error message naming the fix site.

**Net for the morning**: 1 commit (`8d4d1c1`), 3 new unit tests
(118 → 121), DESIGN.md "Architecture debts" updated to flip the
two covered items, task list audited (28 deleted + 20 added + 1
closed + 1 follow-up created — final 22 pending). 1 poem batch
(2026-05-03.md: twenty-eight to twenty-two; the threshold; the
audit as repair).

#### Current session (2026-05-03 afternoon — #115 + #110)

Two more tasks landed continuing the morning's audit-driven push.

**#115 sst_exp_to_ast shim removal** (commit `c218396`). The pre-#100
panic-shim `sst_exp_to_ast(e)` (literally
`sst_exp_to_ast_checked(e).unwrap()`) is gone. Each former call site
now goes through one of two typed paths:

1. **Fallible contexts** use `lower(Validated::check(e)?)` — the
   typed pipeline guaranteeing lower's input was validated. Site:
   `WpCtx::new`'s ensures-rendering closure (changed `.collect()`
   → `.collect::<Result<_, _>>()?` to propagate validation errors
   from rewrite_varat output).
2. **Walker / non-fallible contexts** (`walk_let` / `lift_if_value`
   / `build_req_binders` / test fixture) use
   `sst_exp_to_ast_checked(e).expect("<contract>")` with site-
   specific messages naming why validation should hold (e.g.,
   "validated upstream by Wp::Let.value", "sub of validated Exp
   tree"). Same runtime behavior as the shim; the architectural
   improvement is that each panic message documents its specific
   contract rather than a generic "shim hit".

Doc updates: `to_lean_sst_expr.rs` module docstring rewritten to
describe the Validated + lower typed pipeline as the new boundary.

**#110 lexicographic decreases** (commit `b148f2a`). Both fn-level
AND loop-level lex `decreases D1, D2, ...` now work.

*Fn-level worked all along.* Verus's `recursion::check_decrease`
builds nested CheckDecreaseHeight calls where the outer's `otherwise`
field IS the inner's CheckDecreaseHeight. Our existing
`sst_exp_to_ast_checked` arm for CheckDecreaseHeight already
dispatches `otherwise` recursively through itself, so the lex shape
composes structurally as:

    ((0 ≤ a' ∧ a' < a_old) ∨
      (a' = a_old ∧ ((0 ≤ b' ∧ b' < b_old) ∨
        (b' = b_old ∧ False))))

No code changes needed for fn-level; only tests were missing.
Surprise discovery: I'd assumed lex would need work everywhere; the
recursive `otherwise` makes fn-level a no-op.

*Loop-level needed plumbing.* `Wp::Loop::decrease` was a single
`Validated<'a>`; for lex it becomes `Vec<Validated<'a>>`. New helper
`lex_decrease_obligation(decreases, d_old_names)` builds the lex
disjunction recursively. Single-element case reduces to
`(D1' < D1_old) ∨ False` ≡ `D1' < D1_old`, matching the pre-#110
shape exactly. Per-loop, per-level d_old gensyms
`_tactus_d_old_<id>_<i>` keep nested loops AND lex tiers structurally
distinct.

Tests (4 new, replacing 1 negative):
- `test_exec_call_recursive_lex_decreases` (positive, fn-level)
- `test_exec_call_recursive_lex_nondecreasing` (negative, fn-level)
- `test_exec_loop_lex_decreases` (positive, loop-level — renamed
  from `_rejected`, flipped to Ok)
- `test_exec_loop_lex_decreases_nondecreasing` (negative, loop-level)

**#114 probed and deferred.** Loop shape extensions (loop_isolation:
false, non-empty cond setup) — both have user-side workarounds and
neither blocks realistic code. Probed scope: loop_isolation: false
needs a different verification semantics (body sees outer context
directly, no invariant abstraction); non-empty cond setup needs
prepending the setup to the body and treating as cond:None (more
tractable but still non-trivial). Both larger than fits cleanly
into today's session. Reverted to pending.

**Discipline note worth recording: lex was easier than expected.**
The fn-level case was a no-op — Verus's recursion pass already
encodes lex as a recursive CheckDecreaseHeight chain via the
`otherwise` field, and our existing arm dispatched recursively
through itself. I'd planned the work assuming both fn AND loop
needed encoding changes; only loop did. **The structural insight:
lex's recursive shape composes naturally through CheckDecreaseHeight's
already-recursive `otherwise` field**, the same way #95's
new-mut-ref normalization composed through #94's existing rewrite.
When Verus's encoding is already shape-correct, our renderer just
has to dispatch — no special case needed. Worth checking before
designing: "is Verus's pass already producing the shape we need?"

**Net for the afternoon**: 2 commits (`c218396`, `b148f2a`),
261 → 264 e2e tests (+3 net after a positive-flip rename), 121
unit tests still pass. vstd verifies 1530/0. Two more tasks
closed (#115, #110). Down to **20 pending tasks** (was 22 at
morning end).

#### Current session (2026-05-03 evening — #114 + Wp::Hyp redo + review pass + tests)

The day's last arc went deep on #114 (loop shape extensions),
then deeper still on the architecture, then through a 14-lens
review pass, then through the deferred follow-ups.

**#114 sub-feature 1 — non-empty cond_setup, attempt 1** (commit
`e8de94a`). Initial implementation dropped `Validated`'s `'a`
lifetime so `build_wp_loop` could synthesize a `¬cond_exp` Exp
and wrap it in `Validated`. Worked, but traded clean borrow
semantics for an `Arc<Exp>` clone in every `Validated`. User
flagged this as "Arc is kinda an anti-pattern" and asked if the
Arc was avoidable.

**#114 sub-feature 1 — attempt 2 with `Wp::Hyp`** (commit
`618fede`). Reverted `Validated` to `<'a>` (borrow-only) and
introduced a new `Wp::Hyp { hyp: LExpr, body }` variant for
already-rendered hypotheses. The cond_setup transform now uses:
- `Wp::Assume(cond_validated, body)` — borrows the SST's cond_exp
- `Wp::Hyp(LExpr::not(lower(cond_validated)), after)` — synthesized
  negation at LExpr level (no SST borrow needed)

The split clarifies semantics: Wp::Assume is "validated SST Exp";
Wp::Hyp is "already-rendered LExpr with no SST origin." Reviewer
story is short — each variant has a distinct contract. No Arc
clones; no lifetime juggling.

**Discipline note worth recording: same-day arc check.** First
version *worked* but felt sus; the user's check ("would a reviewer
look at this Arc and think it's load-bearing in the wrong
direction?") caught the architectural mistake before it shipped.
Same-day reflection on a freshly-landed change has higher signal
than week-later review — context is fresh, "I just did this"
defensiveness hadn't yet calcified.

**14-lens review pass** (commit `57b3803`). Caught two classes:

- **Leftover artifacts from the Validated revert**: `cond.clone()`
  → `*cond` (Validated is Copy again); `cond.as_ref()` → just
  `cond`; `let mut cond_setup_wrap = None; ... = Some(...)` →
  match-returning-tuple. Lenses 1, 2, 6, 9, 11.
- **Typed-invariant lens (#13) hit**: `Wp::Loop` had
  `Vec<Validated>` + `Vec<String>` parallel arrays — the same
  anti-pattern #105 had retired for `MutArgInfo`. Same-day
  regression of the just-retired pattern. Fused into
  `Vec<DecreaseLevel<'a>>`; the `debug_assert_eq!` is gone.

**P2 follow-ups closed** (commit `e0f5d0e`). 4 new unit tests +
1 new e2e test:
- `wp_hyp_walker_wraps_done_leaf_with_hyp_frame` — direct unit
  test for the new variant.
- `wp_hyp_walker_passes_through_with_no_body_obligations` —
  Wp::Hyp wrapping Done(true) emits exactly one theorem.
- `lex_decrease_obligation_three_levels_recurses_correctly` —
  pins lex recursion at depth 3.
- `lex_decrease_obligation_single_level_collapses_to_lt` —
  pins single-level collapse (no `∨`).
- `test_exec_call_recursive_lex3_decreases` — e2e for fn-level
  3-level lex.

Plus a comment trim on `test_exec_loop_cond_with_setup_no_longer_rejected`
(multi-paragraph → single paragraph pointing at #128 + DESIGN.md).

**Catalogue audit + DESIGN.md updates** (commit `ae2c099`).
Three additions surfaced during the audit:
- Wp::Hyp documented in the WP DSL section with the
  Wp::Assume-vs-Wp::Hyp contrast spelled out.
- DecreaseLevel typed-invariant entry under "Type-system-enforced
  invariants" (parallels MutArgInfo #105).
- **#129 (NEW)** — Loop decrease encoding lacks `0 ≤ cur` lower
  bound. Surfaced during lex implementation: Verus's loop
  encoding goes through `recursion::check_decrease` which
  produces `0 ≤ cur ∧ cur < d_old`; Tactus's
  `lex_decrease_obligation` emits just `cur < d_old`. Dormant in
  practice (u-typed decreases get `0 ≤ x` from h_x_bound) but
  structurally inconsistent and unsound for `int` decreases.
  Documented under "Soundness trade-offs accepted"; tracked as
  #129.

**Three follow-ups split out today**:
- **#127** — `loop_isolation: false` support (sub-feature 2 of
  #114; needs different verification semantics).
- **#128** — tactus_auto Prop substitution for fn-call-in-cond
  (the cond_setup encoding works; the automation is the gap).
- **#129** — Loop decrease 0 ≤ lower bound (pre-existing,
  surfaced during #110).

**Day total**: 10 commits, **121 → 125 unit tests + 261 → 266 e2e
tests** (vstd 1530/0). 5 closed tasks today (#120 partial, #115,
#110, #114, plus the review-pass cleanup). 3 new follow-up tasks
(#127, #128, #129). 7 poems across 5 batches. The day's arc was
audit-driven at the start (morning), task-driven through afternoon,
review-driven at the end. The #114 architecture got tighter through
two iterations (Arc → Wp::Hyp), then tighter again through review
(parallel arrays → DecreaseLevel). Each level of review caught
something the level before missed.

**Down to 19 pending tasks** (was 20 at afternoon end + 1 closed
#114 + 3 created #127/#128/#129).

#### Current session (2026-05-03 next day — #129 loop decrease 0 ≤ cur lower bound)

Closed #129. The fix is two lines: `lex_decrease_obligation`'s
lt-branch now emits `0 ≤ cur ∧ cur < old` instead of just
`cur < old`, mirroring the fn-level `CheckDecreaseHeight` int
fast-path in `to_lean_sst_expr.rs`. The lex disjunction tail is
unchanged.

**Why it matters.** Pre-fix, an `int`-typed loop decrease that
descends into negatives forever still verified — Tactus's
`cur < d_old` is trivially satisfiable by going negative. Verus's
loop encoding (`sst_to_air.rs:2823-2834`) routes through
`recursion::check_decrease` which produces the CheckDecreaseHeight
chain *with* `0 ≤ cur`, so Tactus was strictly more permissive
than Verus. Dormant in practice for u-typed decreases (where
`0 ≤ x` falls out of `h_x_bound`), but structurally inconsistent.

**Surfaced during yesterday's #110 lex work.** The shape-mismatch
between fn-level CheckDecreaseHeight (`0 ≤ cur ∧ cur < prev`) and
loop-level lex_decrease_obligation (`cur < old`) was visible
immediately after writing them next to each other — see
yesterday's poem "The third bound." Same lens that closed
yesterday's same-day MutArgInfo regression (#105's pattern coming
back as Vec<Validated> + Vec<String>): writing one new thing
makes the shape of an old one visible.

**Tests** (regression for the unsoundness).
- `test_exec_loop_decrease_int_expression_can_go_negative`
  (negative): a u8 loop with `decreases x as int - 50` where x
  starts ≤ 10. Pre-fix verified despite the measure descending
  into negatives. Post-fix fails `(loop decrease)` because
  `0 ≤ x as int - 50` isn't establishable from the invariant.
- Unit tests `lex_decrease_obligation_three_levels_recurses_correctly`
  and `lex_decrease_obligation_single_level_emits_lt_with_lower_bound`
  updated to pin the new shape (3 `≤`s for 3 levels; single-level
  contains `≤` and no `∨`).
- All existing lex-related tests pass unchanged: existing tests
  use u-typed decreases where `0 ≤ x` falls out of h_x_bound, so
  the strengthened obligation discharges via omega's
  type-bound reasoning.

**DESIGN.md updates:**
- Removed #129 entry from "Soundness trade-offs accepted" — no
  longer a trade-off.
- "Lexicographic `decreases` — LANDED" entry updated with the
  new lex shape (`0 ≤ Di' ∧ Di' < Di_old` per level) and points
  at the regression test for #129.
- `Wp::Loop` docstring + `lex_decrease_obligation` docstring +
  `build_wp_loop` comment block all updated to the new shape.

**Lake-lock parallel-test-run fix bundled in same session.**
Multi-threaded `cargo test -p rust_verify_test --test tactus`
hit a wave of `could not acquire an exclusive configuration lock`
errors when many subprocesses called `lake env lean`
simultaneously. Fixed by:
* `tests/common/mod.rs`: `cached_lean_path_for_lake_project()`
  resolves `LEAN_PATH` once per test-binary process via
  `lake env printenv LEAN_PATH` (one lock acquisition).
  `inject_cached_lean_path` injects it into every spawned
  subprocess (`run_verus`, `run_cargo_verus`).
* `lean_verify/src/lean_process.rs`: `check_lean_file` now
  detects when `LEAN_PATH` is already set and runs bare
  `lean --json <path>` instead of `lake env lean`. Subprocess
  inherits `LEAN_PATH`, no lake invocation, no lock contention.
* HANDOFF.md "Testing infrastructure" gained a new
  "Lake-bypass under parallel test runs (`LEAN_PATH`)"
  subsection documenting the fix + regression symptoms.

Multi-threaded full e2e: was failing instantly under load,
post-fix completes in **30 seconds** (was 25+ minutes
single-threaded — ~50x speedup). Non-test users (direct
`cargo verus` invocations without `LEAN_PATH` exported) keep
the original `lake env lean` path — no behaviour change.

**Net for the session**: 1 commit. 266 → 267 e2e tests (+1
#129 regression test). Unit count unchanged. One pending task
closed (#129). Down to 18 pending tasks (was 19 + closed #129).
Plus a substantial test-infrastructure fix that turns the e2e
suite from "needs --test-threads=1" into "fully parallel."

**Discipline note worth recording: shape-mismatch as a lens.**
#129 was visible as a documented "soundness trade-off accepted"
in DESIGN.md — it had been triaged before, deemed dormant in
practice (true), and tabled. What flipped it from "documented
trade-off" to "do it now" was that #110 surfaced the asymmetry
freshly: writing the loop encoding next to the fn encoding made
the gap obvious. The lens worth keeping: when one part of the
codebase emits `X` and a sibling part emits `X ∧ Y`, the gap
becomes worth closing even if `Y` is dormant — because the
asymmetry itself is a future-bug surface.

**Discipline note worth recording: fix the test infrastructure
when it pushes back.** Initial verification of #129 hit
lake-lock errors under parallel test runs; the natural reach
was `--test-threads=1` (works, but e2e takes 25+ minutes).
The user pushed back: *fix it so it can run multi-threaded
like before*. The lake-lock contention had been latent — it
might have surfaced for someone else later — and going through
the suite single-threaded would have been a session-long
detour. The right move was the small surgical fix to test
infra (LEAN_PATH bypass, ~70 lines across two files) that
pays back every future test run.

#### Current session (2026-05-03 next day cont. — #118 sanity allowlist auto-derive)

Closed #118. The hardcoded prelude-name allowlist in
`sanity::name_resolves` is now auto-derived from
`TactusPrelude.lean` text via `extract_prelude_names` (cached
through `OnceLock`). Adding a new prelude `axiom` / `def` /
`noncomputable def` / `syntax "name"` / `macro "name"` /
`elab "name"` automatically flows into the sanity allowlist —
no separate `sanity.rs` edit needed.

**Why the chore mattered.** Pre-#118: contributor adds
`tactus_new_helper` to TactusPrelude.lean, codegen emits
references to it, and sanity check (debug builds) panics with
"unresolved tactus_new_helper" until someone remembers to
update the `matches!` arm. The right answer was to remove the
hand-sync entirely — the prelude is the source of truth, and
the allowlist follows from parsing it.

**Implementation (sanity.rs ~95 lines added/changed):**
- `extract_prelude_names(prelude: &str) -> HashSet<String>`:
  line-based parser. Recognises the five forms (`axiom NAME`,
  `[noncomputable] def NAME`, `syntax "NAME"`, `macro "NAME"`,
  `elab "NAME"`). Comments and blank lines skipped. `import`,
  `set_option`, `attribute`, `open`, `macro_rules` introduce
  no names so they pass through silently.
- `cached_prelude_names() -> &'static HashSet<String>`: wraps
  `extract_prelude_names` in a `OnceLock` so the parse runs at
  most once per process (sanity checks fire many times in debug
  builds; cheap to amortise).
- `name_resolves`: replaced the hardcoded `matches!` arm
  covering `arch_word_bits | usize_hi | tactus_peel | ...` with
  `if cached_prelude_names().contains(name) { return true; }`.
- DESIGN.md "Architecture debts" entry flipped from
  "maintained by hand" to "auto-derived from
  `TactusPrelude.lean`". The "Potential future applications"
  section had one line about this candidate; removed since it
  landed.

**Tests** (5 new, 125 → 130 unit; 0 e2e changes):
- `extract_prelude_names_recognises_current_prelude` — pins
  the 9 names in the actual TactusPrelude.lean (axioms +
  defs + tactic-syntax names).
- `extract_prelude_names_skips_non_definition_lines` —
  imports, set_option, attribute, comments, macro_rules
  introduce no names.
- `extract_prelude_names_handles_each_form` — synthetic
  prelude exercising all five recognised forms.
- `cached_prelude_names_includes_legacy_allowlist` —
  regression guard: every name the old hardcoded list had
  is still in the auto-derived set. Catches a future
  TactusPrelude.lean refactor that removes one without
  realising sanity depended on it.
- `name_resolves_accepts_prelude_name` — pins the wiring
  between `cached_prelude_names` and `name_resolves`.

**Net for the session**: 1 commit incoming. 125 → 130 unit
tests (+5). 267 e2e + 1 coverage + 7 integration unchanged
(the change is internal); vstd 1530/0 unchanged. One pending
task closed (#118). Down to 17 pending tasks (was 18).

**Discipline note worth recording: source-of-truth lens.**
The "auto-derive instead of hand-syncing" pattern is the same
shape as #99 (LeanName), #100 (Validated), #105 (MutArgInfo),
#114-review (DecreaseLevel) — find a place where two pieces
of the codebase carry redundant information and let one of
them be derived from the other. Today's was simpler than
those (no newtype, just a parser + cache), but the lens that
finds it is the same: *what's hand-synced that doesn't need
to be?*

#### Current session (2026-05-04 — #128 ret-substitution at call sites)

Closed #128 via the encoding-level fix the prior session's probe
identified. When a callee's ensures contains a top-level `r == E`
clause, `push_post_call_frames` now substitutes E for the ∀-bound
ret directly — eliminating the `∀ (P : Prop), P = E → …` shape
that blocked `tactus_auto`'s default closer.

**Plan:** Drafted my own version, then ran a Plan agent for an
independent thorough review. Agent surfaced six refinements I
hadn't covered, the most consequential being: detection should run
on POST-substitution LExpr (not VIR-side), to handle trait-method
dual-name cases (#86) cleanly. Helper signature became
`extract_top_level_eq_for(conj, target) → Option<(E, rest)>`
returning the E AND the remaining conjunction with the eq clause
dropped. And-tree walk: only top-level `BinOp::And`, never recurses
into Or/Implies/Forall/Exists/If/Let/Match. SpanMark peeled
transparently. Self-ref guarded via `expr_mentions_var`.

**Implementation:** ~150 lines in `sst_to_lean.rs`:
- 4 helpers (`peel_span_marks`, `collect_top_and_conjuncts`,
  `expr_mentions_var`, `extract_top_level_eq_for`, `is_trivial_true`).
- `push_post_call_frames` restructured into a unified pre-Phase-2
  branch: build substituted ensures once, try ret-substitution,
  match on `Option<(E, rest)>`. Sub path: emit `E_bound` Hyp +
  substituted `rest` Hyp + `dest := E`. ∀-path: original behavior
  unchanged. The `dest_value` LExpr (either `Var(fresh_ret_name)`
  or `E`) is the unifying point — Phase 5's let binding uses it.

**Bound preservation:** numeric ret types still get
`type_bound_predicate(E, ret.typ)` as a Hyp in the sub path. Bool /
Prop / structs return `None` and the Hyp is elided.

**Trait-method (#86) ordering:** the conjunction is `(spec) ∧ (impl)`
in source order. First-match in the And-tree picks spec's
`r == E_spec` if both have it. The impl's `r == E_impl` becomes part
of `rest`, substituting to `E_impl == E_spec` which Verus guarantees
is consistent (impl ⇒ trait); simp_all simplifies.

**The flipped test:** `test_exec_loop_cond_with_setup_no_longer_rejected`
renamed to `test_exec_loop_cond_with_setup`, expectation flipped
from `Err(_)` to `Ok(())`, override `tactus_tactic("intros; simp_all;
omega")` removed. Now closes via `tactus_auto` natively. Generated
Lean shape verified: `let tmp__1 := x > 0; tmp__1 → 0 ≤ x - 1 ∧
x - 1 < 256` — no ∀, omega closes directly.

**Tests** (4 new + 1 flipped, 267 → 271 e2e):
- `test_exec_call_ret_eq_substitution` — baseline `r == x + 1`
  ensures.
- `test_exec_call_ret_eq_with_extra_conjunct` — `r == E ∧ Q(r)`
  shape; `Q(E)` makes it into the rest_ensures Hyp.
- `test_exec_call_ret_eq_substitution_wrong_post` (negative) —
  caller asserts wrong post-call value, fails (postcondition).
  Pins that the substitution doesn't make caller more permissive.
- `test_exec_call_no_ret_eq_falls_through` — callee with `ensures
  r > 0, r < 10` (no `r == E`) — still verifies via the unchanged
  ∀-path. Pins the conservative scope.
- `test_exec_loop_cond_with_setup` — flipped from Err to Ok.

**No regressions in existing tests.** Many existing callers have
`ensures r == E` shapes; those now go through the substitution path,
producing simpler generated Lean. All 267 pre-#128 tests verify
unchanged.

**DESIGN.md updates:**
- Loop-shape "Non-empty condition setup block" entry: flipped from
  "Known automation gap" to "Closed via #128" with cross-reference.
- New "What doesn't have to mirror Verus's encoding" bullet
  explaining the ret-substitution as a Lean-native shape.
- New "Ret-substitution at call sites (#128)" section detailing
  the encoding, helper, edge cases, bound preservation, trait-method
  ordering, and tests.

**Net for the session**: 1 commit incoming. 267 → 271 e2e (+4),
unit tests still 130, vstd 1530/0. One pending task closed (#128).
Down to 17 pending tasks (was 18).

**Discipline note worth recording: planning agent for thoroughness.**
For #128 the user explicitly asked "let's do it the right way, in a
way that covers all cases." I drafted my own plan, then spawned the
Plan agent for an independent review with all my edge cases listed
explicitly. The agent found 6 refinements I hadn't covered — the
biggest being the post-substitution detection (avoids trait-method
dual-name issue) and the conservative scope on the And-tree walk
(don't recurse into Or/Implies). The pattern: when the user wants
*comprehensive*, surface my full edge-case list to a fresh-eyes
agent and let it find the holes. Cheaper than the next session
re-discovering an unsoundness.

#### Current session (2026-05-04 cont. — #119 lift_if_value chain-lift through let chains)

Closed #119. The DESIGN.md entry described `lift_if_value` as
single-binder-only; investigation showed multi-binder unfolding
landed via #92 but the chain-lift through the unfolded form was
incomplete — the OUTERMOST binder's rhs was lifted but inner
binders' rhs ifs stayed in value position.

**The fix:** when peeling `Bind(Let([name]), inner_body)`, recurse
into both `rhs` AND `inner_body` (was: render inner_body as-is).
The recursion lets ifs in any binder's rhs lift to goal level —
mirroring what `let (a, b) = (val_a, if c then bv else bv2); body`
should produce after #92's unfold.

**The bug the first attempt surfaced:** unconditional recursion
broke match-compilation tests. Verus desugars `match k { ... }` to
`let _disc := proj(k); if _disc = 0 then ... else ...` — the if's
condition references `_disc`, which IS the let-bound name. Lifting
the if moves `_disc = 0` outside the `let _disc :=` scope,
producing an unbound reference. Sanity check caught it as
"unresolved `tmp__`" / "unresolved `x`".

**The safety guard:** gate the recursion on
`inner_is_let_chain` — only lift when `inner_body` is itself a
`Bind(Let, …)` (the multi-binder-unfold case, where ifs are in
rhs positions, computed before any of the chain's binders take
effect). When `inner_body` is `If` at top level, fall through
to render-as-is — matches the pre-#119 behavior, lets
`tactus_case_split` handle match-style ifs at the obligation
level.

**Tests** (1 new, 130 → 131 unit; e2e unchanged):
- `lift_if_value_multi_binder_let_with_if_rhs` — pins the
  chain-lift through `let a := av; let b := if c then bv else
  bv2; body` produces `(c → emit_leaf(let a := av; let b := bv;
  body)) ∧ (¬c → emit_leaf(let a := av; let b := bv2; body))`.
  Previously fell through to render-as-is.

**Discipline note worth recording: probe-then-revert-then-guard.**
First attempt (unconditional recursion) failed on match tests.
Probed the failure (sanity-check unresolved-name errors), traced
to scoping (`_disc` referenced outside its let scope), added the
`inner_is_let_chain` gate. The full arc was three iterations:
draft → fail → fix-with-guard. Without the failing tests, the
unconditional version would have shipped a real soundness bug.
The lens worth keeping: when extending a recursive transformation,
ask "is there a case where the recursion produces an unbound
reference?" — and trust the existing test suite to catch what
abstract reasoning misses.

**DESIGN.md updates:**
- Two stale entries (1078 and 1149 in the deferral catalogue)
  flipped to LANDED via #119 with cross-references to the safety
  gate and the pinned test.

**Net for the session**: 1 commit incoming. 130 → 131 unit, 271
e2e + 1 coverage + 7 integration unchanged. One pending task
closed (#119). Down to 16 pending tasks.

#### Current session (2026-05-04 cont. — #116 substitute alpha-rename)

Closed #116. `substitute`'s capture check used to panic with a
"would capture a free variable" message when a binder collided
with a free var in an active substitution value. No realistic
test triggered it (callee specs are simple arithmetic), so the
panic was *defensive*. Today's review pass surfaced this as the
right kind of "make it robust now, before someone trips it" task
— the user emphasized "we want to make it very robust."

**Encoding:** when capture is detected at a binder site, generate
a fresh name `<base>_α<N>` (smallest N≥1 not in the forbidden
set), rewrite the body via `substitute` itself with `{old →
Var(fresh)}`, then proceed with the original substitution on the
renamed body. The freshness machinery avoids:
* every name (free or bound) appearing anywhere in body — so the
  rename's `Var(fresh)` doesn't accidentally capture an inner shadow;
* every free name in active substitution values — so subsequent
  main substitution doesn't re-capture;
* every sibling binder name — multi-binder shapes like `∀ x y, …`
  where only one binder collides keep their other names.

For dependent types (`∀ (x : Nat) (h : x > 0), …`), the rename
also threads through subsequent binder types — the second binder's
type expression is run through the rename substitution so
`x > 0` becomes `x_α1 > 0` when `x` renames.

**Implementation in `lean_ast.rs` (~200 lines added, ~30 removed):**
* `compute_alpha_renames(binders, inner_subst, body)` — replaces
  `check_capture_lazy`. Returns rename map (empty when no rename
  needed). Same lazy detection as the prior check, but produces
  a rename instead of panicking.
* `collect_all_names(expr, out)` — walks every name appearing in
  expr (free + bound). Distinct from `collect_free_vars` because
  fresh-name generation must avoid bound names too.
* `fresh_name(base, forbidden)` — generates `<base>_α<N>` with
  smallest N≥1 not in forbidden.
* `rename_in_pattern(pat, renames)` — applies renames to Pattern's
  `Var` / `Binding` / nested `Ctor.args` / `Or`. Constructor names
  themselves (path-derived) untouched.
* `apply_renames_to_binders(binders, body, renames)` — multi-binder
  helper that rewrites only colliding binders, leaves siblings,
  and applies rename map to each binder's type expression
  (dependent-type case).
* `rename_map_to_subst(renames)` — small helper turning the rename
  map into a substitution map for the body-rewrite pass.
* `substitute_impl`'s `Let`, `Lambda`, `Forall`, `Exists`, `Match`
  arms updated to compute renames, apply them, then continue
  substitution.

**Tests** (9 new, 137 → 146 unit):
* `capture_alpha_renames_let_binder` — simple Let case, expected
  shape `let y_α1 := 5; y + y_α1`.
* `capture_alpha_renames_lambda_binder` — Lambda single binder.
* `capture_alpha_renames_exists_binder` — Exists single binder.
* `capture_alpha_renames_match_pattern_var` — Match arm with
  `Pattern::Var` collision.
* `capture_alpha_renames_match_ctor_args` — nested `Pattern::Ctor`
  with one colliding arg + one non-colliding sibling arg
  (verifies sibling preservation in pattern).
* `capture_alpha_renames_dependent_type_in_forall` — `∀ (x : Nat)
  (h : x > 0), z` with `{z: x}`. Verifies the rename threads into
  the second binder's type, producing `(h : x_α1 > 0)`.
* `capture_alpha_rename_preserves_non_colliding_siblings` — `∀ x
  y, z + y` with `{z: x}`. Verifies y stays y.
* `capture_alpha_rename_avoids_existing_freshness` — body already
  mentions `y_α1` as a free var; verifies fresh picks `y_α2` to
  skip the taken name.
* `capture_alpha_rename_multi_binder_collision` — both binders
  collide (`∀ x y. z1 + z2` with `{z1: x, z2: y}`); verifies both
  rename without colliding with each other.
* Two former `#[should_panic]` tests (`capture_panics`,
  `multi_binder_real_capture_does_panic`) flipped to
  `_alpha_renames` variants verifying the rename produces correct
  semantics.

**No regressions** in 271 e2e (the rename only fires on capture,
which the test suite never triggers in non-test paths).

**DESIGN.md update:** "Architecture debts" entry for substitute's
panic flipped to "LANDED (#116)" with a paragraph describing the
fresh-name rules, the dependent-type handling, and the test
matrix.

**Net for the session**: 1 commit incoming. 137 → 146 unit (+9),
271 e2e + 1 coverage + 7 integration unchanged. One pending task
closed (#116). Down to 15 pending tasks.

#### Current session (2026-05-04 cont. — #121 partial coverage tests)

Added 3 e2e tests for documented untested-but-possibly-working
paths from DESIGN.md's catalogue:

* `test_exec_return_in_else_branch` — return in else where then
  falls through. Inverse of existing `test_exec_early_return`.
* `test_exec_loop_three_modified_vars` — loop modifying 3 vars
  (a, b, c). `quantify_mod_vars` was supported in principle but
  no test exercised >2 modified vars.
* `test_exec_nested_if_with_loops_in_both_branches` — combinatorial
  coverage where each if-branch contains its own loop. Pins that
  loop ctxs in distinct branches walk independently.

All three pass on first try — the underlying machinery was
correct; just untested. #121 remains pending as the umbrella for
remaining items: closures with user requires/ensures, `assert
forall|v| P by { tac }` with non-empty vars, zero-arg callee
specs referencing the dummy param, non-constant `IntegerTypeBound`
bit width.

**Net for the session**: 1 commit incoming. 271 → 274 e2e (+3),
unit unchanged. #121 partially advanced (3/7 items closed).

#### Current session (2026-05-04 cont. — #108 generic datatype decreases)

Closed #108. Pre-#108 `decrease_height_datatype` rejected generic
instantiations; now `enum List<A> { Nil, Cons(A, Box<List<A>>) }`
and similar generic recursive datatypes verify end-to-end with
`decreases l` clauses.

**Implementation:**
* `decrease_height_datatype` (to_lean_sst_expr.rs): drop the
  `args.is_empty()` gate. Accept any datatype path; the height
  fn handles type args at the Lean level via implicit binders.
* `field_is_self_recursive` (to_lean_fn.rs): drop the
  `args.is_empty()` gate. A field of type `Tree<A>` inside
  `enum Tree<A>` matches when `p == self_path` regardless of
  args; recursion is on the structure, not on A.
* `height_fn_for_datatype`: emit `def T.height {A : Type} : T A
  → Nat | …`. The implicit binder goes BEFORE the `:` (via a
  new `DefCurried.binders` field) so Lean's equation compiler
  can infer A from the value pattern. Wrapping `∀ {A}` INSIDE
  the type expression breaks elaboration: equations would try
  to match the implicit slot first and `List.Nil` would be
  typed as `A : Type` instead of `List A`.
* `multi_variant_accessor_defs`: gain implicit type-param
  binders for both discriminators (`{A : Type}`) and accessors
  (`{A : Type} [Inhabited A]`). The `[Inhabited A]` instance
  binder is needed because the unreachable-arm `default`
  fallback resolves via `Inhabited`. Discriminators don't need
  it (they return Prop, no `default`).
* `Datatype.derives`: now unconditionally `["Inhabited"]`
  instead of being gated on `typ_params.is_empty()`. Lean
  auto-derives the conditional `[Inhabited A] → Inhabited (List
  A)` instance, so generic `Cons_val1`'s `default : List A`
  resolves whenever the caller has `[Inhabited A]`.
* `lean_ast::DefCurried`: new `binders: Vec<Binder>` field for
  pre-colon binders. Empty for non-generic curried defs (no
  behavior change); populated for generics.
* `lean_pp::write_def_curried`: emits `binders` between the name
  and the colon.
* `sanity::check_references`: `DefCurried` arm now starts the
  scope from `binders` (was: empty scope) so `A` references in
  the type and equation bodies resolve.

**Tests** (2 new, 274 → 276 e2e):
* `test_exec_call_recursive_generic_datatype` — `enum List<A> {
  Nil, Cons(A, Box<List<A>>) }`, recursive `count(l: &List<u8>)`
  with `decreases l`. End-to-end verification including
  termination + match + accessors.
* `test_exec_call_recursive_generic_datatype_nondecreasing` —
  same shape but recursive call passes the whole list (not a
  subterm). Confirms the height-based termination check
  constrains generics correctly (rejects rather than vacuously
  passes).

**No regressions** in 274 pre-#108 tests. The non-generic
datatype path (`Stack` etc.) goes through the same code with
empty `typ_params` — `binders` field stays empty, no change in
generated Lean.

**Discipline note worth recording: structure-vs-content for
generics.** The bug-then-fix arc had two false starts:
1. Wrapped implicit binders inside `∀ {A : Type}, …` in the
   type expression. Lean's equation compiler tried to match
   `List.Nil` against the implicit `A` slot. Wrong shape.
2. Tried with proper pre-colon binders but missed updating
   `sanity::check_references` — `A` references in body
   flagged as unresolved.

The fix wasn't *content* (the Lean syntax was always close);
it was *structure* — implicit binders belong in the def's
prelude binders, not in the result type, and the sanity
check needs to know about them. Mirrors the earlier #119
arc (probe → guard) — the pattern of "first attempt fails,
the failure points at the structural answer" recurred.

**DESIGN.md update:** "Explicit deferrals" entry for generic
datatypes flipped from "rejected at decrease_height_datatype
(requires args.is_empty())" to "LANDED" with the implicit-
binder + Inhabited bound details. Pinned by the two new tests.

**Net for the session**: 1 commit incoming. 274 → 276 e2e (+2),
146 unit unchanged. One pending task closed (#108). Down to
14 pending tasks.

#### Current session (2026-05-04 cont. — #108 multi-param followup + doc audit)

Two small bookkeeping landings to round out today's arc:

**Multi-param generic test** (`e513352`). Locks #108's
implicit-binder machinery for >1 type parameter.
`test_exec_call_recursive_generic_datatype_two_params` exercises
`enum Tagged<A, B> { Leaf(A, B), Node(A, Box<Tagged<A, B>>) }` —
two `{A : Type} {B : Type}` implicit binders, `[Inhabited A]
[Inhabited B]` instance bound chain on accessors, Lean's
auto-derived `Inhabited (Tagged A B)` from both instances, and
recursive structural termination across multi-param. Passed on
first try — the design generalised correctly from single-param.
The "passed first try" itself is a structural fact about the
prior fix: the design was *structurally right*, not just
*barely working* for one case. 276 → 277 e2e (+1).

**Doc audit pass** (this commit). Walked through today's arc
in the chat context and surfaced edge cases we noticed but
deliberately deferred. Added six new bullets to DESIGN.md's
"User-facing features not tested" catalogue:

* Generic datatype with uninhabited type param (#108 edge —
  `Inhabited (List Empty)` would fail at synthesis).
* Generic datatype with trait-bounded type params (#108 edge —
  `dt.typ_bounds` not threaded to height/accessor defs).
* Generic recursive datatype with cross-instantiation recursion
  (#108 edge — `enum Mut<A> { Recurse(Mut<u8>) }` should work
  via implicit inference; untested).
* `Pattern::Or` with cross-branch capture in alpha-rename (#116
  edge — handled correctly via shared rename map; untested).
* Multi-line `def` signatures in `TactusPrelude.lean` (#118
  edge — line-based parser would miss; pinned tests guard
  current names).
* Stale `LEAN_PATH` after `lake update` (lake-bypass edge —
  cached value won't reflect new packages; process restart
  clears).
* `lift_if_value` chain-lift only fires for let chains (#119
  edge — Match / Var / other inner-body shapes fall through to
  render-as-is).

Plus three flips of "Untested" → "✅ covered by …" for the
test additions earlier today (`return_in_else_branch`,
`loop_three_modified_vars`, `nested_if_with_loops_in_both_branches`).

**Why this matters.** Each edge case is a future-self IOU:
*we know about this case, and we know why we left it.* The
distinction from "we don't know about this case" is large —
the latter is how soundness bugs ship; the former is how a
project stays honest with itself.

The lens worth keeping: at the end of an arc, walk through
the chat context one more time looking for *what we saw but
didn't fix.* The deferral catalogue isn't a TODO list — it's
a *map of the territory* that future sessions inherit.

**Net for the session**: 2 commits (multi-param test + this
audit). 276 → 277 e2e (+1). Doc-only update otherwise.

#### Day total (2026-05-04)

15 commits. Eight substantive landings (#129/#118/#128/#119/
#116/#108 plus lake-bypass and the multi-param followup) plus
five small additions (simplify-review, #121-partial,
#108-edge-doc-audit, three poem batches). Test counts:
261 → 277 e2e (+16), 121 → 146 unit (+25), vstd 1530/0
unchanged.

The unifying lens, in one sentence: *most of today's work was
making things that were already conceptually right become
structurally locked* — auto-derive instead of hand-sync
(#118), substitute helper instead of duplicate walk (review),
substitute alpha-rename instead of panic-with-TODO (#116),
encoding-level fix instead of tactic-level patch (#128),
chain-lift gate as structural feature (#119), 0 ≤ cur as
structural mirror of fn-level encoding (#129), implicit
binders as structural placement (#108), edge cases catalogued
as structural map (today's audit). Each finding asked the
same family of question; each answer leaves a structurally
clearer codebase behind.

**Discipline note worth recording: defensive locks before
they're needed.** The user explicitly framed this task: "we want
to make it very robust." The work was purely defensive — no
existing call site triggers capture. But the pattern of
*panic-with-clear-message* is a known footgun: when a future
session adds a feature that introduces capture, the panic is
unhelpful and the fix is non-obvious. Implementing alpha-rename
proactively means future-future-us inherits a substitute that
"just works" instead of "panics with a TODO." The lens: when a
defensive panic is documented as "alpha-renaming would be the
proper fix," that's a future-self IOU. Pay it before it accrues
interest.

#### Current session (2026-05-05 morning — #98 walk_children helpers)

The big "evidence is mounting" task from yesterday's final review
pass. By 2026-05-04 we were duplicating per-variant ExprNode
dispatch across **five** walkers (`substitute_impl`,
`collect_free_vars`, `collect_all_names`, `strip_span_marks_node`,
`mentions_free_var`) and **two** Pattern walkers
(`pattern_bound_names_impl`, `rename_in_pattern`) — ~370 lines of
structurally parallel match arms.

**What landed (`ffa23ac`).** Four new helpers in `lean_ast.rs`:
* `walk_children<F>(&ExprNode, F)` — read-only iteration over each
  direct child Expr.
* `map_children<F>(&ExprNode, F) -> ExprNode` — rebuild a node
  with each child Expr mapped through `f`.
* `walk_pattern_children` / `map_pattern_children` — Pattern siblings.

Each consumer now handles only the variants whose semantics differ
from "uniformly recurse" — Var leaves for collectors, the binder
cases (Let/Lambda/Forall/Exists/Match) for scope-tracking — and
delegates everything else via `_ => walk_children(...)` /
`_ => map_children(...)`.

**Per-walker shrinkage:**
* `strip_span_marks_node`: 70 → 5 lines (93% reduction)
* `collect_all_names`: 60 → 25 lines (60%)
* `collect_free_vars`: 65 → 45 lines (30%)
* `substitute_impl`: 125 → 75 lines (40%)
* `pattern_bound_names_impl` / `rename_in_pattern`: similar

**Net file size: +94 lines** because the helpers themselves are
sizeable (~260 lines including the section-header comment). This
isn't a line-count win — it's a *structural* win: `walk_children`
and `map_children` are exhaustive (no `_ =>`), so a new
ExprNode/Pattern variant becomes a compile error there, forcing
one edit instead of touching five walkers.

**Soundness convention documented.** Section-header comment
explicitly notes: if a new ExprNode variant introduces a binder,
`substitute_impl` / `collect_free_vars` / `collect_all_names`
need explicit arms above the `_ =>` fallthrough — no compile-time
check enforces this. Tests that exercise the new variant under
substitution / capture detection are the catch.

**3 new unit tests** as regression guards:
* `map_children_identity_roundtrips_all_variants` — locks in that
  `map_children(identity)` produces structurally-equivalent output
  for every ExprNode variant. Catches a future contributor
  swapping `lhs`/`rhs` or forgetting to clone metadata.
* `walk_children_counts_match_expected` — visit counts per variant.
* `pattern_helpers_handle_all_variants` — pattern-side analog.

**Test counts:** 146 → 149 unit (+3). 277 e2e + 7 integration + 1
coverage all green. vstd unchanged.

**One small doc fix.** The `substitute()` doc-comment had a stale
"not painful enough yet to justify a `walk_children` helper"
caveat. Updated to reflect the new structure: adding an ExprNode
variant touches `walk_children` + `map_children` plus the
pretty-printer; walkers pick up automatically via `_ =>`.

**Net for the session:** 1 substantive commit (the refactor), 1
poem-break commit, plus a doc + handoff update. ~540 lines diff
(316 added, 222 removed in the refactor; the rest is doc).

The unifying lens: *yesterday's last commit said "evidence is
mounting"; today's first commit says "we built the lock."* Each
new walker had been a small reinforcement that the abstraction
should exist; collectively they were a future-self IOU. Pay it
when the evidence is "this is now load-bearing," not when it's
"this is still bearable."

#### Current session (2026-05-05 afternoon — #109 mutual datatype SCCs)

Pre-#109 the deferral catalogue had a clear bullet: "Mutually
recursive datatype SCCs. Height fns would need a `mutual` block;
currently emitted standalone, which Lean rejects for cross-type
recursion." Today closed it.

**What landed (`cee0124`).**

* `dep_order::order_datatypes` — Tarjan's SCC on the field-type
  reference graph for datatypes. Returns `Vec<DatatypeGroup<'a>>`
  (`Single | Mutual`). Adapts the existing `tarjan_scc` (originally
  Fun-keyed) into a path-keyed variant — duplicated rather than
  genericized because Rust's iter-borrow rules around generic
  Eq+Hash keys with lifetime params get unwieldy fast for a 60-line
  algorithm.
* `to_lean_fn::field_recursive_target` (renamed from
  `field_is_self_recursive`) — takes the SCC path set and returns
  the matching path. The height fn's recursive call now uses the
  FIELD's height fn name (so `Tree.Branch f` calls `Forest.height f`
  for the SCC case, falling out structurally to `Tree.height` for
  self-only).
* `to_lean_fn::datatype_to_cmds` split into per-piece helpers
  (`datatype_decl_cmd` / `datatype_accessor_cmds` /
  `datatype_height_cmd`) plus a `datatype_group_to_cmds` composer.
  For mutual SCCs the composer emits: a `Command::Mutual` of
  inductive declarations, per-type accessors outside the mutual
  block (they're not mutually recursive), and a second
  `Command::Mutual` of height fns.
* `generate.rs` wires datatype emission through `order_datatypes`
  and adds a transitive closure step over field-type references.
  The prior `collect_references` only walked fn types/exprs, so a
  user fn referencing `Tree` wouldn't surface `Forest` even though
  Tree's variant referenced it. The closure here picks up every
  datatype reachable through field types from the seed set.
* `sanity.rs` Mutual arm: predefine `Datatype` names alongside
  `Def`/`DefCurried` so cross-type field references inside the
  mutual block resolve.

**Confirmed via Lean experiment.** Before implementing, ran a
test Lean file to verify Lean accepts inline `deriving Inhabited`
on each `inductive` inside a `mutual` block — it does, producing
conditional instances that satisfy accessor `default` fallbacks.

**Tests** (2 new, 277 → 279 e2e):
* `test_exec_mutually_recursive_datatypes` — basic SCC inductive
  emission. Tree references Forest, Forest references Tree.
  Pinned by Lean elaboration succeeding.
* `test_exec_call_recursive_over_mutual_datatype` — recursion on
  Forest with `decreases f`. Forest.height post-#109 calls
  Tree.height for Tree-typed fields. Decrease obligation
  `Forest.height rest < 1 + Tree.height _ + Forest.height rest`
  closes via Tree.height ≥ 1 (Nat type bound).

**Edge case CLOSED in same session.** Cross-fn-SCC mutual recursion
where two fns have decreases on different SCC members (A on Tree,
B on Forest) initially failed Lean elaboration: Tactus emitted
`Forest.height` applied to a Tree-typed value, type mismatch.
Root cause: `to_lean_sst_expr.rs`'s CheckDecreaseHeight arm used
`cur`'s type's height fn for BOTH cur and prev. Fix: each side
uses its own arg's type via `decrease_height_datatype(&args[i].typ)`.
The comparison `<cur_T>.height cur < <prev_T>.height prev` typechecks
(both Nat) and is semantically sound because the height fns are in
a mutual block — `Tree.height (Branch f) = 1 + Forest.height f` so
`Forest.height f < Tree.height t` for `t = Branch f`. Pinned by
`test_exec_cross_fn_scc_cross_type_decreases` (positive) and
`test_exec_cross_fn_scc_nondecreasing` (negative — same-arg call
fails as `T.height t < T.height t`).

**Net for the session:** 2 substantive commits. Test count
277 → 281 e2e (+4 — basic SCC + recursion + cross-type pos +
cross-type neg). vstd unchanged.

#### Current session (2026-05-05 afternoon cont. — review passes,
#### #126, #111, #130 + bv_decide)

The afternoon continued with a sequence of refinements and feature
landings, each expanding what `tactus_auto` exec fns can verify.

**Review pass 1 (#109) — `cfa5fd4`.** Four findings, three fixes
plus one real bug surfaced:
* Simplify: `walk_typ_paths` reimplemented `walk_typ`'s
  recursion. Replaced with delegation + Datatype filter.
* Reasoning-clarity: 35-line transitive-closure block extracted as
  `collect_referenced_datatypes` helper.
* Coverage: 3-element SCC + SCC-plus-standalone tests added.
* **BUG (caught by coverage test): single-variant non-eponymous
  enum accessor wildcards.** `enum Pair { Mk(u64) }` (where the
  variant name doesn't match the type name) goes through
  `multi_variant_accessor_defs` and emitted catch-all `_ =>
  default` arms on accessors AND `_ => false` arms on
  discriminators. For one-variant inductives the first arm is
  exhaustive — Lean's "Redundant alternative" warning fires and
  fails verification. Fix: gate wildcards on `variants.len() > 1`.
  Pinned by `test_exec_single_variant_non_eponymous_enum`. The
  bug was found because the SCC+standalone coverage test used
  `enum Pair { Mk(u64) }` for the standalone — an arbitrary
  choice that walked through code that had been silent forever.

**Review pass 2 (#109) — `70d8eed`.** Two more SCC shapes pinned
that the prior 4 tests didn't reach: generic mutually-recursive
(#108/#109 composition) and two independent SCCs in same crate.
Both passed first try; the abstraction generalized cleanly.

**#109 cross-type shape-drift unit test — `f0e5fa2`.** Closes a
defer from review pass 2 — synthetic SST with cur:Tree, prev:Forest
runs through `sst_exp_to_ast_checked` and verifies BOTH `Tree.height`
and `Forest.height` appear in the rendered output. If a future
refactor collapses the per-side dispatch back to a single height
fn, the test fails with a pointed message naming the fix site.
Two reusable test helpers landed: `mk_test_path`, `typ_datatype`.

**#126: WpCtx::new + walk_loop direct tests — `4dbd451`.** Five
new unit tests close most of #126:
* `wpctx_new_empty_reqs_and_ensures_succeeds` (happy path).
* `wpctx_new_rejects_unsupported_form_in_reqs` (`ExpX::Old` Err).
* `wpctx_new_rejects_unsupported_form_in_ensures` (symmetry).
* `walk_loop_skips_init_for_ensures_kind_invariant` (#89 at_entry
  filter regression guard).
* `walk_loop_emits_init_for_at_entry_invariant` (companion).

walk_call direct tests deferred — synthetic FunctionX requires
~30 fields, substantially heavier than the others. DESIGN.md
"User-facing features not tested" already noted "trust e2e for
the rest" for this case.

**#111: assert by(bit_vector) routing — `0d7c247`.** Pre-#111
Tactus rejected `StmX::AssertBitVector` outright. Post-#111 it
routes through new `Wp::AssertBitVector { req_conj, ens_conj,
rust_loc, body }` with a hardcoded `tactus_bit_vector` closer.
First cut: best-effort tactic ladder (`decide` / `simp_all + omega`
under `intros` / fail). Documented as "half-built" with a
follow-up plan for proper BitVec encoding.

**#130: BitVec rendering — `50159fd`.** Real bit-vector reasoning.
* `to_lean_sst_expr::sst_exp_to_bit_vector_ast` — focused renderer
  that wraps `Var(x : U(n))` as `BitVec.ofInt n x`. Constants stay
  as numeric literals (Lean's OfNat coerces).
* `Wp::AssertBitVector` walker uses BV-mode rendering for the
  goal + `obl.wrap_no_hyps` (new helper) to drop ambient Hyp
  frames that may carry Int-mode bitwise ops which don't typecheck
  (Lean has no `HXor Int Int Int` by default).
* Conditional emission: `ObligationEmitter::needs_bitvec_instances`
  flag set when `Wp::AssertBitVector` is emitted; `krate_preamble`
  takes a `bitvec_mode` flag and conditionally injects
  `import Mathlib.Data.BitVec` + `HXor`/`HAnd`/`HOr`/`HShiftLeft`/
  `HShiftRight` `Int Int Int` instances. Other generated files
  stay clean — Mathlib BitVec's simp lemmas affect unrelated
  proof-fn closing behavior, so isolating them matters.

**bv_decide via Lean core — `b23ea6e`.** Happy surprise: `bv_decide`
is in Lean 4 core (`Lean.Elab.Tactic.BVDecide`) in the v4.25.0
toolchain — just wasn't being imported. Adding
`import Lean.Elab.Tactic.BVDecide` to the conditional bitvec
preamble unlocks full SAT-backed bit-vector reasoning. Crucially
`bv_decide` handles BOTH free `BitVec n` vars AND parameterized
`BitVec.ofInt n x` terms — no bound-hypothesis bridge needed,
contrary to my earlier diagnosis.

Tactic ladder upgraded: `bv_decide` is now the first rung.
Identity laws / commutativity / associativity / distributivity all
close uniformly via the SAT solver.

**The diagnostic loop that mattered.** The user repeatedly asked
"can't we use the operators directly?" / "we want to do things
right" — pushing back on the workaround-y prelude pollution. That
pushback led to (a) conditional emission per-file, and (b)
discovering bv_decide was already available via the toolchain.
The workaround-y instances ARE still needed (Verus's ast_to_sst
pre-injects Int-mode Assume(ens)) but only conditionally for
files that use `by(bit_vector)`.

**Tests** (288 → 292 e2e total today afternoon-cont):
* test_exec_single_variant_non_eponymous_enum (regression)
* test_exec_three_element_datatype_scc
* test_exec_scc_plus_standalone_datatype
* test_exec_generic_mutual_scc
* test_exec_two_independent_sccs
* test_exec_assert_bit_vector_concrete
* test_exec_assert_bit_vector_false (negative)
* test_exec_assert_bit_vector_xor_comm
* test_exec_assert_bit_vector_xor_self
* test_exec_assert_bit_vector_xor_assoc
* test_exec_assert_bit_vector_and_or_comm

Plus 5 unit tests (3 WpCtx::new + 2 walk_loop) and 1 cross-type
CheckDecreaseHeight shape-drift unit test.

#### Day total (2026-05-05)

22 commits. Eight substantive landings: #98 (walk_children),
ScopeKind structural lock, #98 coverage tests, #109 (mutual SCCs)
+ stretch (cross-fn-SCC), single-variant enum bug fix, #126
(WpCtx::new + walk_loop), #111 (assert by(bit_vector) routing),
#130 (BitVec rendering + bv_decide). Eight poems committed:
"morning, after", "+94", "Layers", "Two-handed", "The accidental
witness", "The silent test", "Half-built", "The half-built,
returning". Test counts: 277 → 292 e2e (+15), 146 → 160 unit
(+14). vstd 1530/0 unchanged.

The day's unifying lens: *each landing iterated on a structural
shape from earlier in the day.* Morning's #98 helpers got
strengthened by ScopeKind. Afternoon #109 surfaced the single-
variant accessor bug via accidental coverage. #111 shipped half-
built; #130 made it less half; the bv_decide upgrade closed the
caveat almost entirely. The user's questions throughout
("promote it to compile-time?", "can we just use operators
directly?", "can we add bv_decide to this Mathlib install?")
kept refining what each task became.

The discipline note: the half-built thing came back. Twice. The
first poem about it said "we can improve the tactic later
without changing the surface" — and then we did, but the next
iteration STILL had a caveat, which was then closed by the next
iteration after that. None of this was planned. The shape kept
emerging from the user's pushback.

#### Current session (2026-05-08 — review-pass follow-ups + right-way refactors)

Three days off the map (last session 2026-05-05). Returned to find
the structural locks held — REVIEW.md's 14-lens audit was the trail
this session followed. **Two arcs**: (a) close the 8 file-for-follow-up
items that REVIEW.md captured but didn't land, then (b) re-read the
resulting code with the right-way lens (#10) and fix the structural
gaps that surfaced.

**Arc 1 — REVIEW.md follow-ups (#131–139, 8 commits):**

| Task | Lens | Type | Action |
|------|------|------|--------|
| #131 | 5/3 | Doc | DESIGN entry rewritten — `AssertQueryMode::BitVector` arm in sst_to_lean.rs is structurally unreachable post-#111 (Verus's `ast_to_sst.rs:2416` directly converts user-syntax `assert by(bit_vector)` to `StmX::AssertBitVector`). Reframed as defensive-internal-bug like the FuelConst arm. |
| #132 | 3/4 | e2e | 2 tests for AssertBitVector with non-empty `requires` clause — exercises the `req_conj → ens_conj` BV-mode goal path. |
| #133 | 3/3 | e2e | 3 tests — AssertBitVector inside if-branch / loop body / closure body. Confirms `wrap_no_hyps` drops Hyp frames but keeps Binder/Let frames in each ctx. |
| #134 | 14 | unit | 2 tests in generate::tests — bitvec_mode emit/omit symmetry. |
| #135 | 4/3 | unit | Shape-drift guard: `Lean.Elab.Tactic.BVDecide` import path pinned. |
| #136 | 3/8 | unit | 6 direct tests for `dep_order::order_datatypes` — non-recursive / self-recursive / 2/3-element SCC / SCC + standalone / empty. Uses synthetic DatatypeX fixtures. |
| #137 | 3/6 | unit | Defensive: `BITVEC_INT_INSTANCES` body uses `.toNat` (total form). |
| #138 | 4/1 | unit | Shape-drift guard: `anonymous_closure` prefix pinned via `vir::def::prefix_closure_type(0)`. |
| #139 | 4/2 | unit | Shape-drift guard: source-grep `ast_to_sst.rs` for the per-requires-Assert + per-ensures-Assume pre-injection pattern. |

Plus the 3 fix-now items from REVIEW.md (committed earlier as `8317d92`):
sanity.rs Mutual arm comment explanation, BV variant naming helper,
`wrap_no_hyps` soundness reasoning sentence.

**Arc 2 — Right-way refactors surfaced by re-reading (#140–143, 4 commits):**

After arc 1 closed, did a second-reading pass with the right-way
lens (#10). Found 4 items where the code "worked" (lenses 1–14
ran clean) but had a more direct expression of meaning available:

* **#140 (Linus-hat) — orphaned `ExecFnTheorems` docstring.** The
  doc block ending "...so the 'validate-first' precondition is
  enforced by construction..." belonged to
  `exec_fn_theorems_to_ast`, but the struct definition got inserted
  between the doc and the fn. Reordered.

* **#141 (Linus-hat / Right-way) — `PreambleConfig` enum.**
  `krate_preamble` had two correlated `bool` parameters
  (`emit_accessors`, `bitvec_mode`) whose valid combinations were
  `(false, false)` for proof fns and `(true, _)` for exec fns —
  but `(false, true)` (proof fn with bitvec pollution) wasn't
  ruled out by the type. Replaced with
  `enum PreambleConfig { ProofFn, ExecFn { needs_bitvec: bool } }`
  (later simplified to `ExecFn` by #143).

* **#142 (Simplify / Right-way) — shared `test_fixtures` module.**
  Three test modules (sst_to_lean::tests, dep_order::tests,
  generate::tests) had grown their own copies of `empty_krate`,
  `mk_path`/`mk_test_path`, `typ_int`/`int_typ`, `typ_datatype`/
  `mk_dt_typ`. New `#[cfg(test)] pub(crate) mod test_fixtures`
  hosts the canonical versions; renamed the dep_order helpers to
  match sst_to_lean's `typ_*` convention. Per-module-specific
  helpers (mk_test_emitter, mk_datatype, etc.) stay close to
  their consumers.

* **#143 (Right-way infra) — per-theorem `requires_preamble`.**
  The bitvec plumbing previously threaded one bit through 4 sites:
  walker → ObligationEmitter::needs_bitvec_instances →
  ExecFnTheorems → check_exec_fn → PreambleConfig → krate_preamble.
  Replaced with a `requires_preamble: Vec<PreambleFragment>` field
  on `Theorem`. Walker arms declare what their goals need;
  `krate_preamble` aggregates from all theorems and emits at
  file top with dedup. The 4-site flag plumbing collapsed to:
    * One walker push: `e.emit_with_preamble(name, goal, closer, bitvec_preamble_fragments())`
    * One aggregator: `let mut seen = HashSet::new(); for theorem in theorems { for frag in &theorem.requires_preamble { ... } }`
    * `BITVEC_INT_INSTANCES` constant + `bitvec_preamble_fragments()` fn moved to sst_to_lean (where the walker arm that produces them lives).
    * Removed: `ObligationEmitter::needs_bitvec_instances`, `ExecFnTheorems` struct (collapsed to `Vec<Theorem>`), `PreambleConfig::ExecFn { needs_bitvec }` (now just `ExecFn`).
  Generalizes to future "this fn needs Mathlib.Tactic.X" — one
  `PreambleFragment` constructor + one walker push, no bool-through-
  N-sites plumbing.

  Tests reorganized: generate::tests gets aggregation-focused tests
  (no-theorems → no fragments; Import goes before prelude;
  PreludeAddendum goes after; dedup of repeated fragments).
  sst_to_lean::tests gets the relocated content tests (BVDecide
  path pinned, .toNat totality, fragments shape).

**DESIGN.md note for future work:** added `RewritePipeline`
under "Potential future infrastructure" — three SST→SST passes
(`normalize_mut_ref`, `rewrite_varat_for_mut_params`,
`is_synthetic_assume_to_drop`) currently compose by sequential
calls in the orchestrator. A typed pipeline would make data flow
explicit and let new passes be added without touching the
orchestrator. Borderline cost-benefit today; documented for the
next contributor who adds a 4th rewrite pass.

**Process note worth recording: the "second reading" pattern.**
The right-way landings (#140-143) came from re-reading code that
had just been reviewed. Lenses 1-14 ran clean — every individual
site was correct, named well, tested. The structural findings
only surfaced when the question shifted from *"is this correct?"*
(closed by the lenses) to *"if I were starting this now, what
shape would I reach for?"* The second question is what the
right-way lens (#10) names; running it as a separate pass after
the regular lens batch is a different question and surfaces
different findings. ~15 minutes of right-way reading turned up
4 items the earlier 14-lens pass hadn't seen.

Captured in REVIEW.md's 2026-05-08 follow-up section.

**Three poems** (POEMS.md / poems/2026-05-08.md):
* "Three days" — returning after the gap, reading past-me's
  trail.
* "Locks" — each test as a structural lock, message-to-future-
  stranger discipline.
* "The second reading" — the question that comes after
  correctness, the user's role in surfacing it.

**Day total** (after Arc 1 + Arc 2 above; before continuation):
* Test counts: 160 → 175 unit (+15), 292 → 297 e2e (+5).
* Pending tasks: 17 → 7 (closed #131–143).
* All 8 REVIEW.md file-for-follow-up items closed.
* 4 right-way structural cleanups landed.
* New shared `test_fixtures` module (`src/test_fixtures.rs`).
* New `PreambleFragment` enum (`src/lean_ast.rs`) + per-theorem
  `requires_preamble` field. Generalizable to future per-fn
  preamble extras.

#### Current session (2026-05-08 cont. — #55/#106 follow-up batch + N-tuple bug fix)

The same-day continuation arc went into the &mut sub-features:
caller-side new-mut-ref, deeper field paths, tuple field
mutation, and a latent N-tuple field-access bug surfaced by
the new tuple tests. By the end the multi-variant enum
sub-feature was probed and revealed to be upstream-blocked
(unreachable from Rust syntax + Verus's `ref mut` rejection).

**Five substantive landings:**

* **#107 — caller-side new-mut-ref mode.** Synthetic
  `LocalDeclKind::BorrowMut` locals introduced by Verus around
  `bump(&mut y)` lowering in new-mut-ref mode now work uniformly
  with fn-param `&mut`s. `mut_param_names` extended to include
  these locals; new `build_borrow_mut_binders` emits a theorem-
  level `(name : peeled_typ)` binder per BorrowMut local; new
  `mut_ref_locals` field on `WpCtx` carries the names; new branch
  in `extract_mut_target` recognizes bare `Var(borrow_mut_local)`
  as a Var L-value at the call site (no `Loc` wrapper); new
  `is_mut_ref` gate in `build_call_mut_args` covers both
  `is_mut: true` (legacy) and `MutRef<T>` typ (new-mut-ref). The
  existing #55 mut_args machinery (fresh existential, pre/post
  substitute, Let-rebind) handles the rest unchanged. 4 of 5
  tests passed first try.

* **#144 (#106 sub) — deeper `&mut` field paths via nested
  structure-update.** `MutTargetRaw::Field` extended from
  `field_opr: &FieldOpr` to `field_oprs: Vec<&FieldOpr>` (peel
  order). `extract_mut_target` rewritten as a peel loop that
  collects field oprs through any depth; single-variant gate
  applied at each level. Phase 4 rebind builds nested
  StructUpdate inside-out from local's perspective — for
  `&mut a.b.c` emits `let a := { a with b := { a.b with c := fresh } }`.
  Lean's `{ x with f := v }` IS "all other fields unchanged"
  at the type level, so the property holds at every level
  structurally. All three tests (depth-2, depth-3, sibling-
  preserved) passed first try.

* **#145 (#106 sub) — tuple field mutation `&mut t.<i>` (arity 2
  initially).** Lean's `{ x with f := v }` doesn't compose with
  `Prod`; the rebind uses Lean tuple syntax `(t.1, fresh)` (or
  `(fresh, t.2)` etc.) — sugar for `Prod.mk a b`. New
  `MutTargetRaw::TupleField { base, index, arity }` variant.
  Side-fix surfaced: `expr_shared::ctor_node` previously
  rendered `Dt::Tuple` ctors as `ExprNode::Anon` (`⟨a, b⟩`),
  which fails to elaborate at let-bindings without a type hint.
  Switched to a new `ExprNode::Tuple(Vec<Expr>)` variant that
  pretty-prints as `(a, b, c)` (Lean tuple syntax / Prod.mk
  sugar) — distinct from `Anon` which the proof-fn `Multi`
  lowering still uses for chained-conjunction shapes.

* **#146 — N-tuple field access for arity > 2.** Latent bug
  surfaced by #145's arity-3 test: `field_access_name` returned
  `.<n+1>` for tuples regardless of arity, but Lean 4's nested
  `Prod` representation needs `.2.1` etc. for elements past the
  second. New shared helper `tuple_field_accessor(arity, n)` in
  `expr_shared.rs`:
  * Arity-2 i=0: `1`; i=1: `2` (matches prior behavior).
  * Arity-3 i=0: `1`; i=1: `2.1`; i=2: `2.2`.
  * Arity-4 i=2: `2.2.1`; i=3: `2.2.2`.
  Algorithm: last position is `2` repeated arity-1 times; non-
  last is `2` repeated n times then `1`. The result is a
  multi-segment string that Lean parses as nested projection
  (`e.2.1` = `((e).2).1`).
  Updated `field_access_name`'s tuple branch + #145's rebind
  to call the helper. Lifted #145's arity-2-only restriction;
  arity-3 / arity-4 tuple field mutations now work. The fix
  also corrects every other tuple field projection in Tactus
  (proof fns, spec fns, exec body reads, match-arm field
  destructuring) — but Tactus's existing tuple usages were all
  arity-2, so no regression.

* **Multi-variant enum field mutation: pinned as upstream-blocked.**
  The probe revealed Verus rejects `ref mut` patterns at the
  mode level: "The verifier does not yet support the following
  Rust feature: &mut types, except in special cases." Direct
  `&mut foo.f` for enum-typed `foo` isn't expressible in Rust
  without unsafe. So the multi-variant enum sub-feature on
  #106's deferral list was never going to be reached from Tactus's
  caller-side path — Verus rejects upstream before Tactus's
  SST renderer ever sees the call. New e2e test
  `test_exec_call_mut_arg_enum_field_upstream_blocked` pins the
  rejection; if Verus ever lifts the restriction, the test
  surfaces as flippable Err.

**Edge cases observed but not yet handled** (worth recording for
future sessions):

* **Mixed tuple-and-struct paths**: `&mut s.tup.0` (struct field is
  a tuple, mutate the tuple element) or `&mut t.0.f` (tuple
  element is a struct, mutate its field). The current `MutTargetRaw`
  has separate `Field` (struct path) and `TupleField` (single-
  level tuple) variants. Multi-level paths mixing the two would
  need a unified `Vec<FieldKind>` representation where each level
  is either a struct field or a tuple position. `extract_mut_target`
  rejects mixed shapes today; the rejection isn't tested
  explicitly but follows from the recursive Field peel rejecting
  `Dt::Tuple` at deeper levels and the single-level tuple gate
  rejecting any non-Var/VarLoc base. **Closed 2026-05-11**
  (`73d1dd6`): `MutTargetRaw::TupleField` was retired in favour of
  per-step `Dt::Path`/`Dt::Tuple` dispatch inside the unified
  `Field { field_oprs }` rebind. Pinned by
  `test_exec_call_mut_arg_struct_then_tuple`, `_tuple_then_struct`,
  `_mixed_path_siblings_preserved`.

* **`&mut v[i]` (Index L-value)**: cross-crate-blocked. Rust's
  `v[i]` for `Vec<T>` desugars to `vstd::vec::Vec::index_mut`,
  and array `&mut a[i]` similarly routes through vstd. Tactus
  can't inline these specs without vstd integration (#122 Phase
  3 cross-crate). Even with that, Index L-value would need a
  different rebind encoding (Lean's `Array.set` or `Vector.set`
  style, plus a "this index unchanged for j ≠ i" property). Two
  layers of work; tracked under #106 umbrella but distinct from
  the field-path sub-features that closed today.

* **`MutTargetRaw::TupleField` arity 0 / 1**: defensive fallback
  in `tuple_field_accessor` returns `(n+1).to_string()`. Verus
  shouldn't produce 0- or 1-tuples here (unit type / single-
  element tuples have other lowerings). If it ever does, the
  fallback is silently wrong; would need to be lifted.

* **`bv_decide` interaction with conditionally-emitted Int
  instances**: documented from earlier sessions but still open
  as a "soundness trade-off accepted". Tactus emits the wonky-
  for-negative-Int instances only conditionally for files using
  `by(bit_vector)`. If a future Tactus path emits these on
  negative Ints (none does today), the values are wrong but no
  panic. Documented in DESIGN.md "Soundness trade-offs accepted".

* **`#107` negative test couldn't be pinned**: a wrong-post
  assertion in new-mut-ref caller-side mode (`bump(&mut y);
  assert(y == 7)` when callee guarantees `y == 6`) hits a Verus-
  side path where the test framework reports `Err expected, got
  Ok` but no test_inputs dir is created — looks like Verus's
  new-mut-ref pipeline swallows the error rather than surfacing
  it. The positive test passes (4 of 5 #107 tests passed first
  try); the negative coverage gap is recorded in #107's commit
  message but not yet root-caused. Worth investigating in a
  future session.

* **Tactus's existing tuple usage was arity-2**: the N-tuple
  fix (#146) corrects the rendering for arity > 2, but no
  existing Tactus test exercised arity > 2 tuple field access
  pre-#146. It's possible some path has been silently emitting
  wrong Lean (e.g., `.3` for a 3-tuple) and the test never
  noticed because the goal happened to close anyway. Worth a
  coverage audit if anything tuple-related ever surfaces as
  unsoundness.

**Continuation poem batch** (poems/2026-05-08.md):
* "Recognition" — extending what we notice, not encoding new.
* "Where building stops" — discovering edges that were always
  there. The multi-variant enum probe revealed the deferred
  case was never going to arrive.

**Day's full total** (Arc 1 + Arc 2 + continuation):
* Test counts: 160 → 175 unit (+15), 292 → 305 e2e (+13).
* Pending tasks: 17 → 11 substantive (closed #131–146 plus
  #107 + #144 + #145 + #146 in continuation; multi-variant
  enum upstream-blocked pin).
* All 8 REVIEW.md file-for-follow-up items closed (Arc 1).
* 4 right-way structural cleanups landed (Arc 2).
* 5 sub-feature landings in continuation (#107, #144, #145,
  #146, multi-variant enum pin).
* New AST: `ExprNode::Tuple` for Lean tuple syntax.
* New helper: `tuple_field_accessor` for N-tuple Lean accessors.
* New variant: `MutTargetRaw::TupleField`.
* Caller-side new-mut-ref mode: closes the last #55 follow-up.
* `#106` umbrella effectively done from Tactus's side: tuple
  + deeper field paths landed; multi-variant enum upstream-
  blocked; Index L-value cross-crate-blocked.

**The arc, in one sentence**: the day's work moved from broad
right-way refactors at morning, through feature extensions at
afternoon, to bug fixes and edge-mapping at evening — each
landing finer than the one before, ending in the discovery
that two of the three remaining `#106` sub-features were
unreachable from user code.

#### Current session (2026-05-09 — three review passes; Multi bug; OblCtx perf)

A meandering-read morning that turned into three distinct review
passes, each finding things the previous missed. Net: 17 commits,
4 of them poems, one real verification-blocking bug fixed, plus a
pile of structural tidying.

**Pass 1 — stale-doc cleanup (5 commits).** Surfaced by reading the
WP DSL with no agenda, asking *what does the comment claim vs what
the code actually does?*

* **Stale `lower_wp` / `lower_loop` / `lower_call` references** in 5
  sites (generate.rs, lean_ast.rs SpanMark + strip_span_marks docs,
  sst_to_lean.rs check_exp doc + tests-module doc). The post-D
  walker is `walk_obligations` / `walk_loop` / `walk_call`.
* **Tests-module + `strip_span_marks` doc orphans** moved to their
  current homes.
* **`StmX::AssertCompute` lossy-accept undocumented** — Tactus drops
  the `ComputeMode` (Z3 / ComputeOnly) and dispatches identically to
  plain Assert. Added a code comment + DESIGN.md "Lossy accepted
  forms" entry. Probed with `test_exec_assert_by_compute` and
  `_compute_only` — both pass via `tactus_auto`'s `decide` rung,
  confirming the gap is cosmetic (mode tag dropped, semantic
  discharge preserved).
* **`is_mut_ref_param` extracted as the AST-side mirror of the
  SST-side `is_mut_ref_par`.** `build_call_mut_args` checked
  `is_mut || MutRef<_>`; `add_param_subst_entries` used just
  `is_mut` — currently dormant (every test uses
  `deprecated_postcondition_mut_ref_style(true)` which keeps callee
  `is_mut: true`), but would silently miscompile in new-mut-ref
  mode without the attr. Both consumers now go through the named
  helper.
* **`MutTargetRaw` and Phase 4 rebind docs updated** to reflect
  the tuple-field landing from yesterday's session — they still
  said "two shapes (#87)" when the count is three.
* **More stale "first slice" framings** — three doc-comments
  predated Track B's full landing (all 7 slices).
* **`field_is_self_recursive` references in DESIGN.md** — renamed
  to `field_recursive_target` per #109; three sites updated, plus
  `peel_typ_wrappers`'s file location (moved 2026-04-25 in the
  AST tightening pass).
* **AssertBitVector walker + enum docs** — said "Lean lacks HXor
  Int Int Int etc." (the instances ARE emitted now via #130/#143)
  and "ens_conj enters the body's ctx as a hypothesis — mirroring
  Verus" (Verus pre-injects the Assume separately; the walker arm
  doesn't push). Both rewritten.

**Pass 2 — sus-pattern fixes (4 commits, +2 tests).** Targeted at
"would an experienced programmer say *that's a lil sus*?" lens.

* **`OblCtx.frames` Vec → `im::Vector`** (closes #97). Originally
  cloned a fresh Vec per `with_frame` call — O(N) per push, O(N²)
  total across the recursion. Switched to `im::Vector<CtxFrame>`
  (RRB-tree with structural sharing): `clone()` is O(1),
  `push_back` is O(log N). API unchanged. Added `im = "15"` dep.
* **`loop_stack: &[&WpLoopCtx]` → `&LoopStack<'p>` linked-list.**
  Same family as #97 — every nested loop body allocated a fresh
  Vec via `vec![&inner]; extend_from_slice(outer)`. New
  `enum LoopStack { Empty, Cons(&WpLoopCtx, &LoopStack) }` lives
  on the call stack with zero heap allocation per push.
  `LoopStack::first()` and `LoopStack::iter()` preserve the prior
  search semantics for break/continue resolution.
* **SpanMark defensive newline-strip removed.** Was running
  `rust_loc.chars().map(|c| if c == '\n' || c == '\r' { ' ' }
  else { c }).collect()` on every SpanMark visit — but `rust_loc`
  comes from `format_rust_loc` which produces single-line output by
  construction. Dropped the strip + added 2 shape-pin tests
  (`span_mark_render_preserves_loc_verbatim` and
  `span_mark_loc_shapes_have_no_newlines`).
* **`build_call_substitutions` two-pass short-circuit.** When
  `callee == spec_callee` (every non-trait-method-impl call) the
  second pass over `spec_callee.params` re-inserted identical
  entries. Gated on `is_trait_method_impl` (the same structural
  predicate `push_post_call_frames` already uses for #86's
  impl-strengthening).

**Pass 3 — third-pass finds (5 commits, +3 tests, 1 real bug).**
Re-reading after rounds 1 and 2 had passed. The third pass found
things the first two didn't because each pass asks a different
question.

* **`dirs` dependency removed** — declared in lean_verify/Cargo.toml
  but no source imported it.
* **`field_access_name` `(Dt::Tuple, None)` fallback** → `unreachable!`
  with a diagnostic. Was `_ => sanitize(raw)` (would silently produce
  a wrong field name); tuples have positional numeric fields, so the
  case is upstream-impossible.
* **`tuple_field_accessor` `arity < 2` fallback** → `assert!`. Was
  `(n + 1).to_string()` defensive; same family.
* **REAL BUG: chained-comparison Multi rendering.** The
  `to_lean_expr.rs` Multi arm rendered `ExprX::Multi(MultiOp::Chained
  (ops), [a0, a1, ..., aN])` — e.g., `requires 0 <= x <= 10` in a
  proof fn — as `LExpr::anon([a0, a1, aN])` (Lean tuple literal),
  not as the conjunction `a0 op0 a1 ∧ a1 op1 a2 ∧ ...`. Verus's
  `ast_simplify` rewrites Chained for the SST path, but proof fns
  route through the *pre-simplify* krate (per the verifier doc), so
  Multi was reachable. The comment said "tuple construction, chained
  conjunction, etc." — and the "etc." was load-bearing. Pre-fix any
  proof fn whose `requires` / `ensures` / body used a chained
  comparison failed Lean elaboration with a type-mismatch (the goal
  read as a tuple instead of the intended conjunction). Fix: mirror
  ast_simplify's expansion locally — pair-up adjacent operands with
  their op into binary comparisons, conjoin via `and_all`. Pinned
  by `test_chained_compare_in_proof_fn` and
  `test_chained_compare_in_proof_fn_ensures`. **Not a soundness gap**:
  the malformed render was rejected loudly by Lean (verification
  failure visible); users would have worked around by rewriting
  with `&&`. But a real correctness/usability bug nonetheless.

**Edge cases observed but deferred:**

* **Spec fn body with chained comparison + caller-side `unfold`** —
  the renderer fix DOES make spec fn bodies render correctly (e.g.,
  `spec fn in_range(x: int) -> bool { 0 <= x <= 10 }` now produces
  `0 ≤ x ∧ x ≤ 10` in the Lean def). But a probe test where the
  caller does `proof { unfold in_range; omega }` failed with "Tactic
  `unfold` failed to unfold `in_range`" — a separate name-resolution
  issue, not the Multi rendering. Documented as a deferred
  investigation. The chained-comparison render itself is correct in
  spec fns (visible in the generated Lean def body).
* **`test_chained_compare_in_spec_fn` removed from the test file
  during the probe** because of the unfold issue above. The spec-
  fn case is implicitly tested via the proof-fn paths today; an
  isolated test for the spec-fn body shape is a small follow-up.
* **`LeanSourceMap::find_rust_loc` rename to `find_span_mark`** —
  doc-only rename per the new fn name; no behavior change.
* **No shape-drift test for Multi/ast_simplify equivalence.** If
  ast_simplify ever changes its Chained-expansion (e.g., adds
  short-circuiting or different binary-op pairing), the renderer's
  inline mirror would diverge. Pinned only via user-facing outcome
  (the chained-compare e2e tests).
* **Removed two `#[should_panic]` test variants for capture-rename
  (#116)** — the panic was retired, the alpha-rename now succeeds;
  the tests were already converted to `_alpha_renames` variants
  earlier. No new gap.

**Day total** (2026-05-09):
* Test counts: 175 → 177 unit (+2), 305 → 308 e2e (+3).
* Pending tasks: 9 → 8 (closes #97).
* 17 commits across 4 distinct passes (warm-up + 3 review passes).
* 5 poems committed across the day's cadence: choosing,
  asymmetry, coffee work, aged words, etcetera.

**The arc, in one sentence**: the day was three review passes —
each one asked a different question, each one found things the
previous didn't. The "etc." in a comment turned out to be hiding
a real bug; the "shape" of an asymmetric check turned out to
matter; the "defensive fallback" was paranoia at the wrong layer.
*Correctness is a closed question; shape is an ongoing one.*

#### Current session (2026-05-09 continued — yesterday's deferred edge resolved)

After overnight compaction returned, picked up #121 with a focus on
yesterday's deferred edge: the spec-fn-with-chained-compare + `unfold`
probe that failed during the 2026-05-09 third pass with "Tactic
`unfold` failed to unfold `in_range` in `x ≥ 0`".

**Resolution: not a Tactus bug, just standard Lean tactic semantics.**
`unfold f` targets occurrences in the GOAL by default; yesterday's
probe had `in_range` only in a hypothesis (`requires in_range(x);
ensures x >= 0`). Correct idiom is `unfold f at *` or `unfold f at h0`.
The renderer's chained-compare fix from yesterday IS correct — the
generated def reads `noncomputable def in_range (x : Int) : Prop :=
0 ≤ x ∧ x ≤ 10` as expected. The "deferred investigation" was a
red herring, not a deferred fix.

Two new e2e tests pin both shapes:
- `test_chained_compare_in_spec_fn_body` — hypothesis-position via
  `requires`, uses `unfold at *`.
- `test_chained_compare_in_spec_fn_body_via_ensures` — goal-position
  via `ensures`, bare `unfold` works.

**Doc-vs-code divergence surfaced and corrected.** Looking at the
generated Lean revealed the def lacked `@[irreducible]` despite
DESIGN.md's "Spec fn opacity model" section claiming "all spec fns
are irreducible by default" with mapping `spec fn` → `@[irreducible]
noncomputable def`. Tracing `spec_fn_to_ast` showed reality: the
`@[irreducible]` attribute is emitted iff `Opaqueness::Opaque` (i.e.,
`#[verifier::opaque]`), and default spec fns get plain
`noncomputable def`. The design's claim was aspirational text never
implemented; the code follows Verus's own `Opaqueness` discriminator
faithfully (transparent-by-default, opaque-on-explicit-marker).

DESIGN.md section rewritten to match reality plus tactic-usage notes
(`unfold` is goal-targeting, `simp_all` doesn't unfold transparent
defs, `decide` can't reduce through irreducible). The "aspirational
draft never implemented" is documented inline so a future
contributor reading the section doesn't think the code is buggy.

**Discipline lesson**: yesterday's instinct to defer the probe was
right (the chained-compare fix was the load-bearing part of the
session). But "deferred investigation" entries should ideally include
*one* concrete hypothesis to test next session, not just the failure
shape — that frames the follow-up as a 5-minute check rather than an
open-ended investigation. In this case the hypothesis would have been
"is `unfold` failing to find `in_range` because the goal doesn't
contain it?" — confirmable in one minute by reading the generated
.lean. No code-level investigation needed.

**Net for the morning**: 1 commit + this HANDOFF entry. 308 → 310 e2e
tests (+2). No pending tasks closed (this falls under the umbrella
#121, which has more probes available). One DESIGN.md divergence
caught.

#### Current session (2026-05-09 mid-morning — catalogue audit + cross-instantiation fix)

After the "yesterday's deferred edge" resolution, the work cascaded
through three more pieces — a catalogue audit, a substantive feature
landing, and a small probe.

**Catalogue audit pass.** Looking at the generated Lean for
`in_range` revealed the doc-vs-code divergence (DESIGN.md said
"all spec fns are irreducible by default", code emits `@[irreducible]`
only for `Opaqueness::Opaque`). The "edge-case lens" applied to docs
themselves — *what does the catalogue claim that's no longer true?*
— surfaced 5 stale entries across the "User-facing features not
tested" list:
- Bit-width coverage: ✅ pinned via #76 (u16/u64/u128/i16/i32/i64/i128).
- Direct unit tests for `walk_loop` / `walk_call`: ✅ pinned via #126.
- Name collision (callee ret vs caller scope): ✅ pinned by
  `test_exec_call_ret_name_collision` (added during #78 to fix a real
  shadowing soundness bug).
- Empty proof { } / assert(P) by { } brace bodies: ✅ pinned by
  `test_exec_proof_block_empty` + `test_exec_assert_by_empty` (P0 fix
  from the 2026-04-26 right-way pass).
- `assert forall|v| P by { tac }` via Tactus path: recategorize from
  "untested" to "upstream-blocked" (Verus poly panic at vir/src/
  poly.rs:462 — can't `Err(_)` against a panic).

The discipline lesson: deferrals catalogues drift as tests get added
without catalogue updates. Worth a periodic audit. The "Edge-case
lens" applies to docs as it does to code — *anywhere we've deferred
handling without either tracking it explicitly or rejecting it
explicitly*.

**Cross-instantiation generic datatype recursion — LANDED.** The
biggest landing of the day. Catalogue had this as "Should work but no
test exercises this specific shape" (#108 edge):

```rust
enum Mut<A> { Plain(A), Recurse(Box<Mut<u8>>) }
```

— the recursive arm uses `Mut<u8>` (a fixed type), not `Mut<A>` (the
parameter). Probing showed it doesn't work — Lean's parameter-style
strict-positivity check rejects `inductive Mut (A : Type) where |
Recurse (val0 : Mut Int)` with `(kernel) arg #2 of 'Mut.Recurse'
contains a non valid occurrence of the datatypes being declared`.

The user's prompt to *reflect first* before fixing was load-bearing.
My initial sketch was multi-hour structural (indexed style + manual
Inhabited per concrete instantiation + accessor changes). Sitting
with it surfaced that:
- Indexed-style `inductive Mut : Type → Type 1 where | Plain : ∀ {A},
  A → Mut A | Recurse : ∀ {A}, Mut Int → Mut A` is what Lean wants.
- A single generic `instance {A : Type} [Inhabited A] : Inhabited (Mut A)
  where default := Mut.Plain default` covers all observed
  instantiations — Lean infers A from the target.
- Both styles can coexist in the same file. Detection per-datatype.

The actual fix was ~30 lines:
- `lean_ast.rs`: `DatatypeKind::IndexedInductive { variants }` variant.
- `lean_pp.rs`: render `inductive T : Type → Type 1 where | V : ∀
  {A}, ... → T A`.
- `to_lean_fn.rs`: `has_cross_instantiation_recursion` detection
  helper, branch in `datatype_decl_cmd`, `datatype_inhabited_instance_cmd`
  for the manual Inhabited.
- `to_lean_fn.rs::datatype_to_cmds` + `datatype_group_to_cmds`: emit
  the manual instance alongside (or after) the inductive.
- `sanity.rs`: allowlist `Inhabited` (parameter-style bypassed name
  resolution via the `derives` field; only indexed-style references
  it as a Var node).

Pinned by `test_exec_call_recursive_generic_datatype_cross_instantiation`
(was negative pinning the rejection; flipped to positive). Catalogue
entry rewritten from "should work but untested" to LANDED.

**4-element datatype SCC — LANDED.** Cool-down probe. Catalogue had
"3-element SCCs are tested via `test_exec_three_element_datatype_scc`;
4+ element cycles go through the same Tarjan + mutual-block code path
but lack explicit regression tests." Tarjan is generic; depth-4
worked first try. Pinned by `test_exec_four_element_datatype_scc`
(A → B → C → D → A).

**Discipline notes worth recording:**

* *Deferring with a question vs deferring with a worry.* Yesterday's
  HANDOFF entry said "the chained-compare render itself is correct in
  spec fns... but a probe with `unfold in_range` failed... documented
  as a deferred investigation." That's deferring with a worry. The
  question was concrete: *does the goal contain `in_range`?* Two
  characters more in the deferral entry, and this morning would have
  been a 5-second confirmation rather than an investigation. The
  poem "The deferred question" captures the lesson.

* *The conservative estimate was optimistic about my fear, not about
  the problem.* For the cross-instantiation fix I estimated 2-4 hours
  of structural work; actual was ~30 lines after a 5-minute
  reflection on what Lean's restrictions actually permit. The fear
  was bigger than the problem. The user's "pause first" was the
  intervention that surfaced this. The poem "Indexed" captures it.

* *Catalogue drift is a docs-side analog of code-side drift.* The
  same review-lens discipline that catches stale code comments
  catches stale catalogue entries. Periodic audits are cheap and
  surface meaningful divergence. The 5 stale entries in this session
  had accumulated over ~3 weeks of work; a once-a-month audit pass
  would keep the catalogue accurate without ceremony.

**Net for the day** (2026-05-09 mid-morning continuation):
* Test counts: 310 → 313 e2e (+3 cross-inst test + 4-SCC test +
  2 spec-fn chained-compare from morning); 177 unit unchanged.
* Pending tasks: 8 (no change from morning's count — the cross-
  instantiation work was a #121 sub-feature, and the SCC test was
  also #121 coverage).
* 12 commits this session: 1 morning chained-compare/spec-fn-opacity,
  1 morning HANDOFF, 1 catalogue audit, 1 cross-instantiation
  feature landing, 1 4-SCC probe, 4 poems (Returned, The deferred
  question, The pause, Indexed, After the landing).
* 5 poems committed across the day (running total since morning):
  Returned, The deferred question, The pause, Indexed, After the
  landing.

**The arc, in one sentence**: the day was a small fix that grew into
an audit that grew into a real feature that finished with a small
probe, and the most important thing wasn't any single landing but
the user's two-word "pause first" that turned a multi-hour estimate
into a 30-line fix.

#### Current session (2026-05-09 evening — trait-bounded type param probe)

After the goodnight, a re-arrival. One small probe:

**Generic datatype with trait-bounded type params — pinned.** DESIGN.md
catalogue had this listed under "User-facing features not tested" as a
#108 edge: `enum Tree<A: Tag>` with a user-defined trait bound on the
type param. Prediction was that it would work because `height_fn_for_datatype`
ignores `dt.typ_bounds` and the structural height path doesn't need them
— Lean has no encoding of the user trait `Tag` to ask about anyway.
Confirmed: `test_exec_call_recursive_generic_datatype_trait_bound`
verifies first try with `enum TBox<A: Tag> { Leaf(A), Node(Box<TBox<A>>) }`
+ a `Marked: Tag` instantiation in the exec fn. One Rust-level wrinkle
on the way (Rust requires type params to be used non-recursively, so
`Leaf(A)` instead of `Leaf`); not a Tactus issue.

DESIGN.md catalogue entry flipped from "Untested" to ✅ pinned with a
note that the success is structural-not-incidental: the user trait has
no Lean-side encoding, so the bound silently drops and Verus enforces
it pre-Tactus.

**Net**: 313 → 314 e2e tests (+1). Pending count unchanged (sub-feature
under #121). Took ~10 minutes including the false-start on Rust's
recursive-type-param rule. The conservative estimate would have been
~30 minutes; the actual cost was below the cost of estimating
carefully.

**Multi-line def signatures probe (#118 edge) — pinned.** DESIGN.md
catalogue flagged `extract_prelude_names`'s line-based parser as a
concern for future prelude growth: "a future prelude addition with
`def name\n  : LongType := body` would not register the name." Probe
showed that prediction was wrong — the parser handles four multi-line
shapes (name-on-line-1 with type wrapping, implicit-binder section
with bracket section wrapping, body wrapping after `:=`, and modifier
on its own line via the bare-`def NAME` fallback). The single failure
mode is bare `def\n` separated from the name (e.g., `def\n  my_e :
Int := 0`), which is unidiomatic Lean. New unit test
`extract_prelude_names_multi_line_def_shapes` pins both directions —
what works and what doesn't — so a future parser change either keeps
working or surfaces clearly. DESIGN.md catalogue entry rewritten to
reflect actual surface; `worth a parser robustness pass` claim
softened to "theoretical-not-urgent" because the failure mode is
unidiomatic. Test count 177 → 178 unit (+1).

The discipline lesson: catalogue claims about *what fails* are also
catalogue claims, and they drift the same way claims about *what
works* do. The DESIGN entry was a guess from when the parser was
younger; the probe replaces the guess with the actual surface.

**5-element datatype SCC — pinned.** Linear extension of the 4-cycle
test pinned earlier today: P → Q → R → S → T → P. Same emission path
(`mutual { inductives } end` + accessors-out + `mutual { heights }
end`); Tarjan is generic over SCC size, so structural correctness
holds the same way at 5 as at 4. Very deep cycles (10+) remain
unpinned — Lean's mutual-block compilation cost is the latent
concern at extreme depth — but the cheap-test regime now covers
depths 4 and 5. Test count 314 → 315 e2e (+1).

**Generic datatype with uninhabited type param (#108 edge) —
upstream-blocked.** DESIGN.md catalogue had this as a Lean-side
concern: `List<Empty>` would fail `Inhabited (List Empty)` synthesis
at the call site, with the recommended fix being conditional
`deriving Inhabited`. Probe established the prediction is moot:
Verus rejects `enum Empty {}` itself with "datatype must have at
least one non-recursive variant," so an uninhabited type never
reaches Tactus. The Lean-side concern is structurally unreachable
through normal Tactus paths. Pinned by
`test_exec_generic_datatype_uninhabited_type_param_upstream_blocked`
(matches the Verus error string). DESIGN.md catalogue entry
downgraded from "known limitation we should fix" to "upstream-
blocked, not a Tactus concern." If Verus ever lifts the no-empty-
enum rule, the test surfaces as a flippable Err and the
conditional-deriving fix returns to relevance. Test count 315 → 316
e2e (+1).

The discipline lesson, again: catalogue claims about *what would
fail and how* are guesses about a counterfactual world. Probing
moves the claim from "guess" to "known surface" — and sometimes the
known surface shows the concern was solving a problem that doesn't
exist.

**10-element datatype SCC — pinned, latent concern was overstated.**
Catalogue had "very deep cycles (10+) remain unpinned — Lean's
mutual-block compilation cost is the latent concern at extreme
depth." Probe at depth 10 (E0 → E1 → ... → E9 → E0) runs in ~6.8s,
vs ~5s for the 4 and 5 cycles. Near-flat compile time across 4 → 5
→ 10 means the concern only kicks in at much larger depths if at
all. DESIGN.md catalogue entry rewritten to reflect the measured
surface: depths 4, 5, and 10 confirmed; concern softened from "kicks
in at extreme depth" to "if at all." Test count 316 → 317 e2e (+1).

The same discipline pattern: a guess about cost ("Lean compilation
is the latent concern") replaced by a measurement (~6.8s, near-
flat). Three of today's four probes have shifted catalogue claims
in the *softer* direction — the worry was bigger than the surface.

**AssertBitVector with fn call — real codegen panic (#147).** The
day's first probe to shift the catalogue in the *harder* direction.
DESIGN.md claimed two complementary mitigations: Verus rejects
upstream, AND Tactus rejects cleanly. Probe established BOTH wrong:
`assert(spec_fn(x) ^ x == 0) by(bit_vector)` panics in
`lean_verify/src/generate.rs:473` with "Tactus codegen produced
unresolved references." Verus's pre-injected `Assume(ens)` goes
through the regular Int-mode renderer (which supports Calls); that
renders `id_u8(x)` as a Var reference; dep_order doesn't include
`id_u8` in the preamble dep set; sanity check panics.

Pinned as `Err(_)` by `test_exec_assert_bit_vector_with_fn_call_panics`
so a future fix turning the panic into clean rejection or successful
verification surfaces. Catalogue entry rewritten with the actual
shape; new task #147 filed with three candidate fix shapes (extend
dep_order, reject Call in Int-mode pre-injection, or reject upstream).
Test count 317 → 318 e2e (+1).

The discipline lesson, complemented: probes don't only find
overstated worry. They sometimes find unstated worry. The worst
catalogue entries aren't the ones that are pessimistic — they're the
ones that confidently state both the bug *and* the rejection, and
neither holds. A guess that two safety nets exist is worse than a
guess that one does.

**#147 — fixed in the same session it was filed.** After landing
the panic-pin, the user pushed for diagnosis rather than a guess at
the fix shape. Diagnosis surfaced the actual cause was BIGGER than
bit_vector: `dep_order::seed_worklist` walked only require/ensure,
never the function body. *Any* spec fn call in a body-level assert
(plain `assert(P)` too, not just bit_vector) hit the same bug.

The diagnostic test (`test_exec_plain_assert_with_spec_call`) gave
a cleaner reproduction without bit_vector noise. After the
seed_worklist fix landed, the diagnostic surfaced a SECOND latent
bug: `spec_fn_to_ast` reused `fn_binders` which adds u-type bound
hyps as binders — wrong for spec-fn defs (changes the type from
`Int → Int` to `Int → Bound → Int`). Fix: `fn_binders_without_bound_hyps`
helper for spec-fn defs.

Two latent bugs, three commits, full e2e suite green at 319.

The discipline lesson: when a fix candidate is named, *diagnose
before patching*. Today's session almost shipped the smaller fix
(extending dep_order via the bit_vector path specifically) — would
have left the second latent bug for someone else, plus the broader
seed_worklist gap to surface again the next time someone called a
spec fn from a body assert. The user's "diagnose first" turned a
narrow fix into a structural one.

Test count 318 → 319 e2e (+1 net: pinned the bit_vector test as
Ok flipped from Err panic-pin, and added the plain-assert diag).
Task #147 closed.

**Review pass for #147** — ran lenses 1, 3, 4, 5, 13, 14 against the
diff. Findings:
- *Lens 14 (regression-test):* the bit_vector + plain-assert tests
  cover top-level body asserts but not nested positions. Probed with
  `id_u8` in a loop invariant — *codegen* worked (no panic, fix
  reaches the loop's invs via walk_expr's body recursion), but
  `tactus_auto` couldn't close `id_u8 (i+1) = (i+1)` in goal
  position (spec fns are `noncomputable def` and the default toolbox
  can't unfold them). Reshaped to nested-in-loop body assert
  (`assert(id_u8(i) == id_u8(i))`, reflexive) which closes via
  `simp_all`. Pinned by `test_exec_loop_body_assert_with_spec_call`.
- *Lens 5 (documentation):* documented the auto-tactic limitation
  (spec fns in goal position need explicit unfold) in DESIGN.md
  catalogue. Surfaced as a separate concern from #147; the codegen
  fix is complete, this is the layer below.
- *Lens 13 (typed-invariant):* the `bool include_bound_hyps` flag
  on `fn_binders_with_bounds` could be promoted to an enum
  (`enum BoundHyps { Include, Omit }`). Decided against — only 2
  internal callers, both via named wrappers (`fn_binders` /
  `fn_binders_without_bound_hyps`), and the wrappers already encode
  the choice at the public API. If a third caller appears with
  different semantics, revisit.
- *Lens 1 (Linus):* no flag-soup, no defensive code, no orphaned
  docstrings.
- *Lens 4 (upstream-brittleness):* the body walk relies on `walk_expr`
  handling all VIR-AST shapes recursively. Pre-existing pattern —
  `walk_expr` already covers the broad set used by exec/proof fn
  bodies. No new brittleness introduced.
- *Lens 3 (coverage):* nested-in-loop pinned. Other latent shapes
  (spec fn in proof block, spec fn in if cond) follow from
  walk_expr's existing coverage; no specific test added.

Test count 319 → 320 e2e (+1 from review-pass regression test).

#### Current session (2026-05-10 — body-assert pattern + #148 prototype rejection)

After yesterday's review pass closed #147, the morning continuation
followed up on the spec-fns-in-goal-position concern and then ran
into a meta-question about whether to extend Tactus's surface syntax.

**Try-unfold workaround pinned.** Yesterday's catalogue entry
recommended `proof { unfold f }` as the workaround for spec fns in
goal position. Probe established that's incomplete — the tactic-prefix
mechanism applies to every theorem in the fn, including ones whose
goals don't mention `f` (e.g., the first invariant init theorem
`i ≤ n`). Bare `unfold f` fails with "Tactic unfold failed to unfold
f" on those. The actual workaround needs `try unfold f`. Pinned by
`test_exec_loop_invariant_with_spec_call_try_unfold`; DESIGN.md
catalogue entry corrected. Same pattern as yesterday's multi-line def
probe — workaround shape was a guess, never verified. Test count
320 → 321 e2e (+1).

**Body-assert pattern as the alternative.** Probed whether the user
can discharge a loop-invariant maintain obligation by placing
`assert(invariant_expr) by { simp_all [f] };` at the right point in
the body. Works — assert at end-of-body (post-assignment, so `i` is
post-iter value) puts the asserted hypothesis in MAINTAIN's OblCtx;
the obligation's goal closes via the asserted hyp. `simp_all [f]` is
the canonical complete-proof shape (intros + unfold + close). Pinned
by `test_exec_body_assert_discharges_invariant`. DESIGN.md catalogue
now lists BOTH workarounds (body-assert + try-unfold prefix) with the
trade-off (targeted vs uniform). Test count 321 → 322 e2e (+1).

**Substrate-vs-surface exploration.** User asked why Lean needs
per-obligation proof attachment when Z3 didn't. Answer: Z3's
automation is global+aggressive search (one global `reveal_with_fuel`
knob, fuel-bounded saturation handles unfolding implicitly); Lean's
tactics are local+deterministic (one goal at a time, you ask for
exactly what you want). Per-obligation matters in Lean because every
obligation is its own little world. Verus's surface has ALWAYS had
tactic-attachment syntax (`assert(P) by { tac }`, `recommends ... via
Expr`, etc.) — Z3 just didn't make most of it load-bearing. Captured
in poem "What Z3 hid."

**#148 prototype and rejection.** User suggested extending the surface
syntax: `invariant P by { tac },` would attach a tactic directly to
the invariant clause, more readable than body-assert. Explored four
implementation paths:
- **Stage 0 (parser change)** — added `Specification.tactics: Vec<Option<TacticBy>>`
  parallel array in syn-verus, gated on Context::Expr to avoid hijacking
  fn-signature `by { fn_tactic }`. Landed cleanly with sanity tests.
- **Stage 1 (proc-macro desugaring)** — visit_expr_while_mut would
  synthesize `assert(P) by { tac };` body-assert stmts (before loop
  for INIT, end of body for MAINTAIN), reusing existing assert-by
  machinery. Implementation hit a parser interaction we didn't fully
  diagnose: simple test cases that worked under Stage 0 alone failed
  when Stage 1's syntax.rs changes were added.
- **Stages 2+ (pipeline threading)** — sketched: VIR `LoopInvariant`
  gains a tactic field threaded through proc-macro → rust_to_vir →
  SST → sst_to_lean. Estimated ~150-250 lines across 5-6 files
  including VIR shape change.
- **Roll back to body-assert** — user said "I think you're right that
  we shouldn't be adding extra syntax, the better thing is not to do
  it."

Full revert: Stage 0 parser change, sanity tests, defer-doc all
reverted. Body-assert remains the documented recommendation. DESIGN.md
gained "Considered surface extensions (rejected)" subsection
recording what we tried, why we stepped back, and four specific
conditions that would shift the cost-benefit if revisited.

Captured in poems "Two ways to be minimal" (typed shape vs smallest-
disturbance — they don't always agree) and "What Z3 hid."

**Session-end review pass.** Ran lenses 1/4/5/14 against the
surviving session changes:
- *Lens 5*: `fn_binders_with_bounds` comment said "both paths need to
  agree" — stale after #147 added a third path (spec_fn) that
  deliberately diverges. Updated to enumerate all three callers.
- *Lens 4*: DESIGN.md #148 rejection entry referenced two test names
  that were reverted; added clarifier noting they're forensic-only.
- *Lens 14*: #147 bug class 2 (spec_fn_to_ast bound hyps) only tested
  with u8; structurally generalizes to all fixed-width ints. Not
  chased — fix is type-uniform; a test wouldn't deepen confidence.
- *Lens 1*: `seed_worklist`'s parameter is named `proof_fns` but
  accepts any root fn (proof or exec). Pre-existing misnomer, not
  introduced by #147. Left for future cleanup.

**Net for the day:**
- Test count: 320 → 322 e2e (+2: try-unfold, body-assert).
- Task #148 marked completed (rejected after prototype).
- Code touched and surviving: only the 2 new tests + DESIGN.md
  additions (catalogue workarounds + #148 rejection rationale + review
  doc fixes). Everything else was reverted.
- 3 poems for the day: "What Z3 hid," "Two ways to be minimal," plus
  yesterday's "The interventions" referenced.

**The arc:** most of today's "work" was learning that the syntax
extension wasn't worth doing. The body-assert mechanism is fully
expressive; the parser-extension's value was purely readability. The
detour confirmed it the hard way. The lessons in today's poems and
DESIGN's #148 rejection note carry the learning forward.

#### Current session (2026-05-11 — #113 BinaryOp::StrGetChar)

Clean landing after yesterday's not-shipping day. `verus_builtin::
strslice_get_char(s, i)` (Verus surface syntax, VIR `BinaryOp::
StrGetChar`) now lowers cleanly through both expression renderer
paths.

**The latent bug.** The shared `non_binop_head` table emitted
`"String.get"` for `BinaryOp::StrGetChar` — used by both the VIR-AST
renderer (`to_lean_expr.rs`) and (with my fix) the SST renderer
(`to_lean_sst_expr.rs`). But Lean's `String.get` is the *wrong*
function: it takes `String.Pos` (a byte offset) and returns Lean's
`Char`. Verus's `strslice_get_char(s, i)` is codepoint-indexed and
returns `char` → Tactus's `Nat`. Either path would have produced
Lean that failed elaboration. The proof-fn path hadn't been exercised
by any test, so the bug had sat dormant since `non_binop_head` was
extracted to `expr_shared.rs`. Pre-existing rejection in the SST
path meant the symptom never surfaced from exec fns either.

**The fix.** Added `Tactus.strGetChar : String → Int → Nat` to
`TactusPrelude.lean` with body `(s.data[i.toNat]!).toNat` — `s.data
: List Char` is the underlying codepoint list, `[i.toNat]!` is the
panic-on-OOB `GetElem!` indexer (same shape as `array_index`'s `xs[i]!`
from #91), `.toNat` unwraps the `Char`. Routed `non_binop_head` to
the new name. Dropped the SST rejection arm — falls through to the
generic `App(non_binop_head(op), [l, r])` path automatically. Stale
"only reachable case is Xor" comment updated to enumerate Xor and
StrGetChar.

**Three tests** pin the rendering surfaces:
- `test_proof_strslice_get_char` — proof fn ensures `strslice_get_char(s,
  0) == strslice_get_char(s, 0) by { rfl }`. VIR-AST path via
  `vir_expr_to_ast`.
- `test_exec_strslice_get_char_in_assert` — `#[verifier::tactus_auto] fn
  check(s: &str) { assert(strslice_get_char(s, 0) == strslice_get_char(s,
  0)); }`. SST body-level path.
- `test_exec_strslice_get_char_in_ensures` — exec fn ensures using the
  builtin. SST `ens_exps` path.

All three close via `tactus_auto`'s first rung (`rfl`) — both sides
substitute identically to `Tactus.strGetChar s 0`.

**Initial implementation hit one Lean-API drift gotcha.** Wrote
`s.data.get!` initially — Lean 4 no longer has `List.get!` (was
removed in favor of `GetElem!` notation `[i]!`). Pivoted to `s.data[i.toNat]!`,
which is the same shape we use for array indexing in `BinaryOp::Index`.

**Net for the session**: 1 commit incoming, ~50 lines of source change
across 4 files (prelude + 2 renderers + tests), +3 e2e tests. Test
counts now 325 e2e + 1 coverage + 178 unit + 7 integration. One
pending task closed (#113).

#### Current session (2026-05-11 continued — #121 coverage probes)

Probed five catalogue items that DESIGN.md flagged as untested or
"never managed to write a clean test." Four turned out to already
work; one found a real automation gap. Lesson echo from earlier
sessions: *catalogue staleness is real*, and the cost of a probe is
small compared to the cost of trusting a stale entry.

**What was probed and what landed:**

- **`BinaryOp::Xor` concrete case**: pinned by
  `test_exec_xor_bool_concrete` (`assert((true ^ false) == true)` —
  closes via `decide` in `tactus_auto`'s ladder). The existing
  `test_exec_xor_bool` was a fn-return-equals-body smoke test that
  didn't actually exercise xor reasoning; this fills the
  reasoning-side gap for concrete operands.

- **`BinaryOp::Xor` free-vars commutativity** — pinned by
  `test_exec_xor_bool_free_vars_commutative` in its user-explicit
  shape: `assert((b1 ^ b2) == (b2 ^ b1)) by { simp_all
  [Bool.xor_comm] };`. The probe initially closed this by extending
  `tactus_auto`'s simp set, but on user feedback (same session) we
  reverted: minimal automation and transparent user proofs are
  preferred over accreted closer extensions. The lemma being used
  is right at the assertion site, not buried in the closer's set —
  the proof on screen reflects the actual reasoning. DESIGN.md §
  "Bool vs Prop" → "The trade-off accepted" documents this as the
  canonical pattern for Bool-operation gaps under always-Prop
  rendering.

- **Tactic referencing loop-local variables**: pinned by
  `test_exec_assert_by_omega_in_loop_body` — `assert(P) by { omega }`
  inside a loop body actually works for the common case (omega
  resolves both loop-modified vars and fn-param vars as bound names
  in the maintain theorem). Catalogue had marked this "Untested
  directly"; turned out the common-case works fine. What remains
  untested — and probably never tractable — is a user tactic that
  references a hypothesis by name like `exact h_inv` (Hyp frames
  get codegen-internal names, not user-controlled ones).

- **Closure with user-written `requires`**: pinned by
  `test_exec_closure_with_requires`. Verus syntax: `|x: u8|
  requires P { body }` (no `->` between params and `requires`).

- **Closure with user-written `ensures`**: pinned by
  `test_exec_closure_with_ensures`. Verus syntax: `|x: u8| -> (r:
  u8) ensures P { body }` (return binding `(r: u8)` required).

The catalogue had claimed both closure-spec cases "we didn't manage
to write a clean test." Both work fine with the right syntax —
`requires` and `ensures` use different shapes (no `->` before
`requires`, `->` before `ensures`); the probe found them by looking
at how vstd / other Verus tests write them.

**The pattern:** four out of five "untested" catalogue items turned
out to work; one had a real gap. The ratio matches yesterday's
StrGetChar surfacing — most-things-actually-work, but the rare
genuine gap is the high-value find. Coverage's job is to schedule
the first-use that surfaces (or doesn't) the gap.

**DESIGN.md catalogue updates**: three stale entries flipped from
"untested" to "pinned" with the test names; one entry expanded to
document the real Xor commutativity gap with the workaround.

**Net for the session**: 5 new e2e tests, 3 catalogue entries
updated. Test counts 325 → 330 e2e. One pending task closed (#121
partial — the surfacing-via-probes class. The full task umbrella
includes any future probes too).

#### Current session (2026-05-11 continued — xor gap-find / design honesty / audit sweep / #123 heartbeats / lens 15)

After the #121 probe surfaced the bool xor commutativity gap, the
day spiraled into a substantial design-clarification stretch that
ended up reshaping the codebase's approach to automation.

**Bool xor commutativity gap → fix → revert.** The probe found
`assert((b1 ^ b2) == (b2 ^ b1))` couldn't close under
`tactus_auto`'s default closer. Initial fix: add `Bool.xor_comm`
to `simp_all`'s lemma set in the prelude. Test flipped Err → Ok.
Committed. **User pushback** (same session): adding lemmas to the
default closer rebuilds a tiny version of the thing Tactus was
built to escape (Z3-style opaque automation). Reverted the simp-
set extension; rewrote the test to use the user-explicit shape
`assert(...) by { simp_all [Bool.xor_comm] };`. Saved the
preference to memory:
*tactus_auto stays deliberately minimal; prefer transparent user
proofs over extending the closer's simp set.*

**Bool vs Prop design honesty.** DESIGN.md's "Bool vs Prop"
section promised context-sensitive rendering (Prop in spec, Bool
in exec). The code unconditionally renders `TypX::Bool` as `Prop`.
Audit revealed the design-doc/code mismatch. Rewrote the section
to document **always-Prop as the deliberate landed design**, with
a "Why always-Prop" subsection (spec-first model;
Classical.propDecidable covers coercions; no mode threading
needed) and a "Considered: context-sensitive bool rendering"
subsection recording the cost-benefit. Updates the existing entries
across DESIGN.md / HANDOFF.md / tests that had restated the
"promises but doesn't implement" framing.

**5-audit transparency sweep.** Inspired by the bool xor moment,
ran a sweep through five candidate "automation hiding work" sites:
- **#149 tactus_case_split** — keep in `tactus_auto`. Structural
  mirror of user code (recursion-on-datatype → case-split-at-proof).
  Pinned the per-arm proof shape via `proof { cases k with | Foo x
  => tac | Bar y => tac }` (`test_exec_match_enum_with_per_arm_proof`)
  using Lean's native syntax through `proof { }` blocks — works
  today, no codegen change needed.
- **#150 deriving Inhabited** — keep. The "over-deriving" framing
  was conservative; `Inhabited` is more broadly load-bearing than
  accessor fallbacks (GetElem!-style indexing needs it too).
  Doc framing revised.
- **#151 Classical.propDecidable** — keep. New DESIGN.md section
  "Classical-logic commitment" documents what classical gives
  (excluded middle, epsilon for Choose, Classical.arbitrary for
  accessor fallbacks, Classical.choice for Seq.index). Substrate
  not behavior. New e2e test `test_proof_classical_excluded_middle`
  pins user-visible classical use.
- **#152 emit_done_or_split** — keep. Restructures (∧-split + Let-
  peel) without changing what's proven; buys per-conjunct error
  localization + per-theorem caching. Doc verdict added.
- **#153 ret-substitution (#128)** — keep. Eliminates a redundant
  ∀ when callee's ensures contains `r == E`; logical equivalence;
  visible in output. Doc verdict added.

All five audits returned the same shape: *the design is right; the
deliverable is doc clarity.* Net 0 code changes from the sweep
itself; +1 test (Classical EM) + 5 DESIGN.md additions.

**#123 heartbeats attribute** (`#[verifier::heartbeats(N)]`).
Plumbed through the same pipeline as `tactus_tactic`:
Attr::TactusHeartbeats(u32) → VerifierAttrs / FunctionAttrsX →
Theorem::heartbeats: Option<u32> → lean_pp emits
`set_option maxHeartbeats N in\n` before the theorem when Some(N).
Works for both proof fns (`to_lean_fn::proof_fn_to_ast`) and exec
fns (`ObligationEmitter::heartbeats` set at construction; every
emitted theorem inherits). Per-module .lean generation and CI
matrix (the other two pieces of #123) deferred as future work.

**14-lens review pass on heartbeats.** Three actionable findings:
- Lens 7 + 12 (error-message + edge-case): malformed invocations
  (`heartbeats()`, `heartbeats(1.5)`) fell through to the generic
  "unrecognized verifier attribute" catch-all. Added
  `get_heartbeats_arg` helper mirroring `get_rlimit_arg`'s shape.
- Lens 3 (coverage): added `test_exec_heartbeats_multi_theorem`
  (loop fn — every per-obligation theorem inherits the override).
- Lens 5 (doc): DESIGN.md notes on Z3-path interaction (heartbeats
  is noop for non-Tactus fns) and malformed-invocation handling.

**Lens 15 (magic-string lens) introduced and applied.** User
pointed out that the heartbeats test used a magic-string substring
matching the error message verbatim — duplicated between
`attributes.rs` and the test. I had initially framed this as
"approach 1 couples tests to phrasing"; user corrected: shared
constants are exactly what makes phrasing edits percolate to
tests automatically.

Added new lens to the review framework (DESIGN.md § "Code review
strategy"). The lens distinguishes three categories:
- Tactus-controlled strings → extract `pub const`.
- Upstream-emitted (Lean / Verus) → stable substring (out of our
  control).
- Dynamic-content strings → stable tag prefix as `pub const`,
  used as the search substring.

Applied to the heartbeats landing + extended to the broader
codebase:
- New `vir::tactus_messages` module: canonical home for Tactus-
  controlled user-facing message constants. Reachable from both
  `rust_verify` and `rust_verify_test` (no link-graph
  complications around rustc_private).
- 10 constants extracted: `HEARTBEATS_ARG_ERR`,
  `TACTUS_TACTIC_EMPTY_ERR`, `ASSUME_WARNING_TAG`,
  `ASSIGN_NON_SIMPLE_LHS_TAG`, and 7 `ASSERT_LABEL_*` for the
  Tactus error-format suffix labels (postcondition / loop
  invariant / loop decrease / precondition / termination / loop
  condition / branch condition).
- `paren_label(label) -> String` helper for the `(label)` framing
  in `at <loc> (<label>):` error format.
- 14 test sites updated from `m.contains("(<label>)")` to
  `m.contains(&paren_label(LABEL_X))` (or directly for non-paren
  matches). `lean_ast::AssertKind::label()` returns the
  constants; `lean_process::format_error` uses `paren_label`.

**Net for the day** (all sessions on 2026-05-11 combined):
- 22 commits.
- 336 e2e + 180 unit + 7 integration + 1 coverage tests pass
  (322 → 336 e2e, 178 → 180 unit).
- 13 poems committed (POEMS.md index updated).
- Major DESIGN.md updates: "Bool vs Prop" rewrite, "Classical-
  logic commitment" new section, 5 audit verdicts, lens 15 added
  to review framework, "Heartbeat annotations" promoted to
  LANDED.
- 3 feedback memories saved: commit-freely permission, minimal-
  automation preference, layered-automation principle.

**Closing themes of the day**: the work that mattered most was
noticing what was already there (audit sweep verdicts) and making
the rightness legible (doc updates, lens 15 framework). The one
moment of code-change-required (heartbeats #123) was paved by
prior plumbing (#81 tactus_tactic); the one moment of code-
change-attempted-then-reverted (Bool.xor_comm simp extension) was
itself a lesson about not becoming the thing being audited.

#### Current session (2026-05-11 continued — #127 loop_isolation: false)

**The encoding question that drove the design.** Verus lowers
`while c { body }` with isolation=false to break-lowered form
(cond:None + inserted `if !c { break; }`). AIR encodes this via its
`Breakable` primitive — natural-exit fact `¬c` is preserved by AIR's
state-preservation across `Break`. Lean's kernel has no equivalent
control-flow primitive (it's pure type theory; no breakable/state-
preservation constructs).

**Design space explored** (in conversation):
- Option 1: Lift rejection, document limitation, user uses
  `allow_complex_invariants` + `ensures` for post-loop facts.
- Option 2: Pattern-detect `if !c { break; }` at body[0..1] in
  Tactus, add side-channel hyp for `¬c` post-loop.
- Option 3: Path-condition tracking on breaks (the truly general
  encoding for control flow in Lean — disjunction over all
  break paths). Invasive, touches Wp::Done semantics throughout.
- Option 4: Pattern-detect + reverse-engineer the conversion at
  Tactus's SST entry (one transformation, existing cond:Some
  encoding handles the rest).
- **Option 5 (landed)**: Don't pattern-detect at all — preserve
  the pre-conversion cond in an upstream `StmX::Loop` field. AIR
  ignores the field; Tactus reads it. No shape-detection needed.

The general principle that emerged: when the target IR lacks a
primitive the source IR uses, the cleanest answer often isn't to
*re-encode* the primitive but to *preserve the information the
primitive was reconstructing*. Verus's break-lowering reconstructs
"how this loop exits"; Tactus's cond:Some encoding can use that
info directly if we just keep the cond around.

**Implementation**:
- Added `original_cond: Option<(Stm, Exp)>` to upstream `StmX::Loop`
  in `vir/src/sst.rs`. Populated by `ast_to_sst.rs` at the break-
  lowering conversion site (line 2675-2685) with the pre-conversion
  `(c_stm.clone(), c_exp.clone())` BEFORE mutating cnd to None.
- AIR's `sst_to_air.rs` binds `original_cond: _` in its
  `StmX::Loop` destructure — explicit ignore, per the upstream-
  robustness pattern (no `..` in StmX matches).
- `poly.rs` and `sst_visitor.rs` walk `original_cond` like `cond`
  so its embedded Stm/Exp receive the same visitor transformations.
- `sst_vars.rs` clones `original_cond` through both passes.
- Tactus's `build_wp_loop` reads `original_cond`. When `cond` is
  None but `original_cond` is Some AND soundness gates pass, treat
  the loop as cond:Some(original_cond). The existing cond:Some
  encoding handles the rest — body's vacuous if-not-c-break
  obligation discharges under contradictory `c ∧ ¬c` via simp_all's
  contradiction handling; use_obl gets `¬c` as natural-exit hyp.

**Soundness gates** (refuse recovery, fall through to cond:None):
- `count_breaks_targeting_this_loop(body, label) > 1`: user has own
  breaks alongside Verus's inserted one. Multiple exit paths;
  `¬c` not universally true.
- `label.is_some()`: labeled loops would need cross-label break
  counting (deferred).
- Non-empty cond_setup in `original_cond`: setup with calls/short-
  circuits needs scoping work for temp bindings.

**Tests** (10 new, all pass — initial 6 + 4 from review's coverage
lens):
- `test_exec_loop_isolation_false_fn_level` / `_loop_level`: basic
  acceptance at both attribute placements.
- `_natural_exit`: the post-loop `i == n` case — canonical
  motivation. Verifies via the original_cond recovery path.
- `_outer_ctx`: outer fn precondition `n <= 100` flows into both
  body and after via OblCtx inheritance.
- `_user_break_falls_through`: soundness gate — multi-break loop
  has count > 1, recovery refused, falls through to cond:None
  encoding. Fn still verifies (invariant alone gives `r <= n`).
- `_invariant_violation`: negative — invariant maintain obligation
  still fires under the recovery encoding.
- `_labeled_fall_through_ok` / `_labeled_natural_exit_falls_through`:
  pair pinning the labeled-loop gate. Positive case verifies via
  invariant alone; negative case is the *flippable Err* — when
  cross-label break counting is implemented, the Err test turns
  Ok and tells future-us the limitation is gone.
- `_complex_cond_fall_through_ok` /
  `_complex_cond_natural_exit_falls_through`: same shape for the
  non-empty-cond_setup gate. Flippable when cond_setup scoping is
  implemented.

**Review pass** (lenses 1 + 6, then 3 + 12):
- Lens 1 (Linus) + 6 (reasoning clarity): the `effective_cond`
  match was 3 arms but 2 trivially returned `cond`. Refactored to
  `original_cond_recoverable: bool` + ternary. The soundness-gate
  logic now reads as a single condition rather than nested if-
  inside-match. -8 lines, clearer shape.
- Lens 1 + 6 (ast_to_sst.rs): `original_cond` population was a
  let-mut + conditional assignment inside the conversion branch.
  Replaced with `let original_cond = if !simple_while { cnd.clone() }
  else { None };` before the branch. Removes the implicit "capture
  before mutating cnd" ordering dependency.
- Lens 3 (coverage) + 12 (edge-case): added 4 fall-through tests
  (above) pinning the labeled-loop and non-empty-cond_setup gates,
  with positive + flippable-Err pairs.

**End-to-end**: 336 → 346 e2e + 180 unit + 7 integration + 1
coverage tests pass. vstd still verifies (1530, 0 errors). #127
closed.

#### Current session (2026-05-11 continued — #117 fuse two-pass audit)

Same shape as yesterday's #149–#153 audit sweep, applied to the
remaining "Architecture cleanups" pending task. The prior entry
said "fusing would save a pass but entangles modifications with
WP construction. Documented; left alone." — short, opinionated,
no rationale carry-over for a future reader. Audit confirmed the
verdict and produced the missing rationale:

- `collect_modifications` cares about 4 of ~15 statement variants
  `build_wp` walks (Assign/Block/If/Loop only). Fusion would mean
  threading `&mut ModCollector<'a>` through 7 production
  `build_wp` call sites (entry, Block-sequential, If-then,
  If-else, ClosureBody, Loop-body, two cond_setup wraps).
  Every future statement variant would have to consider both
  concerns.
- Realistic loop bodies are 10-100 stmts; verification time is
  dominated by downstream Lean checking, not Rust-side tree
  walks. The redundancy is also bounded the other way:
  `collect_modifications` runs only on loop bodies, so non-loopy
  fns pay nothing.
- Post-hoc extraction from the built Wp tree was considered:
  `Wp::Let` conflates mutation-as-shadowing (`is_init: false`
  assignments) with new-binding lets, so walking the Wp tree
  post-hoc can't distinguish "external mod" from "local let"
  without information that the pre-pass already has natively.

DESIGN.md entry updated with the verdict + conditions for
revisiting (load-bearing profile, upstream `StmX::Loop` mod
stashing, or a general `WpCtx`-style accumulator that all
variants already touch). Same audit-sweep shape: net 0 code
changes, deliverable is doc clarity. #117 closed.

#### Current session (2026-05-12 — NonLinear, body-less spec fns, cross-crate audit, trait gate, external_body)

Long arc: several substantial landings that reshape how Tactus
handles spec-fn emission, trait emission, and cross-crate scope.

**`AssertQueryMode::NonLinear` lowering — LANDED.** Verus's
`assert(P) by(nonlinear_arith)` now routes through a new
`Wp::AssertQuery { primary, preamble, body, after }` variant
carrying mode-specific tactic + preamble fragments. The walker
composes the full closer at scope-entry time:
`first | (intros; primary) | (<outer_closer>) | fail "<scope msg>"`.
`obl.new_scope(closer, preamble)` installs the composed closer +
preamble and drops enclosing-scope Hyps (matching Verus's
NonLinear query semantics — only requires + typ invariants are
in scope). Every theorem the body's recursive walk emits picks
them up. The trailing `fail` overrides Lean's last-failure-wins
reporting so users see "by(nonlinear_arith) scope: could not
close" instead of `tactus_auto`'s misdirected fallback. Generic
over `primary` — future query modes (Polyrith etc.) reuse
`Wp::AssertQuery` with a different tactic. (Any such future mode
is **upstream-blocked**, not Tactus homework — Verus's
`AssertQueryMode` enum only accepts the corresponding surface
syntaxes.) Pinned by `test_exec_assert_nonlinear_commutative`,
`_with_requires`, `_with_proof_block`, `_scope_resets`,
`_inside_loop`, `_nested_scopes`, `_wrong` (negative, also pins
the scope-named failure message). Shape-drift guards:
`ast_to_sst_emits_assume_assert_for_nonlinear_body` (Verus's body
shape) + `nonlinear_preamble_fragments_shape_pinned` (Mathlib
import path).

**Body-less spec fn emission as Lean axiom — LANDED.** Pre-fix,
`spec_fn_to_ast` returned `Command::Def(..., body: sorry)` for
body=None fns (`pub uninterp spec fn`, external_body spec fns,
cross-crate spec fns whose body was stripped). But dep_order's
`build_spec_fn_map` filtered body=None fns BEFORE they reached
emission — so the sorry branch was dead code, and at call sites
the reference was unresolved. Audit removed the filter and routes
through `Command::Axiom { name, binders, ret_ty, attrs }`. Lean's
`axiom` is the right encoding: declares a constant whose value is
unspecified, matching Verus's "this is just a symbol with a type"
semantics. Surfaced by #122 cross-crate probe 6 (local
`pub uninterp spec fn` reference); test name
`test_uninterp_spec_fn_referenced_from_proof`.

**#122 cross-crate audit (probes 1-6) + sanity check returns Err
not panic — LANDED.** The cross-crate verification task was
originally framed as a major Phase 3 feature (CrateDecls.lean
file generation). Audit 2026-05-12 established that
`merge_krates` already brings imported crates' fns into the
merged `vir_crate` Tactus receives, and `export_crate` preserves
`pub open spec fn` bodies. Probes 1-3 (`pub open spec fn` calls
from vstd) work end-to-end. Probe 4 (`Option<u8>` via
`vstd::prelude::*`) works. Probe 6 (local `pub uninterp spec fn`)
works after the body-less emission fix above. The genuine
remaining gap is Probe 5 (`vstd::seq::Seq` external_body type
emission) — see external_body section below. **#122 framing was
too pessimistic**; the `CrateDecls.lean`-per-file infrastructure
isn't blocking. Narrower fix items tracked: #125 cross-crate
trait method decls, external-body type opaque emission, dynamic
dispatch.

Concurrent **sanity check now returns Err instead of panicking**.
`debug_check` originally panicked on unresolved references,
killing the test-harness process and preventing graceful error
reporting. Now returns `Result<(), String>` propagated as
`CheckResult::Failed`. Test pinning becomes possible: probe
tests can assert specific sanity-error patterns via `=> Err(_)`.
Pre-fix the panic was either masked by accidental cmd ordering or
by test harness signal handling — neither was reliable. Also
inverted the order: pp + write to disk BEFORE sanity, so the
generated `.lean` is always on disk for inspection even when
sanity rejects.

**Trait class + instance emission rework — LANDED.** Pre-rework,
the trait Instance emission gate was correlated-by-accident with
method-reach (traits only entered `refs.traits` when an impl
method body was walked). Body-less spec fn emission broke that
correlation, surfacing the latent design flaw. New explicit gate:
emit `instance : Tr T` iff BOTH `refs.traits.contains(Tr)` AND
`refs.datatypes.contains(T)`. The class emission gate becomes a
co-dependent: emit `class Tr` if EITHER `refs.traits` contains it
OR any instance of `Tr` will emit. Class-defaults work landed
alongside this: spec-mode methods with a trait-side default body
get `default` rendered via `vir_expr_to_ast` (load-bearing for
Lean typeclass dispatch); exec/proof methods get the placeholder
`default` (their bodies aren't load-bearing — `walk_call` inlines
specs, not bodies via typeclass dispatch). Shared
`call_inlining::collect_inlined_at_call` abstraction concentrates
the trait-method spec-source resolution (handles
`TraitMethodImpl → kind.method` cross-crate fallback). See
DESIGN.md § "Trait class and instance emission".

**External-body type opaque emission — LANDED.** Types declared
`#[verifier::external_body]` (canonical: `vstd::seq::Seq`,
`vstd::set::Set`, `vstd::map::Map`) emit as opaque axioms
rather than empty `structure` declarations. Pre-fix, the empty-
struct emission gave every external_body type a unique inhabitant
(`T.mk`), so any two values collapsed via `cases x; cases y; rfl`
— a real soundness gap. Shape: `axiom T : Type` (or
`axiom T : Type → Type` for generics) plus
`@[instance] axiom T.instInhabited : Inhabited T`. Inhabited is
required when an external_body type is a field of another
datatype (accessor fallbacks `default` need `[Inhabited (T A)]`).
Downstream: parent datatypes with external_body fields drop
`deriving Inhabited` (axiom-backed defaults aren't computable)
and get a manual `noncomputable instance` instead. Pinned by
`test_external_body_soundness_gap_probe` (empty-struct exploit
now fails to verify — the canonical hole closed),
`test_external_body_distinct_applications_collapse_probe`,
`test_external_body_embedded_in_enum`,
`test_cross_crate_probe_5_seq_in_spec` (vstd::seq::Seq emits as
opaque axiom — closer behavior unchanged for the documented
axiomatic-equality reason, not "unknown constant" anymore).

**Net for the day**: ~25 commits. NonLinear scope + body-less
axioms + cross-crate audit + trait gate rework + external_body
opaque + #122 reframing. Test counts 346 → 388 e2e. Three
real soundness gaps closed (external_body collapse, body-less
unresolved refs, panic-not-Err). DESIGN.md expanded substantially
(class emission, external_body, NonLinear scope sections).

#### Current session (2026-05-15 — proof-fn trait methods, non-unit return, C1/C2/C5 probes, termination_by, BUG-as-nat-cast)

Multi-arc day. Started with reading DESIGN/HANDOFF, settled into
proof-fn trait method work, then closed several follow-ups.

**Proof-fn trait methods — LANDED.** `trait_to_ast` now mode-
dispatches on method kind. For `Mode::Proof`, the class method
emits as a **Prop-typed class field** (Mathlib's
`mul_assoc`/`one_mul` idiom):

```lean
class HasZero (Self : Type) where
  val : Self → Int
  val_is_zero : ∀ (self : Self), val self = 0   -- Prop field
```

Instance bodies provide a tactic proof; the caller accesses the
lemma via typeclass dispatch (`have _ := HasZero.val_is_zero t`).

Three pieces: `proof_fn_method_type` builds
`∀ (params...) (req_hyps...), <ensures>` for unit-return; for
non-unit-return uses `∀ (params...), { r : RetTy // <ensures> }`
(structured `ExprNode::Subtype { name, ty, pred }` AST node).
`strip_class_qualifier` walks the rendered LExpr via
`map_children`, replacing `ClassName.method` references with the
unqualified sibling (Lean rejects class-method refs inside the
class declaration itself; Mathlib uniformly uses unqualified).
`render_by_block` handles tactic body indentation for inline
`by` blocks (re-indents every line by 2 spaces past `by`'s
column).

Plumbing: `tactic_bodies: HashMap<Fun, String>` built once in
`verifier.rs` via `build_tactic_bodies_map`, threaded through
`check_proof_fn` / `check_exec_fn` → `krate_preamble` →
`trait_to_ast` / `trait_impl_to_ast`. Five signature additions,
one helper. Class ordering split-by-mode: classes WITHOUT proof-
fn methods emit before spec fns (old behavior), classes WITH
proof-fn methods emit after spec fns (their Prop-typed fields
can reference free-standing spec fns).

**Coverage shapes C1/C2/C5.** Additional probes for
mixed-mode trait (C1), extends super-trait (C2), and empty trait
(C5). C1 surfaced a real bug: unit-return proof-fn ensures
weren't walked by `dep_order::seed_impl_proof_method_bodies` —
fixed by always walking ensures (body walked only for non-unit
return). C2 surfaced TWO bugs: parent class bound rendered as
`[Super Self%]` (fixed via `class_bounds_to_ast` helper);
parent trait didn't transitively reach `refs.traits` (fixed via
fixed-point closure in `generate.rs`). The "extends" case in C2
exercised the full transitive-reachability story. C5 (empty
trait) passed first try.

**Non-unit return proof-fn trait methods — LANDED.** Subtype
rendering: `proof fn extract() -> (r: int) ensures r == E`
becomes class field `∀ params, { r : int // ensures }`. Instance
body emits as `fun (params...) => ⟨vir_expr_to_ast(body), by first
| rfl | simp_all⟩` — the impl's body expression IS the witness;
rfl/simp_all closes the equality with the ensures' RHS.

Two constraints + resolutions:
1. Verus's `by { }` body syntax doesn't fit non-unit returns —
   FileLoader sanitizes brace body to spaces, type mismatch with
   non-unit return type. Non-unit return proof fns use regular
   Verus-style bodies (just an expression).
2. Inside instance bodies, sibling field refs aren't in scope —
   verified directly in Lean via `/tmp/test_instance_self_ref.lean`.
   `dep_order::seed_impl_proof_method_bodies` pre-seeds all impl
   proof-fn bodies (non-unit return) so the spec methods they call
   emit as standalone defs in the preamble. Over-emit is harmless
   (inert dead code).

**Lens 4-15 audit cleanup pass.** Comprehensive review pass
applied lens 4-15 to the proof-fn trait method work. Findings
included: stale comments, an opportunity to clean up
`strip_class_qualifier` (used `map_children` traversal — clean
delegation), surfacing that the suffix-strip approach for "Self%"
was wrong (DESIGN-relevant). Replaced with
`vir::def::trait_self_type_param()` — Verus's documented public
API constant. The fix lives in `typ_maybe_projection_to_expr`'s
exact-match check.

**Termination_by for recursive proof fns — LANDED (Case 11 part 1).**
`Theorem` AST gains `termination_by: Vec<Expr>` field;
`proof_fn_to_ast` populates from `f.decrease` (mirroring
`spec_fn_to_ast`); pp emits `termination_by <expr>` after the
tactic body (or `(e1, e2, ...)` for lex). Verus's `decreases n`
on a recursive proof fn flows through as faithful translation —
Verus has already certified termination, we pass the measure to
Lean. Lean often auto-infers for simple structural cases, but
the explicit clause is required for Collatz-shape or non-obvious
measures. Pinned by `test_proof_fn_with_decreases_noncrecursive`
and `test_proof_fn_recursive_with_decreases`; 3 pp unit tests.

**Recursive proof-fn TRAIT methods still deferred** (Case 11
part 2): class fields in Lean don't accept `termination_by`
directly (verified 2026-05-15 via Lean test file). Fix involves
either rendering recursive proof-fn trait methods through
`mutual` blocks with WF measures, or emitting them as top-level
theorems (loses typeclass-dispatch property). Flagged.

**BUG-as-nat-cast.md fix — LANDED.** Verus's `fn_call_to_vir.rs`
drops `U(_) → Nat` and `USize → Nat` casts as no-ops (sound for
Z3 which treats both as Int with refinements; unsound for Lean
which has distinct Int/Nat types). Pre-fix, `f(i as nat)` for
`i : u64` lowered to `f i` where `i : Int` — failed Lean
elaboration.

Fix is a Tactus-side normalization pass:
`insert_nat_coercions_in_{exp,stm,expr}` walks SST/VIR-AST at fn
entry, looks up each Call's callee in fn_map, and wraps args
whose Lean type renders as Int (when the corresponding param
renders as Nat) in synthetic `Clip { range: Nat }`. The
renderer's existing Clip handler emits `Int.toNat`. Same
architectural pattern as #94 `rewrite_varat_for_mut_params`,
#95 `normalize_mut_ref`, #127's `original_cond` recovery.

Always-emitting Clip at Verus's cast lowering would break 7
vstd lemmas in `vstd/bits.rs` (calc-style proofs relying on Z3
silently equating `x` and `clip(Nat, x)` for u-typed x). The
pre-pass runs only on Tactus-bound code so vstd stays
untouched and verifies 1530/0 under Z3.

`needs_nat_coercion` peels `Boxed`/`Decorate` via
`peel_typ_wrappers` (SST args often arrive as
`Boxed(Int(U(64)))` from Verus's poly encoding pass). Pre-pass
fires at: exec body + ens_exps + reqs (SST); proof fn require
+ ensure + decrease (VIR-AST); spec fn body + termination_by
(VIR-AST). 5 e2e regression tests:
`test_proof_fn_u64_as_nat_in_ensures` (minimal reproducer);
`test_proof_fn_u_types_as_nat` (all u-types coerce);
`test_proof_fn_both_sides_as_nat` (both sides of ==);
`test_exec_assert_u64_as_nat` (SST path);
`test_exec_loop_invariant_u64_as_nat` (loop invariant).

**Net for the day**: ~10 commits, 9 deferrals closed (Prop-typed
class fields, non-unit return proof-fn trait methods,
`ExprNode::Subtype` variant, C1/C2/C5 coverage shapes,
`termination_by` for proof fns, the as-nat-cast bug). Test
counts 388 → 412 e2e (+24), unit tests 182 → 195 (+13).
DESIGN.md got new sections: "Trait class and instance emission",
"External-body type opaque emission", "U → Nat coercion at Call
sites", "Trait class+instance emission: deferred edges". The
nat-coercion pre-pass adds ~250 lines to `sst_to_lean.rs`.

#### Current session (2026-05-16 — DESIGN-cast-hygiene.md)

After the BUG-as-nat-cast fix surfaced a "paper cut" — chains of
`Int.toNat` operations in goals that trip omega — explored three
options for the underlying rendering choice without committing:

- **Option A**: Cast hygiene lemmas in TactusPrelude.lean + a
  named simp-set rung in `tactus_auto`. ~1-2 days. Reversible.
- **Option B**: Render Verus `nat` as Lean `Int` with bound
  hypothesis (mirroring how u-types already work). ~1-2 weeks.
  Closes USize subtraction soundness gap as a side effect.
  Deletes the nat-coercion pre-pass.
- **Option C**: Emit spec fns as `opaque + axiom` (mirror
  Verus's Z3 encoding directly). ~1 week. Diverges from standard
  Lean `unfold` idioms.

Doc lives at `DESIGN-cast-hygiene.md` alongside DESIGN.md and
HANDOFF.md. Non-committal — design exploration with comparison
table, open questions, and decision criteria framed by audience
and priorities. Three real options, each with substrate-vs-user
complexity trade-offs. The conversation surfaced that Z3 has
**none** of the relevant costs because Z3's model is
fundamentally different (untyped Int + axiomatic spec fns); each
of A/B/C absorbs Z3's "untyped" model into Lean's typed model
at a different layer.

#### Current session (2026-05-17 — warnings cleanup, trait probes, catalogue sweep)

Small bits day. Closed five maintenance items.

**Warning cleanup**: two pre-existing unused `spec_callee`
parameter warnings in `sst_to_lean.rs` (at `emit_call_precondition_theorem`
and `push_post_call_frames`). The parameter was passed by callers
but the body referenced it only in comments; dropped from both
signatures (one call site each, mechanical). Clean compile, no
warnings.

**vstd Nat-pattern probe** (open question #2 from DESIGN-cast-
hygiene.md): grepped vstd for `Nat.succ`, `match n : Nat with`,
and recursive nat-typed spec fns. **Audit cost for Option B is
LOW**: zero `Nat.succ` uses anywhere; the only directly-recursive
nat-typed spec fn is `arithmetic/power.rs`'s `pow(b: int, e: nat)
-> int`, whose body uses generic operators (`==`, `-`, `*`, `if`)
only. Result fed back into DESIGN-cast-hygiene.md.

**Trait emission edge probes** (DESIGN.md "Trait class+instance
emission: deferred edges"):
- `test_trait_generic_impl_probe` — ✅ pinned. `impl<T> Container
  for Wrap<T>` with concrete `Wrap<u8>` reaches the gate via
  short_name (`Wrap`) correctly.
- `test_trait_assoc_typed_default_probe` — ✅ pinned. Default
  method returning `Self::Output` renders cleanly via
  `typ_maybe_projection_to_expr`'s bare-`Output` translation.
- `test_trait_recursive_default_upstream_blocked` — Err pin.
  Verus rejects recursive default bodies with "trait default
  methods do not yet support recursion and decreases". The
  Tactus-side `termination_by` question stays untested
  (unreachable through normal Tactus paths today).

DESIGN.md updated: three edges flipped from "untested" to
either ✅ pinned or upstream-blocked.

**Catalogue staleness sweep**: flipped the proof-fn-trait-method
catalogue entry (line 1391) from "UNTESTED, likely needs
separate handling" to "✅ LANDED 2026-05-15" with cross-reference
to the new "Trait class and instance emission" section.
Cross-referenced DESIGN-cast-hygiene.md from the USize
subtraction trade-off note (the cast-hygiene options B/C close
the USize gap as a side effect).

**Net for the day**: warnings cleared; 3 new e2e tests
(412 → 415); DESIGN.md catalogue refreshed; DESIGN-cast-
hygiene.md updated with the vstd probe finding. No code changes
beyond the warnings cleanup.

#### Current session (2026-05-17 continued — BUG-exec-fn-imports.md fix, two bugs)

Downstream tutorial work hit a gating issue: Mathlib tactics
(`nlinarith`, `ring`, `linarith`, etc.) raised "unknown tactic"
inside `assert(P) by { ... }` blocks in `tactus_auto` exec fns,
even when the user wrote `import Mathlib.Tactic.X` at file top.
Root-causing surfaced TWO distinct bugs (the user's report only
captured the symptom of one).

**Bug 1 — syntax.rs attribute attachment.** Pre-fix,
`builtin_macros/src/syntax.rs:4807` attached `lean_import` attrs
only to fns with `tactic_by` (proof fns). Exec fns marked
`#[verifier::tactus_auto]` got nothing. So even when the file's
tactic bodies were sanitized correctly, the generated `.lean`
file for an exec fn theorem didn't include the user's imports,
and Lean rejected unknown tactics. **Fix**: also attach when the
fn has `verifier::tactus_auto` attr (either `verifier::tactus_auto`
or `verifier(tactus_auto)` shape), mirroring how `is_external`
detects the equivalent attr.

**Bug 2 — tree-sitter-tactus grammar.** Surfaced by writing a
regression test for bug 1: rustc rejected with E0425 "cannot
find value `nlinarith`" BEFORE Lean even ran. Probing with
`TACTUS_FILE_LOADER_DEBUG` showed `find_tactic_block_ranges`
returned `[]` for files containing `import` lines but `[(478, 489)]`
for the same file without import. Root cause: tree-sitter-tactus
had no grammar rule for `import Foo.Bar.Baz` declarations.
tree-sitter's error recovery from raw-Rust parse of the `import`
line lost track of downstream `assert_expression` /
`proof_block` brace bodies inside exec fn bodies. FileLoader saw
no tactic blocks to sanitize.

The reporter's environment apparently didn't surface bug 2 (their
reproducer had both a proof fn AND exec fn — the proof fn's
signature-level `by { }` survives the broken parse, perhaps
because it appears earlier in the parse tree before recovery
truncates). Our single-fn test triggered it reliably.

**Fix (bug 2)**: in `tree-sitter-tactus` submodule:
- Added `'import'` to the keyword list in the token_tree special tokens.
- Added `import_declaration: 'import' Ident('.' Ident)*` rule
  matching verus_syn's parser at `syntax.rs:4485-4505` (no
  semicolon terminator; rule ends when next dotted segment fails).
- Added `$.import_declaration` to `_declaration_statement` choice
  so it's reachable inside `verus! { ... }` macro body parsed as
  statements (line 1135's `repeat($._statement)`).
- Regenerated `parser.c`, `grammar.json`, `node-types.json`.
- 3 new corpus tests pin the rule.

**Discipline note worth recording: root-causing matters.** Initial
instinct was to land bug 1's fix (the user's symptom) and call it
done. The regression test surfaced bug 2 in a way that LOOKED
like a workaround need ("the FileLoader needs to handle imports
specially"). The user's pushback — *"this all seems a lil sussy,
have we root caused the issue?"* — caught the temptation to
patch over a real grammar gap. Tracing FileLoader's tree-sitter
output via env-var debug revealed the two-bug structure cleanly.
The right fix was in the grammar, not in the FileLoader.

**Pinned tests**:
- `test_exec_fn_import_threaded_smoke` (Err pattern, without
  import) — confirms FileLoader sanitization works in the
  baseline case; the rustc-vs-Lean-failure distinction surfaces
  bug 2 cleanly when imports are present.
- `test_exec_fn_import_threaded` (Ok, with import) — confirms
  both bugs are fixed end-to-end; `nlinarith` resolves via the
  imported `Mathlib.Tactic.Linarith`.

**Submodule pointer bumped** in the parent repo's commit.

**Net**: 415 → 417 e2e (+2), 195 unit, 199 → 202 tree-sitter (+3
grammar tests), vstd 1530/0. Two commits: tree-sitter submodule
(grammar + parser regen + corpus tests) and parent (syntax.rs
fix + submodule pointer + e2e regressions).

The downstream tutorial chapter 4 (iterative factorial against
recursive spec) — and any other realistic exec verification
needing nonlinear arithmetic — is now unblocked.

#### Current session (2026-05-17 continued — nlinarith folklore)

After the import fix landed, downstream user surfaced a tactic-
intro asymmetry worth recording as folklore (no code change).

**The observation**: `assert(P) by { nlinarith }` fails against
Tactus's open-form goals (`∀ binders, hyps → goal`) because
`nlinarith` doesn't auto-intro the way `omega` does. Users have
to write `intros; nlinarith` to peel the binders first.

**Not a Tactus bug.** This is intentional Lean / Mathlib design.
`omega` is the OUTLIER in being intro-aware; most Mathlib tactics
(`nlinarith`, `linarith`, `ring`, `polyrith`, `positivity`,
`field_simp`) operate on the current goal state and expect the
caller to have manipulated it into flat form. Tactus's emission
is correct — we produce standard open-form theorems.

**Possible fix: `tactus_auto` rung for `intros; nlinarith`.**
Considered and deferred. The `intros;` prefix would be purely
structural (peeling Tactus's own emission shape), substrate-class
like cast hygiene. But: `nlinarith` can be slow on goals where
it doesn't apply (Positivstellensatz search), requires Mathlib
imported, and the principle of minimal automation pushes against
default ladder extensions. A conditional rung based on file-level
Mathlib import (mirroring BitVec preamble fragments) is a real
option but worth doing deliberately, not as a quick patch.

**Recommended pattern: body-assert.** Move the nonlinear step
inside the body at its point of friction:

```rust
while i < n
    invariant 2 * result == i * (i + 1), ...
    decreases n - i
{
    i = i + 1;
    result = result + i;
    assert(2 * result == i * (i + 1)) by { intros; nlinarith };
}
```

The assert's OWN obligation is the nonlinear identity (`intros;
nlinarith` discharges it); the asserted hypothesis enters scope
for the maintain check, which closes trivially via `simp_all`.
Same pattern as the spec-fn-unfold body-assert documented under
"Tactic / automation limitations" → "Spec fn calls in goal
position need explicit unfolding." One pattern, two surfaces.

**Discipline note worth recording**: the body-assert pattern is
emerging as the canonical "this obligation needs a specific
tactic" answer in Tactus. It scales better than per-fn
`tactus_tactic` overrides (which apply to ALL theorems the fn
emits, not just the hard one) and stays Lean-idiomatic.
DESIGN.md updated with the nlinarith folklore note + cross-
reference to body-assert.

#### Current session (2026-05-17 continued — BUG-fileloader-by-in-comment.md fix)

Downstream user surfaced a three-condition trigger that caused
FileLoader to silently fail to sanitize tactic bodies:
1. A prior `by { ... }` block in the file
2. A `//` comment whose tail is the `by` keyword
3. The next line a `//` comment whose head is `{`

Symptom: tactic names like `intros`, `nlinarith` reached rustc as
identifier references, triggering E0425.

The bug report hypothesized a "Phase 1 / Phase 2 scanner state
leak" but Tactus's FileLoader uses tree-sitter, not a hand-written
scanner. The actual root cause turned out to be in tree-sitter's
GLR conflict resolution.

**The root cause (genuinely):** the grammar declared an explicit
conflict `[$._statement, $.function_item]` between two valid parses
of `#[attr]\nfn f(){}`:
- standalone `attribute_item` followed by sibling `function_item`
- nested: `function_item` containing `attribute_item` as a child

Tree-sitter picked between them based on parse context. In most
files it picked the nested form. But specifically when a
`tactic_block` (proof fn `by { }` body) appeared earlier, plus
`line_comment` extras intervened between the tactic_block and the
next attribute, tree-sitter flipped to the standalone-sibling
parse. FileLoader's `function_has_tactus_auto_attr` walks the
function_item's CHILDREN looking for the attribute; with the
attribute as a sibling, the check returned false, and
`collect_inner_lean_blocks` never ran on the fn's body.

**Debugging discipline note**: the user pushed back twice on
patch-first approaches (once with "have we root caused?", once
asking for a grammar fix not a FileLoader workaround). Both
pushes were correct — the first surfaced that there was a real
parse issue (not just a FileLoader bug to paper over); the second
forced the fix at the right layer. A unit test diagnostic
(`diagnose_function_items_*`, dumping function_item parse output
for working vs failing cases) cleanly showed the structural
difference (attribute as child vs sibling) and made the grammar
locus visible.

**Fix**: `prec.dynamic(-1, $.attribute_item)` in
`_declaration_statement`'s choice deprioritizes the standalone-
sibling parse without removing it (some unrelated corpus tests
legitimately use it — removing it broke "Attributes" and "Derive
macro helper attributes" tests). Matches Rust semantics: outer
attributes always attach to a following item; the standalone form
is only a tree-sitter GLR fallback.

**Probe path that worked (false starts catalogued)**:
1. Initial instinct: workaround in FileLoader (`mask_import_lines`-
   style). User pushed back. Reverted.
2. Grammar fix attempt 1: remove `$.attribute_item` from
   `_declaration_statement` entirely. Broke 2 corpus tests.
   Reverted.
3. Grammar fix attempt 2: `prec.dynamic(1, ...)` on `function_item`
   to prefer nested. Didn't bias enough. Reverted.
4. Grammar fix attempt 3: `prec.dynamic(-1, $.attribute_item)` in
   `_declaration_statement` to deprioritize standalone. **Worked.**
   All 203 tree-sitter tests + 418 e2e + 195 unit pass.

**Submodule + parent commits**:
- `5a85969` (submodule): grammar fix + corpus regression test.
- `835746c` (parent): submodule pointer + unit + e2e regression.

**Net**: 417 → 418 e2e (+1), 195 unit, 202 → 203 tree-sitter (+1),
vstd 1530/0.

Bug doc removed.

#### Current session (2026-05-17 continued — View trait emission cluster + loop-local fixes)

Long sprint. After yesterday's #106 catalogue audit (mixed-paths
turned out to be already-done, `c6865c6`), probed `&mut v[i]`
(`43383f4`) which revealed the catalogue's "needs different rebind
encoding" claim was wrong — Verus's `vec_index_mut` desugar makes
the &mut arg Var-shaped and `Seq::update` captures the "j ≠ i
unchanged" property structurally. The real blockers are a cluster
of four bugs in cross-crate trait emission (A/B/C/D) plus
substitution. Closed three of four, plus two adjacent bugs found
while in the neighbourhood.

**Bug A: class-qualified trait method calls + standalone-def
helper pattern** (`6c278f7`). Pre-fix, goals mixed `view.View.view`
(class-qualified, 3-segment) and `view.view` (bare path, 2-segment)
for the same conceptual call, depending on rendering path
(`DynamicResolved` rendered bare via `lean_name(&resolved.path)`).
Made `call_to_node` in `to_lean_expr.rs` route both `Dynamic` and
`DynamicResolved` through `trait_method_ref(fun)` — always
class-qualified, takes Self via auto-binding. Then added TypeAnnot
wrap for generic disambiguation (gated on `typ_contains_param` so
`Self%` doesn't leak into wraps inside class declarations). The
"duplicate emission" question: my first instinct was to call it a
code smell and remove the standalone-def emission, but Danielle
pushed back ("do u think this is correct?"). Verified directly with
Lean probes that both bare `target` and `Class.target self` inside
an `instance` `where`-block fail (Lean's "instances are not
available for instance synthesis during their own definitions" —
[reference manual § "Instance Declarations"](https://lean-lang.org/doc/reference/latest/Type-Classes/Instance-Declarations/)).
The duplicate IS the canonical Lean idiom: helper-in-namespace +
thin-instance. Added `strip_class_qualifier` to instance method
bodies so sibling refs resolve to standalone defs. Test rewrites:
18 tests now use `unfold Trait.method` style. Net 419 / 419 e2e.

**Bug C: synthesized body for uninterp impl methods** (`9f77305`).
When an impl method has `body = None` (Verus's `uninterp`), the
standalone def gets emitted as an axiom by `spec_fn_to_ast`, but
`trait_impl_to_ast`'s `func.body.as_ref()?` filter dropped the
method from the Instance entirely, leaving a body-less instance.
Lean rejects. Fix: synthesize a body that dispatches to the
standalone axiom via `<standalone> typ_args... params...`. Pinned
by `test_uninterp_impl_method_body_less_instance_probe`. Net 420 /
420 e2e.

**Bug D (partial): MutRefCurrent / MutRefFuture in caller-side
ensures inlining** (`42228d9`). When a callee's ensures references
BOTH `*old(x)` and `*final(x)` (vstd's `vec_index_mut` shape), the
VIR-AST renderer's catch-all `Unary(_, inner) => expr_to_node(inner)`
arm aliased both to bare `Var(p)`, and `ens_subst` mapped that to
the fresh post-state — pre-state distinction lost. Fix in
`rewrite_varat_for_mut_params`: rewrite `MutRefCurrent(Var(p))` →
`Var(<p>_at_pre_tactus)` and `MutRefFuture(Var(p))` / `MutRefFinal(_,
Var(p))` → `Var(p)`. Pinned by
`test_new_mut_ref_pre_post_substitution_probe` (same-crate). Net
422 / 422 e2e.

**BUG-loop-local-names-alpha-renamed: extract leading binders to
theorem-level** (`18d8277`). Loop-local `i` inside an `assert(P)
by { ... }` was inaccessible to user tactics — Lean's `intros`
auto-disambiguates to `i✝¹` when the outer `let i := 0` (from
`let mut i = 0`) is in scope, and user-source `i` resolved to the
let-bound `0`, not the loop iteration value. Two fixes:
(a) `push_mod_var_frames` drops Let frames for modified-var names
(initial-value lets are irrelevant for maintain/use obligations);
(b) `OblCtx::split_leading_binders` extracts leading Binder + Hyp
frames to theorem-level binders. User writes `have h : i + 1 ≤ 101
:= by omega` directly. Net 421 / 421 e2e.

**BUG-multi-var-loop-alpha-rename: inject explicit-named intros
when extraction blocks** (`465a7ed`). The previous fix worked for
single-var loops but multi-var loops (with an outer non-modified
`let a := 0`) blocked extraction — Let(a) became the leading frame,
`split_leading_binders` stopped immediately. Fix in
`emit_with_closer` (the user-tactic emission path): if any frames
remain after extraction, inject `intro <names>;` before the user's
tactic. Names come from frame types — Let / Binder contribute
their source name; Hyp contributes `_`. Layered cleanly on the
extraction logic — same architectural shape as 18d8277 but with
injection as fallback for the cases extraction couldn't reach.
Pinned by `test_multi_var_loop_assert_by_probe`. Net 423 / 423 e2e.

**Discipline note: I almost shipped a wrong inversion.** Twice
during the day I called something a code smell when it was actually
the canonical pattern. The duplicate emission (Bug A
investigation). The "loop-local fix is complete" framing (one
session before the multi-var case surfaced). Each time the
user-supplied bug report or the user-asked question revised the
position. The pattern names something I want to remember: confident
abstract reasoning needs concrete verification — direct Lean
probes, Lean reference manual checks, or downstream user-supplied
probes — before being committed to.

**Doc updates**: DESIGN.md "Trait class and instance emission"
section grew the call-rendering / TypeAnnot-wrap / duplicate-
emission-is-canonical / strip-in-instance-bodies / user-side-
unfold paragraphs plus citation links to the Lean reference manual.
Cross-references added in DESIGN.md for the &mut v[i] probe's
catalogue correction (`43383f4`'s commit message).

**Today's commits in chronological order**: `c6865c6` (mixed-paths
catalogue refresh) → `bd902ae` (poems: catalogue / have we) →
`43383f4` (Vec[i] probe + catalogue correction) → `0946e45` (WIP)
→ `6c278f7` (Bug A) → `5af4000` (poems: Mathlib / what looked like
a smell) → `9f77305` (Bug C) → `18d8277` (loop-local) → `70038c8`
(poems: the work was nearby / what the probe showed) → `42228d9`
(Bug D partial) → `465a7ed` (multi-var loop).

**Remaining View trait cluster work** (for a future session):

* **Bug B: `view.View.V A` blanket-impl rendering**. vstd has
  several `View` blanket impls (`&A`, `Box<A>`, `Rc<A>`, `Arc<A>`)
  each with `type V = A::V`. Tactus renders `<A as View>::V` as
  `view.View.V A` in `typ_to_expr`'s Projection arm — but `V` is a
  class type-param, not a field accessor, so `view.View.V` is
  malformed. The canonical Lean idiom is to bind `V` as a fresh
  implicit on the blanket impl's instance signature
  (`{V : Type} [View A V] : View (Ref A) V`), not as an accessor.
  `trait_impl_to_ast` would need to introduce fresh type-param
  binders for trait bounds involving assoc types. Bigger refactor
  — not a `typ_to_expr`-only fix. Pinned (alongside the rest of
  the cluster) by `test_exec_call_mut_arg_vec_index_probe`'s Err.
* ~~**Bug D remaining piece: vstd-specific `old(vec)@` shape.**~~
  **CLOSED 2026-05-18** — the actual issue was SST-side trait-method
  rendering, not a missed VIR-AST construct in
  `rewrite_varat_for_mut_params`. See the 2026-05-18 session entry
  below for the real diagnosis and fix.

Both are well-scoped for future sessions. The same-crate version
of Bug D works now (`test_new_mut_ref_pre_post_substitution_probe`),
so the architectural direction is validated.

#### Current session (2026-05-17 continued — review pass + helper-proof-fn WIP)

**Review pass** (`7db0654`): ran the DESIGN.md "Code review strategy"
5 lenses over today's diff. Findings:
- **Dead code**: `call_to_node`'s inner `Dynamic | DynamicResolved`
  arm became unreachable after `6c278f7`'s outer dispatch refactor.
  Removed plus its misleading deferred-@-prefix comment.
- **Dead method**: `ObligationEmitter::emit` had no callers after
  the `emit_split` / `emit_with_closer` / `emit_with_extras`
  refactor. Removed (was producing dead_code warning).
- **Orphaned docs**: my refactor of emit_split / emit_with_closer
  left `emit_with_preamble`'s original doc in a stale position.
  Reorganized so each emit method has a clear doc.
- **Coverage gap**: Bug C synth path with typ_params was only
  exercised by the Err-pinned Vec[i] case. Added
  `test_uninterp_impl_method_with_type_params_probe` (same-crate,
  pinned Err for a different downstream issue but verifies the
  synth shape is correct).
- **Upstream-brittleness**: added DESIGN.md "Verus-side invariants
  we depend on" entry for `UnaryOp::MutRefCurrent/Future/Final`
  variants matched by `42228d9`'s rewrite.

Net: 423 → 424 e2e (+1 probe), no regressions.

#### Current session (2026-05-17 continued — helper proof fn + impl-method disambiguation, WIP)

**BUG-no-helper-proof-fn-call-from-exec.md** surfaced the gating
limitation for the headline "verify iterative Rust against
recursive math spec" use case: helper proof fns (e.g., `fib_recurrence`,
`fact_monotone`) aren't callable from exec fn `proof { }` blocks
because Tactus emits each proof fn into its own Lean file and exec
fn files don't include them.

**Fix in progress** (`5cb4a75`): two interlocking pieces.

*Helper proof fn emission.* `krate_preamble` now computes
`helpers_to_emit` (all non-root, non-trait-method proof fns with
tactic bodies) and:
1. Extends `dep_walk_roots` to include them, so their transitive
   spec-fn / datatype / trait refs land in the preamble alongside
   the root fn's.
2. Emits their full `theorem ... := by ...` declarations after
   spec fns.

Helpers emit in both ExecFn AND ProofFn contexts — the bug report
flagged proof→proof as lower-severity but the architectural fix
covers it naturally.

Pinned by `test_helper_proof_fn_call_from_exec_probe`.

*Impl-method name disambiguation.* The widened dep walk surfaced a
pre-existing name collision in standalone-def emission. Pre-fix
`lean_name` filtered out synthetic impl segments (`impl&%0`) — fine
when the dep walk only pulled one impl per file but broken now
that helpers may pull in additional impls. Both `MyInt::is_zero`
and `MyNat::is_zero` collapsed to `is_zero` → "already declared".

Fix: `lean_name` keeps the impl segments (sanitized as `impl__0`,
`impl__1`); `sanitize` extended to also replace `&` (the impl
marker syntax is `impl&%N`); `strip_class_qualifier` takes an
`impl_prefix` arg and produces `<impl_prefix>.<method>` for sibling
refs inside instance bodies (matching the disambiguated standalone
name) while class declarations still pass empty prefix → bare-name
rewrite.

**Completed in `6a936eb`**: 425 / 425 e2e tests pass, vstd 1530/0.
The remaining 7 fails after the WIP commit were a single ordering
bug — helpers were emitted between spec fns and classes, but
helpers may use typeclass dispatch which needs instances declared
first. Moving helper emission to AFTER instances fixed 6 of 7.
The last (`test_uninterp_impl_method_body_less_instance_probe`)
was an inconsistency between `lean_name` (which I'd updated to
keep impl segments) and `LeanName::from_path` (a duplicate in
lean_name.rs that still filtered — Bug C's synth body used
from_path and emitted at the bare name). Updated from_path
consistently; also extended `sanitize` in BOTH copies
(to_lean_type.rs and lean_name.rs) to replace `&` along with
`@ # %`.

Discipline note worth recording: I was zig-zagging earlier on
this fix — first attempted a global lean_name change (24 fails),
then a parallel "lean_name_keep_impl_segments" fn (hacky two-fn
approach), and the user pushed back with "what happened to our
planned approach? This seems hacky." The right plan was the
ORIGINAL one: single consistent `lean_name`, propagate the change
through all consumers. Sticking to it required also fixing
strip_class_qualifier and sanitize. Plus catching the duplicate
filter in `LeanName::from_path` (different file, same logic — the
type of thing the typed-invariant pattern would prevent if there
were a single source of truth for path → lean name conversion).
The hedging cost time and muddied the architecture; the user's
correction was right.

**Two duplicated bits of logic discovered along the way** (not
fixed, flagged for future):
* `lean_name` (to_lean_type.rs) and `LeanName::from_path`
  (lean_name.rs) both convert VIR paths to Lean dotted names. They
  had identical (now-changed) impl-segment filtering. Updating one
  required updating the other. A single source of truth would
  prevent silent divergence.
* `sanitize` is duplicated between to_lean_type.rs and lean_name.rs
  with parallel `needs_sanitization` / character-replacement
  logic. Same situation — adding `&` to one required adding to the
  other. Could share one helper.

#### Current session (2026-05-19 continued — impl method rename LANDED)

The plan documented in the prior session's "Rename implementation
plan" was actually executed in the same arc, across four commits.
(Disk error wiped the conversation history; reconstructing from
git log.)

**Commits, in order:**

* `425a8f4` **WIP rename: `impl__N.method` → `<Self>.<Trait>.<method>`.**
  Standalone def emission + sibling-call rewrite now use
  `Bar.Counter.method` style. Renaming localised to
  `impl_subst.rs`:
  - `MethodContext` gained `name_prefix: Option<Vec<Ident>>`.
  - `set_method_context` pre-renames `method_redirects` Fun
    values when prefix is set.
  - `augment_function` rewrites `f.name` to the renamed Fun.
  - `to_lean_type::type_short_name` is the new helper that peels
    Decorate/Boxed and returns a String.
  - `generate.rs` computes per-impl prefix
    `[type_short_name(Self), short_name(trait_path)]`, counts
    collisions, falls back to `None` (no rename) for impls whose
    natural name would collide.

  Six existing probes failed after this commit because their
  tactic-text referenced the old `impl__N.method` form.
  Investigation continued.

* `6a105e9` **Fix: drop trait segment, fix Bug-C synth-body
  lookup.** Using `Wrap.View.view` as the path created a Lean
  namespace shadowing conflict: inside `def Wrap.View.view`'s
  body, a bare `View.view` reference resolves to the def itself
  (recursive self-ref) instead of the trait class method.
  Empirically reproduced — Bug B probes failed with
  "Application type mismatch: self.val0 of type A but expected
  Type" because Lean treated `View.view self.val0` as a call to
  `Wrap.View.view` (whose first arg is `A : Type`).

  Switched to `<Self>.<method>` (e.g., `Wrap.view`,
  `MyList.length`, `Bar.raw`). Removed the View middle segment;
  collision detection now counts `(Self, method_short)` pairs.

  Also fixed Bug C's synthesised body for body=None Spec
  methods — the forwarder was using `func.name.path` directly
  (un-renamed), so the synth produced `impl__0.shadow` while
  the standalone was at `Hidden.shadow`. Fixed by consulting
  `method_redirects` (built in `set_method_context` from the
  same `method_impls` slice, guaranteed lookup; `.expect()` not
  fallback).

* `0221629` **Re-add trait segment with `impl` marker:
  `<Self>.<Trait>.impl.<method>`.** The two-segment scheme from
  `6a105e9` lost multi-trait-same-method-name disambiguation
  (two traits with `raw` on the same Self both renamed to
  `Bar.raw`). Putting the trait segment back caused the namespace
  shadow. Resolution: **insert an `impl` marker between trait
  and method.**

  ```text
  def Wrap.View.impl.view's body looking up View.view:
  - Wrap.View.impl.View.view — not defined
  - Wrap.View.View.view — namespace `Wrap.View` exists
    (contains `impl` sub-ns) but no `view` declaration there. Skip.
  - test_crate.View.view — class method, MATCH. ✓
  ```

  Without the `impl` marker, `Wrap.View.view` (without the
  intermediate) would self-reference because Lean's namespace
  resolution searches `Wrap.View.<x>` and finds the def. The
  `impl` segment breaks that chain at exactly the right point —
  Lean doesn't auto-search across the impl marker into the
  trait's actual class methods.

  Names now disambiguate by construction:
  `Bar.Counter.impl.raw` vs `Bar.Foo.impl.raw` (two traits with
  the same method name on the same Self).

  Multi-arg trait edge case still falls back to `impl__N.method`
  (legal Rust: `impl Foo<int> for Bar` and `impl Foo<bool> for
  Bar`; both naturally map to `Bar.Foo.impl.raw` and would
  collide).

* `4c424a7` **Two-traits-same-method probe.** Added
  `test_two_traits_same_method_name_disambiguated_probe` —
  `trait Foo { raw }` + `trait Bar2 { raw }` both on `Bar`. The
  rename distinguishes via the trait segment; both impl renames
  fire without collision. Regression guard for the disambiguation
  property.

**Why this matters (user-facing UX).** Pre-rename, goal-state for
impl methods showed synthetic names like `impl__0.length` — users
had to grep generated Lean to figure out what to add to their simp
set. Post-rename, the goal shows the natural name
`MyList.Container.impl.length`. Users see what's there and can
add the right thing to their simp call.

The simp-listing requirement itself doesn't go away — DESIGN
principle #1 still applies (no silent unfolding). But the names
in the goal state are now **discoverable from the goal state**
rather than opaque-synthetic.

**Net (final commit `4c424a7`):** 434/434 e2e (+1 disambiguation
probe), 209/209 lib, vstd 1530/0.

**Reflection.** The deferral note in the prior entry estimated
"~150 lines + test verification, ballparked half a session" — that
proved roughly accurate. The unexpected part was the namespace
shadow in the first naming scheme (`Wrap.View.view`); the `impl`
marker fix took an additional round of debugging once the symptom
("self.val0 of type A but expected Type") became reproducible.
The general pattern continues: each "obvious" naming scheme
exposes a Lean elaboration constraint, and the right path is
empirical rather than purely-derived.

#### Current session (2026-05-19 continued — audit follow-up, `@[reducible]` experiment ruled out, rename deferred)

After the Bug B fix landed (commit `df01442`, see below), Danielle
asked for another audit pass focused on untested edge cases. Two
more real bugs surfaced from probe writing alone (commit
`df01442`):

* **Multi-arg trait bounds drop the fresh binder.** The first audit
  pass (commit `6a15799`, the day before) tightened
  `trait_bounds_to_ast`'s TypEquality match from "path only" to
  "path + typs structural equality". But `ImplSubst::build`
  synthesised fake `TypEquality(T, [TypParam(X)], N, fresh)` bounds
  with `typs` always of length 1, regardless of the trait's actual
  arity. For `impl<A: Converter<u8>>` the bound has typs
  `[A, u8]` (length 2) — the fake's `[A]` doesn't match under the
  tightened comparison, so the fresh binder doesn't reach the
  bracket. Generated Lean had `Converter A Int : outParam Type
  → Type` (2-arg on 3-arg class). Fix: thread each impl typ-param's
  matching bound through `param_to_bounds`, capture the bound's
  full typs, use them as the fake bound's typs.

* **Standalone def bodies use class dispatch (forward-ref).** Step
  1's `rewrite_self_sibling_calls` fired in `trait_impl_to_ast`
  (instance method body) but NOT in `spec_fn_to_ast` (standalone
  def body). The standalone is emitted BEFORE its instance, so any
  class dispatch in its body forward-references the instance and
  fails to elaborate. Bug latent until a non-blanket impl had two
  spec methods where one calls the other (e.g.,
  `impl Counter for Bar { spec fn doubled() { Counter.raw(self) *
  2 } }`). Symptom: `failed to synthesize Counter Bar`. Fix:
  moved `rewrite_self_sibling_calls` from `to_lean_fn.rs` to
  `impl_subst.rs`, added `MethodContext { trait_path,
  impl_self_typ, method_redirects }` inside `ImplSubst`, extended
  `augment_function` to rewrite the body when a method context is
  set. `generate.rs` calls `subst.set_method_context(ti,
  method_impls)` before stashing each subst. Single source of
  truth for per-impl rewrite logic.

  Two new pinned probes (`test_view_blanket_impl_multi_arg_trait_probe`,
  `test_impl_method_sibling_call_in_body_probe`) and one new unit
  test (`build_fake_bound_carries_full_typs_for_multi_arg_trait`)
  guard the regression.

Then a deeper UX issue showed up: the `impl__N.method` standalone-
def name leaks into the user-facing goal state when they
`simp_all [Trait.method]`.

**Tried: `@[reducible]` on impl method standalones.** Hypothesis:
mark forwarders transparent, simp cascades through. Result: simp
doesn't delta-reduce reducible defs absent explicit `simp [name]`
or `@[simp]` annotations. `@[reducible]` controls
elaborator/typeclass-search reducibility, not simp's normalization.
Empirically verified by running the suite both with and without
the annotation — same probe failure either way. Reverted.

**`@[simp]` would work but violates DESIGN principle #1** (adds
silent rewrite rule the user didn't ask for). Ruled out.

**Deferred plan: rename `impl__N.method` →
`<SelfTypeShortName>.<TraitShortName>.<method>`** (e.g.,
`Bar.Counter.raw`, `Wrap.View.view`). Doesn't fix the user-side
simp-listing requirement, but makes the standalone's name
**discoverable from the goal state** rather than opaque-synthetic.
Mathlib has the same ergonomic load — user lists `Foo.bar` in
simp — but the names are natural.

**LANDED 2026-05-19** in the same arc — see the next session entry
above. Final scheme is `<Self>.<Trait>.impl.<method>` (the `impl`
marker is load-bearing for Lean namespace resolution). The "naming
scheme" / "collision case" / "rename implementation plan" notes
below describe the *originally proposed* `<Self>.<Trait>.<method>`
shape, kept here for forensic context but superseded by the final
landed scheme.

**Realistic-case validation** (added 2026-05-19 after a hypothesis
that the issue might only arise in contrived probes):
`test_impl_method_realistic_is_empty_probe` exercises the textbook
`Container { length, is_empty }` pattern with `is_empty :=
length() == 0`. Hits the issue — the user's natural
`simp_all [Container.is_empty, Container.length]` stalls at
`impl__0.length { n := 0 } = 0`. They have to add `impl__0.length`
to the simp list manually. This confirms the rename is warranted
for real user-written code, not just edge probes — the issue
fires for any trait with delegating method bodies (a common Rust
API pattern: `len`/`is_empty`, `next`/`peek`, `read`/
`read_to_end`, etc.). The probe currently passes only because its
tactic explicitly lists `impl__0.length`; post-rename it'd list
`MyList.Container.length` — equally explicit but recognizable.

##### Rename implementation plan (for a future session)

**Naming scheme.** For each impl method's standalone def, derive
the path `<SelfTypeShortName>.<TraitShortName>.<MethodShortName>`:
- `SelfTypeShortName` = `short_name(ti.trait_typ_args[0].path)`
  for `Datatype` Self. For non-datatype Self (e.g., `&A` =
  `Decorate(Ref, A)`), peel one layer and recurse OR fall back to
  a synthetic prefix.
- `TraitShortName` = `short_name(&ti.trait_path)`.
- `MethodShortName` = `f.name.path.segments.last()`.

**Collision case to handle**: two impls of the same trait for the
same Self type with different trait generic args
(`impl Foo<int> for Bar` and `impl Foo<bool> for Bar` — legal
Rust). Both map to `Bar.Foo.method`. Disambiguation options:
- (a) `Bar.Foo_int.method` / `Bar.Foo_bool.method` (encode trait
  args in the trait segment). Aesthetic concern: `Foo_int_bool_...`
  for multi-arg cases.
- (b) Fall back to `impl__N.method` when the natural name would
  collide. Detect collisions by building the natural-name map and
  noting duplicates; emit `impl__N` only for those.
- (c) Append `_v<N>` suffix on the natural name for the Nth impl
  of the same `(Self, Trait)` pair.

Most likely (b) is the cleanest — keep the readable name when
unique, fall back to the disambiguator when necessary.

**Edge cases for `SelfTypeShortName`:**
- `Datatype(p, args, _)` → `short_name(p)`. (`Wrap<A>` → `Wrap`.)
- `Decorate(Ref, _, inner)` → recurse on `inner`. (`&A` → A's
  name; for blanket `&A` over typ-param the inner is TypParam.)
- `Decorate(other, _, inner)` → recurse on `inner` (Allocator
  decoration etc. is transparent for naming purposes).
- `Boxed(inner)` → recurse on `inner`. (Boxed is the SMT box,
  transparent for naming.)
- `TypParam(name)` → use the typ-param's name (e.g., `A`). Note:
  this could collide if multiple impls all use `A` — fall back
  via the collision case handler.
- `Primitive(p, _)` → some name based on the primitive (e.g.,
  `Slice`, `Array`). Tactus already renders these specially in
  `typ_to_expr`.
- `MutRef(inner)`, `PointeeMetadata(inner)` → recurse on inner.
- Other variants — fall back to `impl__N`.

The helper would live alongside `short_name` in `to_lean_type.rs`
or in `impl_subst.rs`.

**Where to apply the rename**:

1. **`impl_subst::augment_function`** rewrites `f.name` to the
   natural path. The function's identity flows through unchanged
   to `spec_fn_to_ast`, which uses `lean_name(&f.name.path)` —
   that becomes the natural name automatically.

2. **`impl_subst::set_method_context`** populates
   `method_redirects` using the renamed `Fun` so the body's
   `rewrite_self_sibling_calls` swaps to the natural name in
   sibling-call rewrites.

3. **Verify: no other path consults the original
   `impl%N::method` Fun.** The original `Fun` is the FunctionX's
   `name` field, used as a key in `fn_map`, `dep_order` graphs.
   After rename, lookups by the ORIGINAL Fun won't find the
   renamed FunctionX. Need to either:
   - Keep the original Fun as the lookup key everywhere, only
     rewriting for rendering (more careful threading).
   - Or rewrite consistently across all maps (more invasive but
     uniform).

   I'd lean toward the second — rewrite consistently — by
   running `maybe_augment_impl_method` BEFORE `fn_map` and
   `dep_order` are built. The augmented FunctionX becomes the
   canonical entry.

**Naming sanity-check allowlist.** The renamed names (e.g.,
`Bar.Counter.raw`) need to be in `sanity::name_resolves`'s
allowlist OR resolve naturally via the emitted def's existence.
Currently impl method standalones resolve naturally because
`spec_fn_to_ast` emits the def with the name. Same should hold
after rename.

**Tests to update**:

- `test_impl_method_sibling_call_in_body_probe` — tactic body
  references `impl__0.raw`; update to `Bar.Counter.raw`.
- The `impl_subst::tests::*` unit tests asserting specific names
  like `_tactus_assoc_A_View_V` — those are for fresh-binder
  names, unrelated to impl method names, so should be unaffected.
- Any test that grep-able by goal-state assertion against
  `impl__N.method` — should be none currently but worth checking.

**Risk surface**:

- Name collisions across impls (handled by the collision-case
  scheme).
- Path uniqueness in `fn_map` / `dep_order` — confirm renamed Fun
  doesn't clash with anything else.
- Lean parser may reject some name shapes (e.g., names starting
  with a digit, names containing reserved characters). Likely
  fine since we're using sanitised type/trait names.

**Estimated cost**: ~150 lines + test verification. Ballparked
half a session.

**Probes to add as regression guards** (after rename lands):
- A test whose tactic does NOT use `impl__N` in its simp set,
  using the natural name instead — pinning the readability win.
- A multi-impl-same-trait probe to exercise collision handling.

#### Current session (2026-05-19 — Bug B step 2: per-impl projection substitution)

**Bug B is CLOSED.** `test_view_blanket_impl_probe` flips from
`Err(_)` to `Ok(())`. Step 1 (VIR-level type-aware sibling rewrite,
committed `bbadec0`) plus step 2 (per-impl projection subst, this
session) form the full fix.

**Step 2 mechanism.** New module `impl_subst.rs` (~250 lines):

```rust
struct ImplSubst {
    fresh_binders: Vec<Ident>,           // ["_tactus_assoc_A_V"]
    fake_bounds: Vec<GenericBound>,      // TypEquality(View, [A], V, TypParam("_tactus_assoc_A_V"))
    proj_map: HashMap<(Ident, Path, Ident), Ident>,
}

impl ImplSubst {
    fn build(impl_typ_params, impl_typ_bounds, typs_iter) -> Self;
    fn rewrite_typ(&self, typ: &Typ) -> Typ;
    fn augment_function(&self, f: &FunctionX) -> FunctionX;
}
```

The "fake TypEquality bound" insight is the key reuse:
`trait_bounds_to_ast` already iterates bounds appending matching
TypEquality typs to rendered args. Synthesising a TypEquality
bound with `TypParam(fresh)` on the RHS makes the existing
renderer produce `[View A _tactus_assoc_A_V]` for free, no
changes to the bound rendering path.

**Where it plugs in.**
- `generate.rs` builds `impl_substs: HashMap<Path, ImplSubst>`
  keyed by impl_path, after `instances_to_emit`. Each subst is
  built from the union of trait_typ_args + assoc_type values +
  every method's ret/param typs.
- For impl-method standalone defs (spec_fn_to_ast call site),
  `maybe_augment_impl_method(f, &impl_substs)` returns either an
  augmented clone (typ_params extended, typ_bounds extended,
  ret/param typs rewritten) or `f.clone()` if no subst applies.
  The augmented `FunctionX` flows unchanged through
  `spec_fn_to_ast` — no changes needed there.
- `trait_impl_to_ast` takes `subst: &ImplSubst` directly. Extends
  binders with `subst.fresh_binders`, prepends `subst.fake_bounds`
  to `ti.typ_bounds` before `trait_bounds_to_ast`, rewrites
  trait_typ_args and assoc_types[i].typ via `subst.rewrite_typ`.

**Scope: signature only.** Bodies are NOT walked. The body of
`view` is `self.0.view()` which renders to `View.view self.val0`
— no projection in the rendered Lean (Lean infers V from class
dispatch via the augmented `[View A _tactus_assoc_A_V]` bracket).
This kept the rewrite localised to `impl_subst.rs` and three
existing call sites, avoiding invasive changes to
`vir_expr_to_ast` or the SST renderer.

**Generated Lean for the Wrap blanket impl:**

```lean
class View (Self : Type) (V : outParam Type) where
  view : Self → V

noncomputable def impl__0.view (A : Type) (_tactus_assoc_A_V : Type)
  [View A _tactus_assoc_A_V] (self : Wrap A) : _tactus_assoc_A_V :=
  View.view self.val0

noncomputable instance {A : Type} {_tactus_assoc_A_V : Type}
  [View A _tactus_assoc_A_V] : View (Wrap A) _tactus_assoc_A_V where
  view := fun (self : _) => View.view self.val0

noncomputable instance : View Holder Int where
  view := fun (self : _) => self.v
```

The blanket impl's instance + standalone now type-check.
`test_view_blanket_impl_probe` closes with
`simp_all [View.view]` (the user's tactic; `omega` alone can't
reduce class dispatch — see DESIGN.md "Spec fn calls in goal
position" for the canonical pattern).

**Reflection.** Yesterday's two failed attempts (V-as-field
encoding; forward-call instance bodies) ruled out the
"uniformly nice" approaches. Today's fix is targeted: the
type-aware sibling rewrite (step 1) makes
`strip_class_qualifier` only fire when correct; the per-impl
subst (step 2) injects fresh binders for assoc-type
passthrough exactly where projections appear. Both steps leave
existing non-blanket-impl behavior untouched. The "fake
TypEquality" trick is the load-bearing piece — it kept the
data flow explicit while reusing existing machinery, so no
thread_local hack and no `@[simp]`-on-standalones (the two
approaches DESIGN.md principle #1 would have blocked anyway).

Net: 428/428 e2e (probe flips to Ok), 195/195 lib, vstd 1530/0.

#### Current session (2026-05-18 continued — Bug B exploration, no fix landed)

**Outcome: pinned a same-crate probe (`test_view_blanket_impl_probe`)
as `Err(_)`, explored two encoding options, reverted to baseline with
a design sketched for the next session.** No code changes to the
emission pipeline landed.

**What I tried (and why it didn't work):**

* **V-as-field encoding.** Switched `trait_to_ast` from outParam class
  indices to structure fields (`class View (Self : Type) where V :
  Type; view : Self → V`) so `<A as View>::V` would render as a real
  Lean field accessor. The encoding parsed, but Lean's elaborator
  *doesn't reduce class field projections during typeclass search* —
  `OfNat (View.V (Wrap Holder)) 7` failed to synthesize because
  `View.V (Wrap Holder)` stayed unreduced. **outParam isn't
  decoration; it makes V available as a unification variable during
  instance search.** With V-as-field, the projection has to be
  reduced, and `noncomputable` instances don't unfold during
  typeclass resolution.

* **Forward-call instance bodies.** Changed `trait_impl_to_ast`'s Spec
  body emission from "render in place + `strip_class_qualifier`
  rewrite" to "eta-expanded forward call to the standalone def"
  (uniform with Bug C's synth body). Conceptually cleaner — it
  removes `strip_class_qualifier`'s over-eager rewrite (which mis-
  rewrites blanket impls where `View.view self.0` calls A's instance,
  not the current impl's). But it broke 5 proof-fn tests because
  their tactic bodies do `simp_all [Foo.predicate]` expecting one
  unfold to reach the impl body — with forward-call, the unfold chain
  is `Foo.predicate → impl__N.predicate → body`, two steps. simp set
  wasn't autoextended to cover the standalone. Reverted.

**Reverted state**: trait class encoding is back to outParam,
instance bodies back to `strip_class_qualifier`, dep_order Spec-mode
seeding removed. 428/428 e2e tests pass with the Bug B probe pinned
as `Err(_)`.

**Design for next session (the "fake TypEquality bound" insight):**

The cleanest path forward is a *per-impl substitution* built once
per `impl_path`, applied in two places (instance emission + impl
method standalone-def emission). Key insight: the augmented bound
shape `[View A V_a]` can be produced by *synthesizing fake
`GenericBoundX::TypEquality` entries* and letting the existing
`trait_bounds_to_ast` machinery (which already appends TypEquality
typs to matching trait bounds) handle the rendering. No new code
path in the bounds renderer.

Sketch:

```rust
struct ImplSubst {
    // Fresh implicit binders to prepend to the impl's typ_params.
    fresh_binders: Vec<Ident>,           // e.g., ["A_V"]
    // Synthesized TypEquality bounds for trait_bounds_to_ast.
    fake_bounds: Vec<GenericBound>,      // e.g., TypEquality(View, A, _, TypParam("A_V"))
    // Projection→fresh-binder substitution for typ rewriting.
    proj_map: HashMap<(Ident, Path, Ident), Ident>,
}

fn build_impl_subst(
    impl_typ_params: &[Ident],
    impl_typ_bounds: &GenericBounds,
    typs_to_walk: impl Iterator<Item = &Typ>,  // all impl signature typs
) -> ImplSubst;

fn rewrite_projections_in_typ(typ: &Typ, subst: &HashMap<...>) -> Typ;
```

Applied at:
1. **`trait_impl_to_ast`**: extend `ti.typ_params` binders with
   `subst.fresh_binders`; prepend `subst.fake_bounds` to the bound
   list passed to `trait_bounds_to_ast`; rewrite each
   `ti.trait_typ_args` and `assoc_types[i].typ` via
   `rewrite_projections_in_typ`.
2. **Impl method standalone def** (emitted via `spec_fn_to_ast` for
   TraitMethodImpl Spec fns): same — extend typ_params, prepend
   fake bounds, rewrite ret/param typs. Likely cleanest as a
   `transform_impl_method(f, subst) -> FunctionX` that clones with
   modifications, then passes through unchanged `spec_fn_to_ast`.

The subst is *fully determined* by walking impl-signature typs for
`Projection { trait_typ_args: [TypParam(X)], trait_path: T, name: N }`
where `X` is in `impl_typ_params` and there's a bound `Trait(T, [..X..])`.
Build it once at the krate level keyed by impl_path; consume in
both call sites.

**Scope concerns to mind during implementation:**

* `strip_class_qualifier` over-rewrite (the forward-call problem)
  is a separate orthogonal bug. The pre-transform doesn't touch
  instance method bodies — those keep using `strip_class_qualifier`.
  Blanket impls calling Class.method on a typ-param will still
  mis-rewrite, but the projection-rendering bug is what the test
  pin is currently about, so we'd partially fix Bug B and leave
  the body issue for separate work.

* Body-bug fix idea: rewrite Class.method calls in the impl body
  *at VIR level* (not LExpr) before vir_expr_to_ast, where the
  call's first-arg type is available. Only rewrite when the
  receiver type matches the impl's Self.

* Bug B's blast radius: only affects blanket impls (vstd `View for
  &A`/`Box<A>`/`Rc<A>`/`Arc<A>`). No current Tactus test uses
  blanket impls; the new probe is the first. If full vstd
  consumption isn't urgent, Bug B can stay pinned without
  blocking anything else.

**The reflection that mattered**: I almost reached for `thread_local`
as the subst mechanism by reflex. It would have worked, but the
subst is a *fact about the impl* — passing it explicitly keeps the
data flow visible. The "fake TypEquality" trick is what makes the
explicit-pass path tractable (otherwise threading subst through 54
typ_to_expr call sites is what pushes people toward thread_local
in the first place).

#### Current session (2026-05-18 — Bug D-remaining: SST trait-method dispatch)

**Bug D-remaining piece** (`old(s).view()` style spec calls in
`&mut` callee ensures) was NOT what I'd assumed in the prior
session. The original HANDOFF entry guessed the issue was a
"different VIR-AST construct (maybe a builtin call)" needing a
broader `rewrite_varat_for_mut_params`. Wrong guess: the
MutRefCurrent/Future rewrite caught the shape fine — `old(s)`
became `Var(s_at_pre_tactus)` correctly. The actual breakage was
in **`to_lean_sst_expr.rs`'s `ExpX::Call` arm**: it rendered
trait-method calls with the trait's Self type-arg as a *positional
value arg*, producing Lean garbage like `View.view Holder z`
(parses as `(View.view Holder) z` → `Int z` → "Function expected
at View.view ?m.33 but this term has type Int").

**Fix** (this session): mirror the proof-fn renderer's class-method
dispatch in the SST renderer. New branch in
`to_lean_sst_expr.rs:628`:

```rust
ExpX::Call(CallFun::Fun(fun, Some(_)), _typs, args) => {
    // `Some(_)` second component corresponds exactly to
    // `CallTargetKind::DynamicResolved` (see
    // `CallTargetKind::resolved` in ast_util.rs) — i.e., a
    // trait-method call that Verus resolved to an impl.
    // Render as `Trait.method (arg : Self_typ)` for Lean's
    // class dispatch; drop typs from the head.
    ...TypeAnnot wrap concrete arg types and return type...
}
```

`typ_contains_param` was moved from private to `pub(crate)` in
`to_lean_expr.rs` so the SST renderer can use the same gate as
the proof-fn path (annotate only when the type is concrete — a
`TypParam` would render as `Self%` / `T%`, sanity-rejected outside
class bodies).

**Detection signal: `CallFun::Fun(_, Some(_))`.** The
`Option<(Fun, Typs)>` second component is set iff the VIR
`CallTargetKind` was `DynamicResolved` (see `CallTargetKind::
resolved` in `ast_util.rs:694`). For `Static`, `ProofFn`,
`Dynamic`, `ExternalTraitDefault` this is `None`. So `Some(_)`
is a reliable trait-method-resolved marker in the SST. (The
`Dynamic` case — unresolved trait method decls, only reachable
cross-crate today — would still mis-render with the
None-branch's positional-typs shape, but that's already broken
under #125's cross-crate work.)

**Probe**: `test_old_view_trait_dispatch_probe` (same-crate
trait+impl+`&mut`+ensures with `old(s).view()`/`s.view()`) flips
Ok with the fix. The intermediate inherent-method probe
(`test_old_view_pre_post_substitution_probe`) was already passing —
inherent methods route through `Static`, which never had the
class-dispatch issue.

**Vstd-side probe** (`test_exec_call_mut_arg_vec_index_probe`)
remains pinned `Err(_)` — but its failure mode has narrowed: it
now fails at "Unknown identifier `View.view`", which is **Bug B
(blanket-impl rendering)**, not Bug D anymore. The View trait
class itself isn't being emitted into the test crate because
vstd's View is defined cross-crate and gets routed through Bug B's
malformed `view.View.V A` projection rendering. Confirmed
Bug D-remaining is independent of Bug B.

**Net**: 427/427 e2e tests (425 prior + 2 new probes), vstd 1530/0,
lean_verify lib 195/0. Task #172 closed.

**Reflection on the original HANDOFF guess.** The prior entry
"probably goes through a different VIR-AST construct" wasn't
falsified by code reading alone — the SST `Call` arm's flat
"typs as positional args" rendering only fails for trait methods,
which the same-crate `test_new_mut_ref_pre_post_substitution_probe`
(plain `*old(x) + 1` on a primitive) wouldn't surface. The bug
needed a trait-method spec call inside an ensures clause to
appear. The investigation pattern that worked: write the
intermediate probe (`old(s).view()` on an inherent method — passes,
ruling out the rewrite), then the next probe up (trait method —
fails with the Lean parse error), then read the generated Lean.
The "guess what AST node" approach the prior session implied
would have led me astray; the "narrow with probes, read the
emitted Lean" approach landed the fix in one iteration.

#### Current session (2026-05-19 continued — error-span UX arc: obligation-site `-->`, proof-fn body-lines, source preview swap)

User reported a workflow tax: every `tactus_auto` Lean failure
emitted a single rust_verify error attached to `fn_span`, so the
`-->` arrow always pointed at the function signature line (e.g.
`-->  file.rs:63:1`). The actual obligation location was buried
in the message body as `at file.rs:104:18:`. Their workflow was
`verus file.rs 2>&1 | head -30` → mentally extract `104:18` →
`vi file.rs +104`. Compounded across 5–10 failures per proof
iteration, real time lost.

Landed across three substantive commits + DESIGN.md
documentation. Each was scope-disciplined; pushback from user
twice caught me proposing more invasive options than needed.

**Commit 1 (`a777f9a`) — exec-fn errors point at the obligation
site.** Each Lean diagnostic gets its own rust_verify error with
the obligation's `vir::messages::Span` as the primary span;
rustc renders standard per-error `-->` line:col at the failing
assert/invariant/call. Plumbing:
* `ExprNode::SpanMark` and `SpanMarkLandmark` grow
  `rust_span: Option<vir::messages::Span>` alongside the existing
  string `loc`. The ~10 construction sites in `sst_to_lean.rs`
  already had the obligation Span in hand (`&ens.span`,
  `&inv.span`, `&call_span`, etc.); just clone-through.
* `format_error` returns `FormattedDiag { message, rust_span }`
  instead of just `String`.
* `CheckResult::Failed` carries `Vec<TactusDiag>` (one per
  failing obligation) instead of a single concatenated
  `error: String`.
* `verifier.rs` gets `emit_tactus_diag` helper that reports one
  `MessageLevel::Error` per diag, used by both proof-fn and
  exec-fn paths. Each error has `help: Some("generated .lean
  file: ...")` so users can still `cat` the artifact.

User feedback that shaped this: "I would prefer all errors were
reported regardless of how noisy" — confirmed per-error reporting
over collapse.

**Commit 2 (`1ed726b`) — proof-fn errors point at the failing
tactic line.** Each Lean diagnostic inside a `by { ... }` body
gets a span pointing at the corresponding line in the user's
`.rs` file. New plumbing:
* `FormattedDiag` / `TactusDiag` grow
  `proof_fn_body_line_offset: Option<usize>` (0-indexed line
  offset within the user's tactic body).
* `tactic_body_line_span` in `spans.rs`: takes parent span +
  fn_start_loc + tactic_body byte range + line offset, computes
  target `BytePos` via parent.lo + (target_file_byte -
  fn_first_byte_in_file) delta. No `SourceMap` needed at
  construction — works from verifier worker threads (where
  source_map is None).
* `raw_span_data` (new) reads a `SpanData` out of a `RawSpan`
  via plain `downcast_ref::<SpanData>().copied()` — sidesteps
  the rustc-thread warning from `from_raw_span` (which uses
  `Span::data()`, an interner round-trip). The `unsafe`-free
  way to get `BytePos` and `SyntaxContext` on a worker thread.
* Construct a fresh `SpanData` directly (it's pub fields) and
  `Arc::new(...)` as the RawSpan. No `Span::with_lo` /
  `Span::data()` calls — those use the rustc thread-local
  interner.

The same-day chained-compare false-start (Path 1 in DESIGN.md's
new "Alternatives rejected" list) — multi-byte
`Pattern_White_Space` replacement (LRM/NEL) — turned out to be
more complex than just recomputing `multibyte_chars`. User
pushed back; we picked the simpler path.

**Commit 3 (`68317dd`) — source preview shows original tactic
content.** The proof-fn `-->` from commit 2 pointed at the right
line but rustc rendered a blank preview, because
FileLoader-sanitized content (blank spaces inside tactic
blocks) is what rustc cached in `SourceFile.src`. Fix: at
diagnostic emission time, swap `sf.src` back to the original
content. Mechanism:
* `TactusFileLoader::read_file` caches the original content per
  canonical path in a static `OnceLock<Mutex<HashMap<PathBuf,
  Arc<String>>>>` before sanitization.
* Sanitizer extended to preserve `\r` (alongside `\n`) so CRLF
  line endings don't desync `normalized_pos` between sanitized
  and original.
* `spans::swap_source_for_diagnostics` looks up the SourceFile,
  recomputes `multibyte_chars` from original content via a
  ~20-line UTF-8 byte-length helper (since rustc's
  `analyze_source_file` is `pub(crate)`), writes both
  `sf.src` and `sf.multibyte_chars` through a `*mut SourceFile`
  derived from `Arc::as_ptr`. Memoized per file via static
  `SWAPPED_FILES` set.
* `Reporter::report_as` (which runs on the main thread, the
  only consumer of `sf.src` via rustc's diagnostic renderer)
  calls the swap helper for each span's file before forwarding
  to rustc. The threaded path's `QueuedReporter` forwards
  messages to the main thread which then calls `report_as`, so
  the swap reliably runs before rendering.

Safety of the `unsafe`: single-threaded reader (main reporter
thread; workers hold `BytePos` values, not `Arc<SourceFile>`),
no concurrent mutation (rustc creates SourceFiles at load and
doesn't mutate after; our swap is the only post-construction
write).

Result: `--> test.rs:18:5` followed by `18 |     omega` followed
by `|     ^^^^^`. Carets align correctly even on Unicode lines
because `multibyte_chars` was recomputed.

**Discipline notes worth recording**:

* *Pushback shaped the design twice.* User's first pushback
  rejected selective sanitization ("many reasons we listed in
  DESIGN.md"). Second pushback rejected multi-byte
  `Pattern_White_Space` replacement chars in favor of the simpler
  recompute-on-swap. Both pushbacks were right — each time I was
  reaching for "clever" where "boring" was sufficient.

* *The byte-count-preserving sanitizer was already the right
  thing.* The whole fix turned out to be "trust what the
  sanitizer already did (preserve byte offsets), recover the
  original content for display." Didn't need to fight any
  existing decision.

* *Avoid `from_raw_span` from worker threads.* It calls
  `Span::data()` which uses rustc's thread-local interner and
  prints a backtrace warning when called off-thread. New
  `raw_span_data` helper does a plain downcast — same access,
  no warning. Pattern: when a function wraps a simple operation
  in caution-for-a-specific-case, sometimes the simple operation
  is enough without the wrapping. (Captured in poem "the
  wrapping the function did".)

**Commit 4 (`0c39701`) — DESIGN.md documentation.** New
subsection "Diagnostic source preview swap (landed 2026-05-19)"
under the Unicode/sanitization chapter. Documents the fix
mechanism, safety invariants, and six rejected alternatives:
selective sanitization, tree-sitter-guided variant, append-to-
message-body, drop-rustc-Span hand-render, multi-byte
Pattern_White_Space replacement, fork-rustc_span,
wrap-rustc-emitter. Each with one-paragraph why-not.

**Test counts**: 425 → 435 e2e (+10 across the arc), 195 → 209
unit. vstd 1530/0 unchanged. Six commits including the lakefile
tutorial-helper registration (carried in working tree from prior
tutorial work) and a poems commit ("hollow line" / "the wrapping
the function did" / "one for one").

**Caveats remaining**: none significant. CRLF handling is a
pre-existing latent issue (sanitizer used to replace `\r` with
space) — fixed as a side effect of this work. 4-byte UTF-8 chars
in tactic bodies (emoji, mathematical symbols above U+FFFF)
remain a tiny edge case — `multibyte_chars` recompute handles
them correctly, but they're rare enough that no test exercises
the path.

#### Current session (2026-05-19 continued — four review passes on the error-span arc)

After the error-span work landed, ran multi-lens review passes
over the arc. DESIGN.md § "Code review strategy" names the
discipline ("each pass asks a different question; ~15 minutes
of right-way reading turns up 4 items the earlier pass hadn't
seen"). Four passes landed; each surfaced something the prior
ones missed.

**Pass 1 (`2f6531a`) — shape.** Typed `DiagLocation` enum
(`Direct(Span)` | `ProofFnBodyLine(usize)` | `Unknown`)
replacing two parallel `Option` fields on `TactusDiag` and
`FormattedDiag`. The "both Some" combination was meaningless
and would have caused the verifier to silently prefer the
span over the offset; now structurally unrepresentable. Same
typed-invariant pattern as `MutArgInfo` / `LoopInvKind` /
`DecreaseLevel`. Also: extracted `parse_file_line_col` helper
(was duplicated inline in `Reporter::report_as` and
`tactic_body_line_span`); fixed stale docstring on
`emit_tactus_diag`; extracted `LEAN_FILE_HELP_PREFIX` and
`NO_ERROR_DIAGNOSTICS_BODY` to `vir::tactus_messages` (lens 15
magic-string avoidance); added 12 new unit tests for the
helpers; added a CRLF-preservation regression test.

**Pass 2 (`93183ba`) — second-reading finish.** Three small
findings on re-read: (a) test comment on
`multibyte_chars_two_byte` mentioned `≤` but the test used only
`é`; (b) `DiagLocation` doc overclaimed what the enum fixed
(only "both Some" was actually wrong; the other unused-but-
permitted combos weren't); (c) two consecutive `for sp in
&msg.spans` loops in `Reporter::report_as` could be fused into
one.

**Pass 3 (`d8e49fd`) — soundness.** Real finding:
`swap_source_for_diagnostics` had a TOCTOU between checking
`SWAPPED_FILES` and the unsafe `*mut SourceFile` write. The
check held the lock briefly, then released it; the unsafe
write ran outside the lock. If two threads passed the check
simultaneously, both could perform the unsafe write — two
`*mut` writes to the same location without synchronization is
UB even though they'd produce identical content. Today only
the main-thread `Reporter::report_as` calls in, so no race in
practice, but the function was `pub`. Belt-and-suspenders fix:
hold the lock through the entire critical section (check →
cache lookup → SourceFile lookup → unsafe write → insert);
restricted visibility to `pub(crate)` so the safety story
doesn't depend on caller discipline alone; added a third
safety invariant to the doc-comment.

**Pass 4 (`b85ac32`) — point-in-time consistency.**
`tactic_body_line_span` was re-reading the file from disk
while `swap_source_for_diagnostics` used the
`TactusFileLoader` cache. If the user edits the file between
rustc parsing and diagnostic emission, the two helpers would
see different content — the span would point at line N of new
content while the rendered preview showed line N of old
content. Switched the helper to use the same cache. Both
consistent now (both describe the rustc-parsed snapshot); saves
one disk syscall per failing proof-fn diagnostic as a side
effect.

**The pattern across passes.** Each pass asked a different
question. Pass 1 asked "what's the right shape?" — caught
shape and helper issues. Pass 2 asked "what reads wrong on a
re-read?" — caught comment / doc / loop-fusion issues. Pass 3
asked "what assumptions are baked into the safety story?" —
caught the TOCTOU. Pass 4 asked "what's the time-axis story?"
— caught the file-edit-mid-build inconsistency. The DESIGN.md
framing held: "review passes never reach a fixed point because
the questions are unbounded; what you do is run enough lenses
that the *known unknowns* are small."

**Test counts**: 209 lean_verify unit tests (unchanged), 66
rust_verify unit tests (+14: 13 new spans tests for
`parse_file_line_col` and `compute_multibyte_chars`, plus the
CRLF preservation test). 435 e2e + 1 coverage + 7 integration
unchanged; vstd 1530/0.

#### Current session (2026-05-20 — investigation: transparent-wrapper peel vs trait dispatch; no code landed)

Began thinking we'd land "filter cross-crate redundant blanket
impls" to unblock `test_exec_call_mut_arg_vec_index_probe` (the
vec_index Err pin). Through pushback + investigation, the work
unfolded into a structural finding that's bigger than the
immediate symptom. **No code changes landed** beyond a pinned
regression probe + this doc entry. The deliverable is the
analysis preserved for a future session that has appetite for
the multi-session refactor it actually requires.

**What we found** (in order):

1. **Bug B (same-crate blanket-impl assoc-type passthrough) is
   green**, but the cross-crate vec_index version still fails
   with multiple structural issues:
   - vstd's four `View` blanket impls (`View for &A`, `Box<A>`,
     `Rc<A>`, `Arc<A>`) all emit instance heads with Self peeled
     to bare typ-param → all four heads are `view.View A V`
     (duplicates).
   - Standalone defs for these impl methods aren't emitted (the
     dep walk doesn't reach them; nothing in the test calls
     `(&u8).view()` or `Box<u8>.view()`). Instance bodies
     reference unresolved `view.impl__N.view`.
   - "Unknown identifier `View.view`" is downstream of those
     unresolved standalones plus a namespace-prefix-dropping
     bug in cross-crate inlined ensures rendering.

2. **The probe (`test_non_forwarding_blanket_over_ref_probe`)
   demonstrates the gap is NOT vstd-specific.** Same-crate user
   code writing `impl<A: Foo + ?Sized> Foo for &A { spec fn
   foo(&self) -> int { (**self).foo() + 1 } }` and then asserting
   `(&h).foo() == 8` fails — Tactus's peel collapses `&Holder →
   Holder` at the dispatch site, picks the concrete `Foo Holder`
   instance, returns 7. The blanket's `+1` is silently dropped.

3. **The root cause is Tactus's peel-at-dispatch decision.** For
   pure-forwarding blanket impls (vstd's case), the peel
   coincidentally gives the right answer because the inner
   type's instance produces the same value. For non-forwarding
   ones (the probe), Tactus silently dispatches wrong.

4. **Verus handles this via separate type-ID encoding.** In
   `vir::context::DECORATE = true` mode (the default),
   `sst_to_air::monotyp_to_id` emits a two-component type-ID
   `(REF, basic A)` for `&A` distinct from `(NIL_SIZED, basic A)`
   for `A`. The SMT value type is still peeled (both `Poly`), but
   dispatch axioms key off the type-ID — so the blanket impl
   provides a real dispatch bridge. **Tactus's peel diverges
   from Verus's semantics here**; the divergence is silent for
   forwarding blankets, observable for non-forwarding ones.

5. **A filter (skip redundant cross-crate blanket-over-typ-param
   instances) is triage, not a fix.** It would unblock the
   vec_index probe by removing emission noise, but doesn't
   correct the underlying peel-at-dispatch divergence. User
   code with non-forwarding blanket impls would remain silently
   wrong.

**Proper fix shape** (for a future session with appetite):

- Add opaque wrapper types to `TactusPrelude.lean`:
  `axiom Ref : Type → Type`, plus `MutRef`, `Box`, `Rc`, `Arc`.
  Inhabited instances. Deref ops (`Ref.deref : Ref A → A`) as
  axioms.
- Modify `typ_to_expr` Decorate arm to render reference
  decorations distinctly (NOT peel them). Keep peeling `Boxed`
  (Verus's poly encoding, genuinely Lean-transparent) and
  probably keep peeling `Ghost`/`Tracked` (verification metadata,
  not runtime types).
- Modify expression renderer: `*r` for `r: &A` emits
  `Ref.deref r`; `&x` emits `Ref.mk x` (or equivalent — check
  what Verus's lowering produces).
- Audit every use of `peel_typ_wrappers`. Distinguish
  structural-identity peels (keep — `is_int_height`,
  `decrease_height_datatype`, `field_recursive_target`) from
  rendering-equivalence peels (remove — `type_short_name`,
  `typ_to_expr`).
- `type_short_name` returning `Ref`/`Box`/etc. for the wrapper
  cases satisfies the "never `impl__N`" principle as a side
  effect.
- Audit `#55`/`#94`/`#107` `&mut` infrastructure for interactions
  with `MutRef A` as a distinct type.
- Expect substantial test churn: many existing tests bind
  `&self` and would see their signatures change. Plan for
  multi-pass test triage.

**Scope estimate**: 3-5 focused sessions. Phasing in the
final reply of this conversation (Phase 1 = additive prelude
behind flag; Phase 2 = un-peel `Ref` only and validate probe;
Phase 3 = broaden to `Box`/`Rc`/`Arc`/`MutRef` + fix test
fallout; Phase 4 = cleanup + DESIGN.md update + remove flag).

**Pinned probe**: `test_non_forwarding_blanket_over_ref_probe`
in `rust_verify_test/tests/tactus.rs` (Err) — flips to Ok when
the un-peel landing happens. Documents the gap in code so
future sessions don't rediscover it from scratch.

**Why we stopped here**: I noticed my analysis oscillating
between recommendations (filter / un-peel / both / track for
future) — five-ish iterations in one conversation. Danielle
named the fatigue directly and offered to stop. The
investigation itself IS a deliverable; pushing through to land
code in that state would have been the wrong move. The proper
fix needs a session that begins with it as the priority, not a
session that ended in it after a long detour through alternate
options.

**Test counts**: 435 e2e (+1 if probe lands, unchanged otherwise
since probe is Err-pinned and would have been Err either way).
209 lean_verify unit, 66 rust_verify unit, 7 integration. vstd
1530/0.

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
                     constructs WpCtx (fn_map, type_map, ret_name, ensures_goal_with_marks)
                     build_wp(check.body, Done(ensures_goal), ctx) → Wp<'_>
                     walk_obligations(wp, ctx, OblCtx::new(), &mut emitter) → Vec<Theorem>
                       — one theorem per obligation site (Assert / Done conjunct / loop
                         init invariant / loop maintain conjunct / call precondition /
                         assert-by). See "Per-obligation theorem emission" below.
  3. debug_check(&cmds) — sanity::check_references panics on unresolved references
     (gated on #[cfg(debug_assertions)])
  4. pp_commands(&cmds) → PpOutput { text, landmarks: { tactic_starts, span_marks } }
     — tactic_starts[0] gives 1-indexed line where `Tactic::Raw` body begins (proof fns);
       span_marks[i] = { line, loc, kind } per emitted SpanMark (exec fns)
  5. write_lean_file(path, text) → $TACTUS_LEAN_OUT/{crate}/{fn}.lean
  6. lean_process::check_lean_file(path, lake_dir) — invokes `lake env lean --json <path>`
  7. Parse JSON diagnostics, map via LeanSourceMap (find_span_mark filters to obligation
     kinds only; closest-preceding-mark is structurally exact under per-obligation),
     report through Verus
     (error messages include the generated .lean path for easy inspection)
```

### Per-obligation theorem emission

`sst_to_lean::build_wp` (SST → Wp) and `walk_obligations` + helpers (Wp → Vec<Theorem>). Each `Wp<'a>` variant has its own walker arm; obligation sites emit theorems, structural sites push frames onto an `OblCtx`. The `OblCtx` accumulates Let / Hyp / Binder frames as the walker descends, and `wrap` folds them around each emitted goal in source order.

- **`Done(leaf)`** — `emit_done_or_split` peels top-level `Let` (push to OblCtx, recurse on body), splits top-level `And` (recurse on each conjunct), and emits the leaf at SpanMark or unwrapped fallback. Multi-clause ensures naturally yields one Postcondition theorem per clause; loop-body terminators yield per-invariant + per-decrease theorems.
- **`Let(x, rhs, body)`** — `walk_let` peels for value-position if-shapes (forks into two recursive walks with cond as Hyp frame) and inner `let z := zval; bodyval` shapes (peels one layer of inner let into OblCtx, continues lifting on bodyval). Plain rhs pushes a Let frame and recurses on body. No theorem emitted.
- **`Assume(P, body)`** — pushes `Hyp(P)` frame; no theorem emitted.
- **`Assert(P, body)`** — emits one theorem for `P` (kind from `detect_assert_kind`: `Termination` for `CheckDecreaseHeight`, `Plain` otherwise). Body walks with `P` as a Hyp frame for subsequent obligations.
- **`Branch { cond, then_branch, else_branch }`** — walks each branch under its own `Hyp(cond)` / `Hyp(¬cond)` frame. `cond` is wrapped in a `BranchCondition` SpanMark — hypothesis-kind, never an error label, but produces the `/- @rust:LOC -/` comment.
- **`Loop { cond, invs, decrease, modified_vars, body, after }`** — `walk_loop` emits one init theorem per invariant; walks `body` in maintain ctx (∀ mod_vars + bounds + invs as hyps + cond as hyp + `_tactus_d_old := D` let); walks `after` in use ctx (∀ mod_vars + bounds + invs as hyps + ¬cond as hyp). Body's `Done(inv_conj_marked ∧ decrease_marked)` flows through `Wp::Done` → `emit_done_or_split` per-conjunct.
- **`Call { callee, args, dest, after }`** — `walk_call` emits a precondition theorem for substituted requires (skipped when callee.require is empty), then walks `after` under `∀ ret, ret_bound → ensures(subst) → let dest := ret;` frames (each frame pushed only when meaningful — empty ensures skips the Hyp(True) push).
- **`AssertByTactus { cond: Some(P), tactic, body }`** — emits one theorem for `P` with the user's tactic as closer (or `tactus_auto` if tactic is empty); body walks with `P` as Hyp.
- **`AssertByTactus { cond: None, tactic, body }`** — pushes the tactic onto `e.tactic_prefix`; every theorem emitted in body's scope gets `(tactic) <;> closer` (skipped if tactic is empty). `<;>` rather than `;` handles goal-closing prefixes (e.g., `simp_all`) cleanly: zero remaining subgoals means the closer no-ops instead of failing with "no goals".

Each emitted theorem's tactic body is `tactus_auto` (`rfl | decide | omega | simp_all | tactus_case_split | fail`) — no `tactus_peel` needed because per-obligation theorems are flat (single obligation, accumulated context as frames). `tactus_auto`'s `omega` and `simp_all` handle ∀/→/let frames natively.

`AssertKind` splits into obligation-firing kinds (Plain / Postcondition / LoopInvariant / LoopDecrease / CallPrecondition / Termination) and hypothesis-only kinds (LoopCondition / BranchCondition). `find_span_mark` filters to obligation kinds only — hypothesis SpanMarks provide visual `/- @rust:LOC -/` debug comments but never appear as error labels. The split is enforced by `is_obligation_kind()`.

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
                     `build_wp_call`, `build_wp_loop`, `walk_obligations`,
                     `walk_call`, `walk_loop`, `walk_let`,
                     `walk_assert_by_tactus`, `emit_done_or_split`.
                     `check_exp` is a thin validation wrapper around
                     `sst_exp_to_ast_checked`.
                     `peel_transparent(&Exp) -> &Exp` is the shared
                     Box/Unbox/CoerceMode/Trigger peeler;
                     `peel_value_position` adds a layer of `Loc` peel
                     for value-position lookups (`walk_let`,
                     `lift_if_value`); `match_single_let_bind`
                     destructures `Bind(BndX::Let([single]), body)`.
                     Adding a new transparent wrapper = one edit
                     to `peel_transparent`, not multiple.
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
4. **`tactus_auto` is a dumb leaf closer.** Per-obligation theorem emission means each theorem's goal is a single obligation wrapped in the OblCtx's let/→/∀ frames — no nested `∧` structure to peel. `tactus_auto`'s `omega` and `simp_all` handle the frames natively (intros, zeta-reduction). `tactus_peel` (a recursive `∧/∀/→` peeler) survives in the prelude as a tool for ad-hoc proof blocks but isn't part of the codegen-emitted closer set anymore.
5. **Assert/assume as WP nesting, not conjoined.** `assert(P); assume(P)` (Verus's desugaring of user `assert(P)`) must NOT trivially satisfy itself. `(P) ∧ (rest)` for asserts vs `(P) → rest` for assumes.
6. **`_tactus_body_` / `_tactus_d_old` / `tactus_peel` reserved prefix.** Tool-generated names never collide with user code (Rust doesn't produce `_tactus_` or `tactus_`-prefixed identifiers).
7. **Two-layer dependency walking.** `dep_order::walk_expr` recurses through ExprX; `dep_order::walk_place` recurses through PlaceX. Place variants can hide Call refs inside; both walkers cover the full tree.
8. **Tuple rendering.** `Dt::Tuple(n)` → `T₁ × T₂ × …` type, `⟨a, b, …⟩` constructor, `.1`/`.2` field access (Lean 1-indexed).
9. **u-types render as Int, not Nat.** Lean's `Nat` truncates subtraction (`0 - 1 = 0`); rendering u8/u16/…/u128 as `Int` with both-sided bounds makes underflow catchable. USize keeps rendering as `Nat` — const-generic constraint (see DESIGN.md).
10. **WP DSL (`Wp<'a>`) with structural continuations.** Each compound node carries its own `after: Box<Wp<'a>>`; `Done(leaf)` is the only terminator and has no continuation slot. `Return` writes `Done(let ret := e; ctx.ensures_goal)`, naturally fn-exit by construction. Adding a new WP form means one constructor + one arm each in `build_wp` and `walk_obligations` — no central dispatcher to keep in sync.
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
18. **Loop break / continue via threaded `WpLoopCtx`.** `build_wp` takes `Option<&WpLoopCtx>` as a parameter; `WpLoopCtx { break_leaf, continue_leaf }` holds the goals each control-flow edge must establish. Inner loops shadow outer (innermost applies). `StmX::BreakOrContinue` emits `Wp::Done(chosen_leaf)`. `Wp::Loop::cond` is `Option<&Exp>` — `None` is Verus's break-lowered `while c { … break; … }` shape; `walk_loop` drops the cond-gates in that case.
19. **Per-obligation theorem emission (D, 2026-04-26).** One Lean theorem per obligation site instead of one mega-theorem per fn. Each theorem gets its own `pos.line` in Lean diagnostics, so `find_span_mark` returns the right `AssertKind` label by structural construction (the closest preceding obligation-kind mark IS the obligation for that theorem). `OblCtx` accumulates Let / Hyp / Binder frames as the walker descends; `wrap` folds them around each emitted goal. `AssertKind` splits into obligation-firing kinds vs hypothesis-only kinds (`is_obligation_kind()`); hypothesis-side SpanMarks (LoopCondition, BranchCondition) provide `/- @rust:LOC -/` debug comments but are filtered out of error labels.
20. **Per-test Tactus output isolation (`TACTUS_LEAN_OUT`).** `run_verus` and `run_cargo_verus` set `TACTUS_LEAN_OUT=<test_input_dir>/tactus-lean` per spawned subprocess. Without this, `cargo test`'s inherited `CARGO_TARGET_DIR` routes every test's Lean output to a shared path, races across parallel tests with same-name fns + different-content writes. Pre-D the races were masked by content homogeneity (same fn name → usually same content); per-D writes are distinctive enough to surface. See "Per-test isolation" under Testing infrastructure.
21. **`&mut` at call sites via local VIR-AST rewrite (#55).** `walk_call` introduces a fresh existential per `&mut` arg (post-call value), substitutes `varat_pre_name(p) ↦ caller_arg` (pre-state) and `p ↦ Var(fresh)` (post-state) in the inlined ensures, then rebinds the caller's local via a `Let` frame placed AFTER the ensures `Hyp`. The `VarAt(p, Pre)` rewrite to `Var(<p>_at_pre_tactus)` happens at the VIR-AST level via `rewrite_varat_for_mut_params` (a small `vir::ast_visitor::map_expr_visitor` user) BEFORE rendering — scoped to the `&mut` param name set so loop ensures' at-entry refs and non-mut params keep the natural `VarAt → Var` collapse. First instinct of changing the renderer globally failed 54 tests; scoped rewrite is the right level. `varat_pre_name` lives in `expr_shared.rs` so the rewrite-side and substitution-key-side stay in sync (compile error on divergence).
22. **Trait-method calls via callee-redirect + spec-source split (#56).** When `StmX::Call::resolved_method = Some((resolved_fun, resolved_typs))`, `build_wp_call` redirects the callee lookup from `fun` (trait method decl) to `resolved_fun` (resolved concrete impl), and uses `resolved_typs` as the type-args slice (`Self` is filled in by Verus's resolution). Inside `walk_call`, `pick_spec_source` further redirects spec lookup to the trait method decl when callee is `TraitMethodImpl`. Reason: Verus rejects impl-side `requires` declarations (impls inherit), so the impl's `require` is empty; using the trait's spec is sound because Verus enforces impl ⇒ trait via its trait-impl-checking pass. Trade-off: impl-specific strengthening of `ensures` isn't seen at call sites (caller sees the trait-level contract); deferred follow-up. `is_trait_default = Some(true)` (default-impl invocation) still rejected — separate concern.
23. **Gensym for callee return name and per-loop d_old (#78, #83).** Two same-shape gensyms after they surfaced as soundness/hardening fixes: (a) `walk_call` emits `_tactus_ret_<id>` for the ∀-bound return value (not the callee's source-level ret name), substituting the original ret name in the ensures rendering — pinned by `test_exec_call_ret_name_collision` after a real shadowing bug surfaced. (b) `Wp::Loop` carries `d_old_name: String` (built from Verus's stable `StmX::Loop::id`); `walk_loop` uses it for the `let _tactus_d_old_<id> := D` binding. Both reserve the `_tactus_*` prefix; user code can't collide. Same conceptual move in two places; the second was preemptive after the first surfaced as a real bug.
24. **`assume(P)` warnings + `CheckResult` shape (#80).** `CheckResult::Success` and `Failed` carry `warnings: Vec<String>`. The verifier emits each as `MessageLevel::Warning` before the success/error path. `collect_assume_sites` walks the VIR-AST `vir_fn.body` (NOT the SST) to find user-written `ExprX::AssertAssume { is_assume: true, .. }` — the SST has synthetic `StmX::Assume` injected by Verus's overflow / call-ensures passes, which would false-positive every overflow-checked op.
25. **Per-fn tactic override (#81) + `tactus_usize_bound` (#82).** `#[verifier::tactus_tactic("…")]` plumbs through `FunctionAttrsX::tactus_tactic: Option<String>`. `ObligationEmitter::default_closer: Tactic` is read by `simple_tactic` rather than returning a hardcoded constant — every codegen site honors the override uniformly. `assert(P) by { user_tac }` sites still use the user-supplied tactic from the assert-by; the override applies only to default-closer sites. `tactus_usize_bound` in `TactusPrelude.lean` discharges symbolic `2 ^ arch_word_bits` via `rcases arch_word_bits_valid; subst; simp; first | decide | omega`. Composes via `tactus_first | tactus_auto | tactus_usize_bound`.
26. **Labeled break via stack-threaded `WpLoopCtx` (#88).** `WpLoopCtx::label: Option<String>` carries the loop's source label. `build_wp` parameter changed from `loop_ctx: Option<&WpLoopCtx>` to `loop_stack: &[&WpLoopCtx]` (innermost-first). Each `build_wp_loop` extends the stack with its own ctx for body walks. `StmX::BreakOrContinue { label, .. }` resolves the leaf: unlabeled → `stack.first()`; labeled → `stack.iter().find(|c| c.label.as_deref() == Some(target))`. "Not found" produces internal-bug errors (Verus's mode checker should prevent them).
27. **`walk_call` substitution-state via `CallSubstitutions` struct.** What used to be 6 scattered locals (typ_subst, req_subst, ens_subst, mut_param_names, mut_idx_to_fresh, fresh_ret_name) bundle into a single struct built by `build_call_substitutions`. Two emission helpers (`emit_call_precondition_theorem`, `push_post_call_frames`) take the struct as a single shared input. Reduces `walk_call` from ~200 lines of mixed phases to ~30 lines orchestrating three named helpers; the substitution scheme (especially the `&mut` pre/post split) lives in one place with documented invariants.
28. **`build_wp_call` four-phase validation.** Was 140 lines with 6 early-Err sites + arity + mut-arg building inline. Split into `reject_unsupported_call_shapes` (split / is_trait_default), `resolve_callee` (resolved_method redirect + fn_map lookups), `validate_call_arities` (param + typ_args counts), `build_call_mut_args` (&mut detection + simple-Loc extraction). Each helper has a single concern; `build_wp_call` itself is ~50 lines.
29. **Reserved identifier conventions** (single source of truth in `expr_shared.rs`). Four conventions: (1) `_tactus_<role>_<id>` prefix for codegen-internal gensyms + theorem names; (2) `<x>_at_pre_tactus` SUFFIX (the only outlier — keeps original param name first for readable error messages); (3) `tactus_<name>` no-prefix for user-visible Lean tactics in TactusPrelude; (4) bare names in TactusPrelude (`usize_hi`, `arch_word_bits`, etc.) — safe because Tactus generates user defs inside `namespace crate.module` while these live at top-level. Cross-referenced from `sanity::name_resolves` and the gensym sites. Two gensym mechanisms: prefer Verus-stable IDs (e.g., `StmX::Loop::id`) when available; fall back to `ObligationEmitter::next_id()`.
30. **Error messages follow a three-question convention.** Every user-facing `Err(...)` answers in order: (a) what surface syntax did the user write?, (b) is there a workaround?, (c) is this tracked (task #)? Internal-bug rejections (paths that should never fire) get a short message + "please open an issue" rather than long explanations of pipeline invariants — those move to code comments.

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

`let y = if c then a else b; rest` forks into `(c → let y := a; rest) ∧ (¬c → let y := b; rest)`. At `Return`-position, `lift_if_value` produces this directly in the Done leaf. At `Let`-position (`Wp::Let`), `walk_let` peels for the same shape — recursing per branch with cond as a Hyp frame. Both peel through transparent wrappers and single-binder `ExpX::Bind(Let, …)`.

Tests: `test_exec_tail_if_expression`, `test_exec_let_if_expression`.

### Slice 5: loops ✅

`StmX::Loop` becomes `Wp::Loop { body, after }` — `body` is built with `Done(I ∧ D < _tactus_d_old)` as its terminator; `after` is the post-loop continuation. `walk_loop` emits one init theorem per invariant, walks `body` in maintain ctx (∀ mod_vars + bounds + invs as hyps + cond as hyp + `_tactus_d_old := D` let), walks `after` in use ctx. Body's `Done(inv_conj_marked ∧ decrease_marked)` flows through `Wp::Done` → `emit_done_or_split` per-conjunct — yielding `_tactus_loop_invariant_*` and `_tactus_loop_decrease_*` theorems with their own pos.line.

Tests: `test_exec_loop_count_down`, `test_exec_loop_count_up`, `test_exec_loop_invariant_fails` (negative), `test_exec_loop_sequential`, `test_exec_loop_nested`, `test_exec_loop_in_if_branch`, `test_exec_loop_in_else_branch`, `test_exec_loop_lex_decreases_rejected`, `test_exec_loop_break_rejected`, `test_exec_loop_no_invariant`, `test_exec_loop_decreases_unchanged` (negative).

Known shape restrictions (rejected by `build_wp_loop`): `loop_isolation: false`, `cond: None`, condition setup stmts, lexicographic `decreases`, `invariant_except_break` / `ensures` invariants.

### Slice 6: overflow obligations ✅ (soundness fix)

`HasType(e, U(n))` emits `0 ≤ e ∧ e < 2^n` (was `True`). u-types render as `Int`. Fixed-width params get `(h_<name>_bound : …)` hypotheses. `IntegerTypeBound(kind, _)` evaluates to the decimal literal (`u8::MAX` → `255`). `ArchWordBits` resolves to the prelude axiom. USize/ISize emit bounds via `usize_hi` / `isize_hi` constants.

Tests: `test_exec_overflow_diagnostic`, `test_exec_overflow_tight_ok`, `test_exec_signed_overflow_fails`, `test_exec_underflow_unguarded_fails` (the u-as-Int soundness demo), `test_exec_underflow_guarded`, `test_exec_mul_overflow_fails`, `test_exec_u32_add_guarded`, `test_exec_integer_type_bound_u8_max`, `test_exec_integer_type_bound_i8_max`, `test_exec_char_bound`, `test_exec_widen_u8_to_i16`, `test_exec_usize_trivially_bounded`, `test_exec_usize_overflow_fails`, `test_proof_arch_word_bits_compiles`.

### Slice 7: function calls ✅ (with recursion)

`StmX::Call` becomes `Wp::Call { callee, args, dest, after }`. `walk_call` emits one theorem for the substituted requires (kind=`CallPrecondition`, skipped if requires is empty), then walks `after` under `∀ ret, ret_bound → ensures(subst) → let dest := ret;` frames (each frame skipped when meaningful — empty ensures skips the Hyp(True) push). Callee's `require`/`ensure` are rendered via `vir_expr_to_ast` and param-substituted via `lean_ast::substitute` — no let-shadowing.

**Termination** comes via Verus's own `recursion` pass, which inserts a `StmX::Assert(InternalFun::CheckDecreaseHeight)` before every recursive call site (including mutual recursion across an SCC). `sst_exp_to_ast_checked` lowers `CheckDecreaseHeight` to the int-typed obligation `(0 ≤ cur ∧ cur < prev) ∨ (cur = prev ∧ otherwise)`. Non-int decreases rejected with a clear error.

Tests: `test_exec_call_basic`, `test_exec_call_requires_violated` (negative), `test_exec_call_in_if_branch`, `test_exec_call_in_loop`, `test_exec_call_trait_method`, `test_exec_call_trait_method_requires_violated` (negative), `test_exec_call_trait_method_two_impls`, `test_exec_call_trait_method_with_args`, `test_exec_call_zero_args`, `test_exec_call_many_args`, `test_exec_call_mut_arg`, `test_exec_call_mut_arg_wrong_post` (negative), `test_exec_call_mut_arg_requires_violated` (negative), `test_exec_call_mut_arg_field_rejected` (negative), `test_exec_call_two_mut_args`, `test_exec_call_recursive_decreasing`, `test_exec_call_recursive_nondecreasing` (negative), `test_exec_call_recursive_no_decreases` (negative), `test_exec_call_mutual_recursion`, `test_exec_ctor_rejected`.

Rejected (in `build_wp_call`): cross-crate callees, cross-crate trait method decls (#56 follow-up), split-assertion calls. `&mut x.f` for single-variant structs LANDED (#87) via Lean structure-update rebind. Deeper paths `&mut a.b.c` LANDED via #144 (recursive nested structure-update). Tuple field `&mut t.<i>` LANDED via #145 + #146 (Lean tuple syntax + multi-segment N-tuple accessors). Multi-variant enum field mutation upstream-blocked at Verus's mode check (`ref mut` not supported). `&mut v[i]` cross-crate-blocked (Vec/array indexing routes through vstd). `is_trait_default = Some(true)` LANDED (#96) — call redirects to the trait method decl.

### What's deferred

The seven original Track B slices are all landed, plus #49 / #50 / #51 / #52 (struct Ctor) / #53 / #54 / #55 (caller-side) / #56 (caller-side) / #57 / #58 / #76 / #77 / #78 / #79 / #80 / #81 / #82 / #83 / #85 / #86 / #88 / #90 / #92 / #94 (callee-side `&mut`) / #96 (trait default-impl invocation) / #99 / #100 / #101 / #102 / #103 / #104 / #105 / D from the Tier 1-3 roadmap. See **Pending work** below for the remaining queue.

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the full catalogue. Currently blocking realistic exec fns:

- **`&mut` args at call sites** — caller-side LANDED (#55), callee-side body verification LANDED (#94), `&mut x.f` for single-variant structs LANDED (#87 via Lean structure-update rebind). Deeper paths `&mut a.b.c` LANDED via #144 (recursive nested structure-update). Tuple field `&mut t.<i>` LANDED via #145 + #146 (Lean tuple syntax + multi-segment N-tuple accessors). New-mut-ref callee-side LANDED (#95); caller-side LANDED (#107) via BorrowMut local + extended recognition. Multi-variant enum field mutation upstream-blocked at Verus's `ref mut` rejection. `&mut v[i]` cross-crate-blocked.
- **Trait-method calls** — caller-side LANDED (#56) for `DynamicResolved` (concrete-receiver) and same-crate `Static`/`Dynamic` paths. Impl-specific strengthening of `ensures` LANDED via #86 — caller sees the conjunction of trait's and resolved-impl's ensures. Trait default-impl invocation LANDED via #96 — when the impl uses the trait's default body, `resolve_callee` redirects to the trait method decl (which holds the default body + spec) using the call site's typ_args. Cross-crate trait method decls remain a `#56` follow-up.
- **`assume(P)` warning** — DESIGN.md promises a "unproved assumption" compile warning; not wired.
- **USize arith rarely auto-verifies** — the bound is emitted, but `tactus_auto` can't discharge symbolic `2 ^ arch_word_bits`. Users need `cases arch_word_bits_valid` proofs.
- **Labeled `break`** — landed via #88 (label-keyed stack of `WpLoopCtx`). Labeled `continue 'outer;` still rejected by Verus upstream (needs `loop_isolation(false)` which we don't support either); the label-stack handles it in principle.
- **`invariant_except_break` / `ensures` loop invariants** — only `at_entry = at_exit = true` invariants accepted. Verus's default `invariant x …` syntax produces both, so this covers the user-written common case; more complex loop shapes (e.g., ones desugared from `while let Some(x) = it.next() { … }`) may hit it.
- **VIR / SST expression renderer unification** — shared leaves extracted into `expr_shared.rs`; the walkers themselves stay separate because the source trees are genuinely different shapes. See DESIGN.md § "Two parallel expression renderers" for the analysis of why full unification was rejected.

### Adding new slices

1. Extend `sst_to_lean::build_wp` / `build_wp_call` / `build_wp_loop` to produce a new `Wp` variant (or accept a new form). Validation (Err for unsupported shapes) happens in the same pass.
2. Extend `Wp` enum with the new variant if the WP rule doesn't fit an existing one. Each new variant needs: constructor + `walk_obligations` arm. If the variant's emission diverges enough, also add a dedicated `walk_<variant>` helper.
3. If the goal shape makes `tactus_auto` fail, add a prelude macro or emit a targeted `Tactic::Raw` at emission time. Keep `tactus_auto` dumb.
4. If new AST shapes are needed, extend `lean_ast` (preferably via smart constructors) and `lean_pp`. If the new shape has binders, extend `lean_ast::substitute` and `collect_free_vars` — three places to edit.
5. Add snippets to `tactus_coverage::run_snippets` if new VIR variants become reachable via `dep_order::walk_expr` / `walk_place`.
6. Update DESIGN.md — both any relevant architecture section and the deferrals catalogue.
7. Do a review pass (see **Code review strategy** below) before calling it done.

## Pending work

All major Tier-3 tasks have landed (#55 caller-side `&mut`, #56
caller-side trait method calls, #93 closures, #95 new-mut-ref
callee-side, #107 new-mut-ref caller-side, #110 lex decreases,
#111/#130 BitVec mode, #144 deeper field paths, #145/#146 tuple
field mutation). The 2026-05-08 session closed all 8 REVIEW.md
file-for-follow-up items plus 4 right-way structural cleanups
plus 5 caller-side-and-field-path sub-feature landings. The #106
umbrella is now fully done from Tactus's side: tuple + deeper
field paths LANDED (#144 / #145 / #146); mixed paths LANDED
(`73d1dd6`); multi-variant enum upstream-blocked; Index L-value
cross-crate-blocked. Pending count: **6 across 4 themes**. None
is on the critical path for realistic code today.

The full catalogue lives in DESIGN.md § "Known deferrals, rejected
cases, and untested edges" — this section summarizes the task
themes:

### Feature deferrals with clear shape (1 pending)

- **#112** StmX::OpenInvariant (atomic invariants for concurrency).

Closed: **#106** &mut at call sites for non-Var L-values umbrella
— all Tactus-workable sub-features landed: tuple field LANDED
(#145 + #146); deeper field paths LANDED (#144); mixed tuple-and-
struct paths `&mut s.tup.0` / `&mut t.0.f` LANDED (`73d1dd6`,
2026-05-11); multi-variant enum field mutation upstream-blocked at
Verus's `ref mut` mode check; `&mut v[i]` Index L-value cross-
crate-blocked (Vec/array indexing routes through vstd, #122
dependency). **#107** caller-side new-mut-ref mode LANDED
(2026-05-08) — BorrowMut locals fold into the existing
`mut_param_names` set via `build_borrow_mut_binders` +
`mut_ref_locals` field on `WpCtx`. #108 / #109 / #111 / #130
(2026-05-05); **#113**
BinaryOp::StrGetChar (2026-05-11) — `Tactus.strGetChar` prelude
helper replaces the incorrect `String.get` head emitted by
`non_binop_head`; both VIR-AST and SST renderer paths now lower
cleanly. **#127** loop_isolation: false support (2026-05-11) —
upstream `StmX::Loop.original_cond` field preserves the pre-
break-lowering cond; Tactus's `build_wp_loop` recovers the
cond:Some encoding under single-break + unlabeled + empty-cond-
setup soundness gates. Natural-exit fact (`¬c` post-loop)
available without ergonomically-painful `allow_complex_invariants`
+ `ensures` workarounds.

### Architecture cleanups (0 pending)

Closed: **#117** fuse two-pass over loop bodies — *audited
2026-05-11; keep as-is.* Fusion would mean threading
`&mut ModCollector<'a>` through 7 `build_wp` call sites and
entangling concerns at every future statement variant; perf
saving is one tree traversal per loop body (realistic 10-100
stmts, dominated by Lean checking, not Rust). Conditions for
revisiting documented inline in DESIGN.md's architecture-debts
section. Same audit-sweep shape as 2026-05-11's #149–#153 — net
0 code, deliverable is doc clarity.

Closed: **#97** `OblCtx::with_frame` O(N²) → `im::Vector` (LANDED
2026-05-09; same session also moved `loop_stack` from `&[&WpLoopCtx]`
to `LoopStack<'p>` linked-list, eliminating a sibling allocation
hot spot).

Closed: #98 / #116 / #118 / #119 (earlier sessions); plus the
2026-05-08 right-way batch (#140 orphaned doc / #141 PreambleConfig
enum / #142 shared test_fixtures module / #143 per-theorem
preamble requirements).

### Robustness + test gaps (0 pending — open umbrella)

Closed: **#121** test coverage probes (2026-05-11) — closures with
user `requires` ✅ `test_exec_closure_with_requires`; closures with
user `ensures` ✅ `test_exec_closure_with_ensures`; tactic
referencing loop-local ✅ `test_exec_assert_by_omega_in_loop_body`;
`BinaryOp::Xor` reasoning ✅ `test_exec_xor_bool_concrete` + `_gap`
(found a real automation gap pinned as Err); `assert forall|v| P
by { tac }` upstream-blocked (Verus poly panic); return-in-else /
multi-var loops already pinned in earlier sessions. The umbrella
stays as an open ticket for future surfaces.

Closed: #126 / #129 (earlier sessions); 2026-05-08 closed all 9
REVIEW.md follow-ups (#131-139) — full list in REVIEW.md's
"2026-05-08 follow-up" section.

### Phase 3 (1 task + 2 sub-items)

- **#122** cross-crate verification (CrateDecls.lean) — gating
  for everything cross-crate.
- **#123 (partial — heartbeats piece LANDED 2026-05-11)**: the
  `#[verifier::heartbeats(N)]` attribute plumbs through to
  `set_option maxHeartbeats N in` per theorem. Remaining
  sub-items: per-module `.lean` file generation (currently per-fn —
  fine at our scale), CI matrix for multi-Lean-version testing.

### Upstream-blocked (2 tasks)

- **#124** exec-mode closure calls (FnOnce/Fn/FnMut) — Verus's
  `exec_nonstatic_call` not supported; lifting needs Verus-side
  work.
- **#125** cross-crate trait method decls + cross-crate dyn Trait
  — unblocked by completing #122.

### Tasks closed in 2026-05-02 / 2026-05-03 (sub-tasks for history)

- **#95 new-mut-ref callee-side** (2026-05-02). Caller-side still
  deferred → #107.
- **#93 closures** (2026-05-02). Three slices landed; FnOnce/Fn/FnMut
  exec calls deferred → #124.
- **#120 (partial) shape-drift tests** (2026-05-03). Two of four
  gaps closed; remaining two split → #126.
- **#115 sst_exp_to_ast shim removal** (2026-05-03). Pre-#100
  panic-shim gone; sites use either the typed
  `lower(Validated::check(e)?)` pipeline or `expect("<contract>")`
  with site-specific messages.
- **#110 lexicographic decreases** (2026-05-03). Both fn-level
  (a no-op via Verus's recursive `otherwise`) and loop-level
  (lex disjunction in `lex_decrease_obligation`) covered.
- **#114 loop shape extensions sub-feature 1 (cond_setup)**
  (2026-05-03). Two iterations: first via Validated lifetime
  drop (Arc clone, sus); second via `Wp::Hyp { hyp: LExpr, body }`
  variant for synthesized hypotheses (clean, borrow-only).
  Sub-feature 2 (loop_isolation: false) split → #127. Automation
  gap split → #128.

### Earlier-deferred items still open

- **`&mut v[i]` / deeper paths / multi-variant enum field mutation
  (#55 follow-ups, not in pending-tasks list).** Index L-values
  need a different encoding (array "one-element-changed" property);
  deeper field paths can extend #87's structure-update pattern but
  need recursive Loc handling; multi-variant enum field mutation
  needs a match-and-rebuild encoding.
- **Cross-crate trait method decls + cross-crate `dyn Trait`
  (#56 follow-ups, not in pending-tasks list).** Both require
  Phase 3 cross-crate infrastructure (`CrateDecls.lean`).

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
| `cargo test -p lean_verify --lib` | 154 | AST pp (precedence, tuples, indexing), `substitute` (shadowing, capture avoidance via alpha-rename for Let/Lambda/Forall/Exists/Match incl. Pattern::Binding + dependent types), `mentions_free_var` (binder-scope tracking), `strip_span_marks` + SpanMark metadata preservation through substitute, `walk_children` / `map_children` identity round-trip + visit-count regression guards + `scope_kind` direct categorization + `QuantifierKind::build` dispatch (#98), `Wp` / `walk_obligations` / `contains_loc` / `lift_if_value` (incl. multi-binder chain lift) / `peel_value_position` / `match_single_let_bind`, type translation, sanity check scope tracking + prelude-name auto-derivation, `format_rust_loc`, lean_process, `LeanName` constructors |
| `cargo test -p lean_verify --test integration` | 7 | Tactus-prelude + Lean invocation end-to-end on hand-written Lean |
| `vargo test -p rust_verify_test --test tactus` | 292 | Full e2e: VIR → AST → Lean for proof fns + exec fns (all slices, source mapping, match automation, recursive datatypes incl. generic `List<A>`-style + multi-param `Tagged<A, B>` with implicit type-param binders + mutually recursive SCCs via Lean `mutual ... end` blocks (#109) including cross-fn-SCC cross-type decreases + 3-element cycles + SCC-plus-standalone mixes + single-variant non-eponymous enums + generic mutual SCCs + multiple independent SCCs in one crate, `assert(P) by(bit_vector)` via BitVec-mode rendering + Lean core `bv_decide` (#111/#130: concrete + commutativity + associativity + AND/OR comm + xor_self + negative), per-obligation theorems with AssertKind labels pinned, &mut at call sites + callee-side &mut body + &mut x.f via structure update, trait-method calls with impl-strengthened ensures + default-impl invocation, bit-width matrix, control-flow combinations incl. return-in-else / multi-var loops / nested-if-with-loops, lossy-accept paths, name-collision regression guard, assume warning, per-fn tactic override, tactus_usize_bound, HeightCompare, labeled break, reveal_with_fuel/unfold workflow, array indexing via array_index, invariant_except_break / loop ensures, chained-compare distinct-temps regression, new-mut-ref callee-side normalization, exec closure declarations + body verification scope + spec-closure calls, lexicographic decreases for fns + loops with `0 ≤ cur` lower bound, ret-substitution at call sites for `r == E` ensures) |
| `vargo test -p rust_verify_test --test tactus_coverage` | 1 | Coverage assertion: expected VIR variants all hit by `walk_expr`/`walk_place` |
| `vargo build --release` (vstd) | 1530 | Regression guard: vstd proof library still verifies |

### Per-test isolation for Tactus output (`TACTUS_LEAN_OUT`)

`run_verus` in `tests/common/mod.rs` sets `TACTUS_LEAN_OUT` to `<test_input_dir>/tactus-lean` for every spawned subprocess. Without this, generated `.lean` files would land in the shared `<rust_verify_test target>/tactus-lean/test_crate/<fn>.lean` (because cargo's inherited `CARGO_TARGET_DIR` overrides the relative-CWD fallback in `lean_out_root`). Two tests defining a fn with the same name but different content would race in parallel runs, producing flaky failures whose root cause is invisible (one test's output overwrites the other's between Lean spawn and disk read). Per-test `TACTUS_LEAN_OUT` gives each test its own output tree.

Symptom of regression: same test fails on one cargo run and passes on the next; running it alone passes. Likely cause: the env-var setting got lost.

### Lake-bypass under parallel test runs (`LEAN_PATH`)

`lake env lean` acquires a per-project configuration lock when invoked. Parallel rust_verify subprocesses (one per test, default `cargo test` parallelism) all hit the same lock, producing
`could not acquire an exclusive configuration lock; another process may already be reconfiguring the package` errors that take down the whole test suite.

The fix has two pieces:

* **Test harness side** (`tests/common/mod.rs`): `cached_lean_path_for_lake_project()` resolves `LEAN_PATH` *once* per test-binary process by running `lake env printenv LEAN_PATH` in the lake-project dir (one lock acquisition, brief). `inject_cached_lean_path` injects the cached value into every subprocess via `child.env("LEAN_PATH", ...)`. Both `run_verus` and `run_cargo_verus` call it.
* **`lean_verify` side** (`lean_process.rs`): `check_lean_file` checks `std::env::var_os("LEAN_PATH")` — if already set, runs bare `lean --json <path>` instead of `lake env lean`. The subprocess inherits `LEAN_PATH` from the harness and resolves Mathlib imports through it without going through lake.

Net: only the FIRST test-binary invocation acquires the lake lock; every subprocess runs `lean` directly. Multi-threaded runs of the full e2e suite go from "fails with lock errors" to "completes in ~5 min instead of 25 min single-threaded."

For non-test users (e.g., direct `cargo verus` invocations) `LEAN_PATH` is unset and the original `lake env lean` path is taken — no behaviour change.

Symptom of regression: parallel `cargo test -p rust_verify_test --test tactus` hits a wave of "could not acquire an exclusive configuration lock" errors. Likely cause: `LEAN_PATH` not being injected, or the `lake env printenv` step failing silently (project moved / not built). Workaround: re-run with `--test-threads=1`.

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

### Debugging Err-expected tests

Tests written with `=> Err(_)` (or `=> Err(err) => { ... }`) match
*any* verus failure and pass silently in default `cargo test` output —
useful for pinning deferred functionality, but hides what error
actually triggered the match. Two ways to see the captured error:

* **`cargo test ... -- --nocapture`** — surfaces the full Lean / verus
  diagnostic plus a one-line summary line `[test_name] passed matching
  Err pattern; verus: Err(N error(s); first: "<first line>")` emitted
  by the test harness macro. The summary line confirms WHICH error the
  pattern caught, useful when debugging "did my Err probe fail for
  the right reason?"
* **`VERUS_KEEP_TEST_DIR=1`** — preserves `target/debug/test_inputs/
  <test-binary>-<test_name>/` instead of deleting it on pass. Inside,
  `tactus-lean/test_crate/<fn>.lean` is the generated Lean file — run
  it through `lake env lean` directly to see the raw Lean error
  (often more informative than verus's reformatted version).

When `=> Err(_)` doesn't match (i.e., test expected failure but verus
returned Ok), the pattern-mismatch panic now includes the actual
result: `[test_name] expected pattern '\`Err(_)\`' but got: Ok(...)`
— previously a bare "Err(_) does not match $result" with no context.

## Repository layout

```
tactus/
  DESIGN.md                    ← comprehensive design document (includes
                                 deferrals catalogue under §
                                 "Known deferrals, rejected cases, and
                                 untested edges")
  HANDOFF.md                   ← this file
  POEMS.md                     ← chronological index pointing at poems/
  poems/                       ← per-date poem files (YYYY-MM-DD.md)
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
        sst_to_lean.rs         ← WpCtx + Wp DSL + build_wp / walk_obligations
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
      tactus.rs                ← 277 end-to-end tests
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
10. **`OblCtx::with_frame` clones the whole `frames` Vec per call.** O(N²) memory across deeply-nested recursion (asserts inside branches inside loops). Realistic exec fns don't go deep enough for this to matter; switching to `Rc<im::Vector<_>>` (structural sharing) would fix it without changing the API.
11. **`Wp::Branch` still clones `after` into both branches.** Exponential in nested if-depth. Fine for realistic code (DESIGN.md § "Known codegen-complexity trade-offs"). Rc/arena would fix cleanly; neither is worth the lifetime-threading cost yet. The same pattern repeats at the walker level: per-obligation emission visits the post-if continuation's obligations once per branch path, so a fn with K nested ifs and N obligations after the last if emits 2^K × N theorems for the post-if work. Realistic code stays well below.
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

# Lean must be on PATH for the test subprocess. If `which lake` works,
# `PATH="../tools/vargo/target/release:$PATH"` is enough. If only
# `~/.elan/toolchains/` is populated (no `~/.elan/bin/` proxy),
# prepend the pinned toolchain's bin dir explicitly:
#   PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.25.0/bin:../tools/vargo/target/release:$PATH"
# (See DESIGN.md "Putting Lean on PATH" for the long form.)

# ── Full test suite ────────────────────────────────────────────────
# 277 end-to-end tests
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus

# Coverage matrix (1 test, asserts walker visits the expected variant set)
PATH="../tools/vargo/target/release:$PATH" vargo test -p rust_verify_test --test tactus_coverage

# 114 unit tests (AST pp, substitute, Wp DSL, sanity check, type translation,
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
