# Tactus Handoff Document

## What is Tactus?

Tactus is a fork of Verus that replaces Z3 (SMT solver) with Lean 4's proof kernel for verification. Users write Rust code with specs (`requires`/`ensures`/`invariant`) and Lean-style tactic proofs using `by { }` blocks. The `.rs` files are the single source of truth.

See `DESIGN.md` for the full design rationale and decisions, including a comprehensive "Known deferrals, rejected cases, and untested edges" catalogue.

## Current state

**217 end-to-end tests + 1 coverage test + 114 unit tests + 7 integration tests pass.** vstd still verifies (1530 functions, 0 errors). The pipeline works: user writes a proof fn with `by { }` or an exec fn with `#[verifier::tactus_auto]`, Tactus generates typed Lean AST, pretty-prints to a real `.lean` file, invokes Lean (with Mathlib if available), and reports results through Verus's diagnostic system.

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

Rejected (in `build_wp_call`): trait-default-impl calls (`is_trait_default = Some(true)` — #56 follow-up), cross-crate callees, cross-crate trait method decls (#56 follow-up), split-assertion calls, `&mut x.f` / `&mut v[i]` (non-simple Loc shapes — #55 follow-up).

### What's deferred

The seven original Track B slices are all landed, plus #49 / #50 / #51 / #52 (struct Ctor) / #53 / #54 / #55 (caller-side) / #56 (caller-side) / #57 / #58 / #76 / #77 / #78 / #79 / #80 / #81 / #82 / #83 / #85 / #88 / #90 / #92 / D from the Tier 1-3 roadmap. See **Pending work** below for the remaining queue.

See DESIGN.md § "Known deferrals, rejected cases, and untested edges" for the full catalogue. Currently blocking realistic exec fns:

- **`&mut` args at call sites** — caller-side LANDED (#55). Callee-side body verification (`tactus_auto` on a fn that itself takes `&mut`), `&mut x.f` / `&mut v[i]` shapes, and new-mut-ref mode are documented `#55` follow-ups.
- **Trait-method calls** — caller-side LANDED (#56) for `DynamicResolved` (concrete-receiver) and same-crate `Static`/`Dynamic` paths. Trade-off: impl-specific strengthening of `ensures` not seen at call sites (caller sees the trait-level contract). `is_trait_default = Some(true)` and cross-crate trait method decls are documented `#56` follow-ups.
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

Both major Tier-3 tasks (#55 caller-side `&mut`, #56 caller-side trait
method calls) have landed MVS-form. Remaining work is a set of
follow-ups, each smaller and pickable independently.

### #55 follow-ups

The caller-side MVS landed. The remaining `&mut` work breaks into three
distinct sub-tasks; each could be picked up independently:

- **Callee-side body verification.** Allow `tactus_auto` on a fn that takes
  `&mut` params. Needs fn-entry binding of `<x>_at_pre_tactus` and
  rewriting of body assignments to thread post-state forward through SSA.
  Largest of the three.
- **Non-simple `Loc` shapes** (`&mut x.f`, `&mut v[i]`). Currently rejected
  in `build_wp_call`. Verus's Z3 path uses havoc-base + assume-other-fields-
  unchanged; we'd need a parallel encoding.
- **New-mut-ref mode** (`UnaryOp::MutRefCurrent` / `MutRefFuture`). The
  current MVS handles legacy-mode `VarAt(p, Pre)` only. Migrated functions
  use `MutRefCurrent`/`MutRefFuture` UnaryOps instead. Would need
  parallel handling at the rewrite site.

### #56 follow-ups

The caller-side MVS for trait method calls landed (DynamicResolved
+ Static/Dynamic same-crate paths via `walk_call`'s standard
inlining). Remaining sub-tasks:

- **Impl-specific strengthening of `ensures`.** Currently
  `pick_spec_source` returns the trait method decl, so a
  caller never sees the impl's strengthened ensures (e.g.,
  trait says `r < 100`, impl says `r == 5` → caller sees
  only `r < 100`). Per-clause merge: at each call site,
  conjoin the trait's ensures with the impl's (already
  proven trait-implication-sound by Verus). Bounded work
  but invasive — touches the substitution map shape.
- **`is_trait_default = Some(true)`** (calls resolved to the
  trait's default impl, not a concrete impl). The default
  body uses `Self` as a parameter that needs additional
  substitution. Currently rejected with a clear error.
- **Cross-crate trait method decls.** When the resolved impl's
  `method` Fun isn't in fn_map (the trait lives in another
  crate), rejected at build time. Lifting requires the
  cross-crate spec-availability infrastructure (Phase 3
  work — `CrateDecls.lean` for trait method decls).
- **Truly dynamic dispatch through `dyn Trait`.** Currently
  works for same-crate trait method decls (falls through to
  existing fn_map lookup of `fun`), fails cross-crate.
  Same fix as above.

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
| `cargo test -p lean_verify --lib` | 114 | AST pp (precedence, tuples, indexing), `substitute` (shadowing, capture avoidance), `strip_span_marks`, `Wp` / `walk_obligations` / `contains_loc` / `lift_if_value` / `peel_value_position` / `match_single_let_bind`, type translation, sanity check scope tracking, `format_rust_loc`, lean_process |
| `cargo test -p lean_verify --test integration` | 7 | Tactus-prelude + Lean invocation end-to-end on hand-written Lean |
| `vargo test -p rust_verify_test --test tactus` | 217 | Full e2e: VIR → AST → Lean for proof fns + exec fns (all slices, source mapping, match automation, recursive datatypes, per-obligation theorems with AssertKind labels pinned, &mut at call sites, trait-method calls, bit-width matrix, control-flow combinations, lossy-accept paths, name-collision regression guard, assume warning, per-fn tactic override, tactus_usize_bound, HeightCompare, labeled break) |
| `vargo test -p rust_verify_test --test tactus_coverage` | 1 | Coverage assertion: expected VIR variants all hit by `walk_expr`/`walk_place` |
| `vargo build --release` (vstd) | 1530 | Regression guard: vstd proof library still verifies |

### Per-test isolation for Tactus output (`TACTUS_LEAN_OUT`)

`run_verus` in `tests/common/mod.rs` sets `TACTUS_LEAN_OUT` to `<test_input_dir>/tactus-lean` for every spawned subprocess. Without this, generated `.lean` files would land in the shared `<rust_verify_test target>/tactus-lean/test_crate/<fn>.lean` (because cargo's inherited `CARGO_TARGET_DIR` overrides the relative-CWD fallback in `lean_out_root`). Two tests defining a fn with the same name but different content would race in parallel runs, producing flaky failures whose root cause is invisible (one test's output overwrites the other's between Lean spawn and disk read). Per-test `TACTUS_LEAN_OUT` gives each test its own output tree.

Symptom of regression: same test fails on one cargo run and passes on the next; running it alone passes. Likely cause: the env-var setting got lost.

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
      tactus.rs                ← 217 end-to-end tests
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
# 217 end-to-end tests
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
