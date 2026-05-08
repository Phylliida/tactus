# Review pass — 2026-05-05 work

A 14-lens review of the code landed 2026-05-05: #98 (walk_children +
ScopeKind), #109 (mutual datatype SCCs + cross-fn cross-type
decreases), #126 (WpCtx + walk_loop direct tests), #111 (assert
by(bit_vector) routing), #130 (BitVec rendering + bv_decide). Files
in scope:

* `lean_verify/src/lean_ast.rs` — `walk_children` / `map_children`
  / `walk_pattern_children` / `map_pattern_children` / `ScopeKind` /
  `QuantifierKind` / `substitute_match_arm` / `substitute_quantified`
  / `map_binders`. Plus 12 new unit tests.
* `lean_verify/src/dep_order.rs` — `order_datatypes` / `walk_typ_paths`
  / `tarjan_scc_path` / `DatatypeGroup`.
* `lean_verify/src/to_lean_fn.rs` — `field_recursive_target` (renamed
  from `field_is_self_recursive`) / `height_fn_for_datatype` (now
  takes `scc_paths`) / `datatype_to_cmds` split into
  `datatype_decl_cmd` / `datatype_accessor_cmds` /
  `datatype_height_cmd` / `datatype_group_to_cmds` composer /
  single-variant accessor wildcard fix.
* `lean_verify/src/sst_to_lean.rs` — `Wp::AssertBitVector` variant /
  `OblCtx::wrap_no_hyps` / `ObligationEmitter::needs_bitvec_instances`
  / `ExecFnTheorems` struct / `walk_loop` direct tests / `WpCtx::new`
  tests / cross-type CheckDecreaseHeight shape-drift test.
* `lean_verify/src/to_lean_sst_expr.rs` — cross-type
  `CheckDecreaseHeight` per-side height-fn dispatch /
  `sst_exp_to_bit_vector_ast`.
* `lean_verify/src/generate.rs` — `collect_referenced_datatypes`
  helper / `BITVEC_INT_INSTANCES` constant / `bitvec_mode` flag on
  `krate_preamble`.
* `lean_verify/src/sanity.rs` — `Datatype` predefine in mutual block.
* `lean_verify/TactusPrelude.lean` — `tactus_bit_vector` macro.

Test additions: 277 → 292 e2e (+15), 146 → 160 unit (+14).

Two prior review-pass commits during the day already landed
findings (`b445785`, `cfa5fd4`, `70d8eed`); this REVIEW captures
the state as-of end-of-day, applying every lens to the resulting
code.

---

## 1. Linus hat

*Clever abstractions, defensive code, flag soup, lies about purity.*

**Findings:**

1. **`tarjan_scc_path` duplicates `tarjan_scc`** (`dep_order.rs:303-...`).
   Same algorithm, ~60 lines, keyed on `&Path` instead of `&Fun`. The
   inline comment justifies the duplication ("Rust's iter-borrow rules
   around generic Eq+Hash keys with lifetime params get unwieldy fast
   for a 60-line algorithm"). Honest call. **Skip** — the duplication
   is bounded and the comment locates the trade-off.

2. **`obl.wrap` and `obl.wrap_no_hyps`** in `sst_to_lean.rs:883,902`
   differ only in one match arm (`CtxFrame::Hyp`). Could share via a
   closure parameter, but two methods is more readable for the two
   call patterns we have. **Skip.**

3. **`ExecFnTheorems` struct** (`sst_to_lean.rs:540-543`) is just
   `(Vec<Theorem>, bool)`. Tuple would work; struct is self-
   documenting at call sites. **Right-way over Linus** — keep.

4. **`needs_bitvec_instances: bool`** on `ObligationEmitter`. Mutable
   state set by one walker arm, read by the constructor's caller.
   This flag is what FP would flag — see lens 2.

**Triage:** No fix-now items.

---

## 2. FP lens

*Mutable that could be immutable; stateful that could be a parameter.*

**Findings:**

1. **`ObligationEmitter::needs_bitvec_instances`** mutable flag
   (`sst_to_lean.rs:933`). Imperatively set during walk; alternative
   would be a post-hoc scan of `emitter.out` text for "BitVec.ofInt".
   The flag is cleaner — single source of truth, set at the place
   where the decision is made (the walker arm). **Skip** — the
   imperative flag matches the imperative walk it lives inside.

2. **`needs_bitvec_instances` cross-fn boundary**: set in
   `walk_obligations`'s `Wp::AssertBitVector` arm, read at the end of
   `exec_fn_theorems_to_ast` and propagated to caller via
   `ExecFnTheorems`. Trans-function mutable state. Acceptable given
   the imperative shape of the walker.

**Triage:** No fix-now items.

---

## 3. Comprehensive coverage

*What code paths have no test?*

**Findings:**

1. **`walk_call` direct unit test still missing** (#126 partial).
   Synthetic FunctionX is genuinely heavy; e2e covers it. Documented
   in DESIGN.md "User-facing features not tested." **Skip** — already
   triaged in #126's commit.

2. **Datatype SCCs of size > 3 not explicitly tested.** Tarjan
   generalizes; documented in DESIGN. **Skip.**

3. **AssertBitVector inside an `if`-branch / loop body / nested in
   another assert.** The current bit_vector tests place the assert
   directly in a fn body. Different surrounding contexts go through
   the same `Wp::AssertBitVector` walker but the OblCtx accumulation
   differs — `wrap_no_hyps` drops the surrounding if's branch hyp,
   which is what we want, but no test pins this. **File** — would
   help confirm the wrap_no_hyps choice doesn't lose info we'd
   actually need.

4. **AssertBitVector with a `requires` clause** (non-empty `req_conj`).
   The current tests all have empty requires. The walker has a
   `matches!(req_conj.node, ExprNode::LitBool(true))` collapse for
   the empty case; the non-empty path emits `req_conj → ens_conj` but
   isn't exercised. **File.**

5. **AssertBitVector with mixed bit widths** (e.g., `(x : u8) ^ (y as u8)`
   where `y : u32`). `sst_exp_to_bit_vector_ast` matches the type's
   `IntRange::U(n)` per-variable; mixed widths in one expression go
   through unchanged but Lean's BitVec ops require homogeneous widths
   so the goal would fail elaboration. Verus probably normalizes
   widths upstream, but unverified. **File** — minor; likely Verus
   rejects most cases upstream.

6. **HXor Int instances on negative Ints.** Wonky-but-total
   semantics documented. Not tested directly because Tactus only
   emits on bounded-non-negative Ints; if a future Tactus path emits
   on negative Ints, the wrong values pass typecheck. The "what if
   this assumption breaks" test would construct a goal with a
   negative-Int `x ^^^ y` and verify it's still total (no panic).
   **File** — defensive.

7. **3+ AssertBitVector statements in one fn** beyond the 2-statement
   `and_or_comm` test. Multiple Assumes from Verus's pre-injection
   stack on each other; the walker runs once per AssertBitVector;
   `wrap_no_hyps` drops accumulated hyps each time. Looks fine but
   unverified. **Skip** — low value.

8. **`order_datatypes` / `collect_referenced_datatypes` direct unit
   test.** Currently exercised only via e2e. Synthetic KrateX
   fixture is now feasible (we have `empty_krate` from #126). **File.**

**Triage:** Items 3, 4, 6, 8 worth filing for a follow-up coverage
session. None block correctness today; e2e covers the core paths.

---

## 4. Upstream-brittleness

*What breaks silently if Verus changes X?*

**Findings:**

1. **`anonymous_closure` prefix string** in
   `generate.rs:collect_referenced_datatypes` and the prior closure-
   filtering site. If Verus changes the synthesized-closure path
   prefix, our filter silently misses (or wrongly includes) the
   closure datatypes. **Mitigation:** the prefix is centralized in
   one helper now; one edit site if Verus changes. No shape-drift
   test — the symptom would surface as an `Inhabited`-derive failure
   on zero-variant inductives. **File** — could add a shape-drift
   test.

2. **Verus's `ast_to_sst` pre-injecting `Assume(ens)` before
   `AssertBitVector`** is the load-bearing reason we need
   `wrap_no_hyps` AND the conditional Int-bitwise instances. If
   Verus changes the pre-injection (e.g., drops the Assume now that
   AssertBitVector publishes its ensures itself), our
   `wrap_no_hyps` becomes unnecessary and the Int instances go
   unused. Detecting this drift: comment in our codepath mentions
   the upstream behavior explicitly, but a shape-drift test
   constructing a synthetic SST with AssertBitVector + checking
   the WP tree shape would lock it. **File.**

3. **Lean core's `Lean.Elab.Tactic.BVDecide` import path** is
   load-bearing for #130's bv_decide. If a future Lean toolchain
   moves this module (e.g., to a Mathlib-only path), our
   `bitvec_mode` preamble's import fails. **File** — pinned tests
   would catch this on toolchain bump, but a unit test that asserts
   the import string matches an expected value would surface earlier.

4. **`Mathlib.Data.BitVec` as the source of `BitVec.xor_comm` etc.**
   If Mathlib renames or relocates these lemmas, the
   `tactus_bit_vector` simp-fallback rungs break. The bv_decide rung
   doesn't depend on these so the breakage would be isolated to
   bv_decide-can't-discharge edge cases. **Skip** — bv_decide is the
   primary path; simp lemmas are graceful-degrade.

5. **`StmX::AssertBitVector` field shape** (`requires`, `ensures`).
   Verus could change to a different encoding (e.g., a single
   `query: Exp` field). Our build_wp arm destructures via
   `StmX::AssertBitVector { requires, ensures }` — adding a field
   would compile-error (good) but renaming would silently miss
   matches if not exhaustive. We use exhaustive destructure (no `..`).
   **No finding.**

6. **`field_recursive_target` peels via `peel_typ_wrappers`** which
   handles `Boxed` / `Decorate`. If Verus adds a new transparent
   wrapper, the SCC graph misses cross-type references through it.
   `peel_typ_wrappers` is shared with the height-fn emission so the
   bug would manifest as broken height fns first. **No finding** —
   centralized helper limits blast radius.

**Triage:** Items 1, 2, 3 worth filing for shape-drift tests. None
urgent — they're "future-rebase landmines" not active issues.

---

## 5. Documentation / deferrals

*What's landed but not documented? Stale comments?*

**Findings:**

1. **DESIGN.md edge case catalog** — already updated comprehensively
   in commit `929eb34` (today). Covers single-variant enum bug fix,
   ScopeKind::Other miscategorization, AssertBitVector non-trivial
   shapes, HXor Int wonky semantics. **Done.**

2. **HANDOFF.md afternoon session entry** — comprehensive; covers
   all of today's afternoon work. **Done.**

3. **`DESIGN.md` "Rejected statement-level forms"** still lists
   `StmX::AssertQuery` with `AssertQueryMode::BitVector` as
   rejected. That's the OLDER Verus path, unreachable post-#111
   because Verus's ast_to_sst converts to dedicated
   `StmX::AssertBitVector`. The fallback Err arm in
   `sst_to_lean.rs:3444` still exists as defensive code. **File** —
   the doc entry could note "AssertBitVector path supersedes; this
   arm is defensive."

4. **Sanity.rs Mutual arm comment** mentions Datatype predefinition
   for #109 but doesn't explain WHY (cross-type field references in
   the inductive declarations). Easy to misread as redundant. **Fix
   now** — a sentence of context.

5. **`obl.wrap_no_hyps` doc** says "see Wp::AssertBitVector for
   rationale" — good cross-reference but reader has to navigate.
   Self-contained doc would be friendlier. **Skip** — the cross-
   reference is fine.

6. **`BITVEC_INT_INSTANCES` constant doc** explains conditional
   emission rationale. Good.

**Triage:** Item 4 worth fixing now. Item 3 worth filing.

---

## 6. Reasoning-clarity

*A-month-from-now readability.*

**Findings:**

1. **`bitvec_mode: bool` parameter on `krate_preamble`** is a
   positional bool. Could be an enum (`PreambleMode::Standard` /
   `PreambleMode::BitVector`) for clarity at call sites. Trade-off:
   adds a type. The callsites are 2 — readability win is small.
   **Skip.**

2. **`ScopeKind` section header comment** in `lean_ast.rs` is long
   (~50 lines). Walks through soundness convention, why two helpers,
   alternatives considered. Could be split into a brief overview at
   the section header + detailed prose at each consumer. **Skip** —
   the centralized doc is more discoverable.

3. **`sst_exp_to_bit_vector_ast` rejection arm** uses
   `format!("expression shape {:?} ...", std::mem::discriminant(&e.x))`
   — the discriminant is a numeric ID, not the variant name. A user
   seeing this error gets a meaningless number. **Fix now** — use a
   helper that names the variant.

4. **`exec_fn_theorems_to_ast` returns `ExecFnTheorems`** — the
   field name `theorems` is fine, but `needs_bitvec_instances` is a
   mouthful. Could be `bitvec_used`. **Skip** — explicitness wins.

5. **`Wp::AssertBitVector` field `rust_loc: String`** — the type is
   "any string", but it's specifically a formatted "path:line:col".
   Could be a typed `RustLoc` (already noted as a future-applications
   candidate elsewhere in DESIGN). **Skip** — DESIGN-level decision,
   not for this review.

6. **The `_α<N>` suffix from #116 is documented in `expr_shared.rs`
   reserved-identifier-conventions list.** Verified. **No finding.**

7. **`tactus_bit_vector` macro's tactic ladder** — 6 alternatives.
   The order matters (bv_decide first, then decide, then simp_all).
   Comments explain. **No finding.**

8. **`obl.wrap_no_hyps` doc** mentions the BitVec scenario but
   doesn't say *why* dropping hyps is sound. The reasoning: the
   bit_vector solver's contract is "given the user's `requires`,
   prove the `ensures`" — the surrounding ctx's hyps are
   incidentally true at this site but not guaranteed to be true in
   the bit_vector encoding. **Fix now** — add a sentence on the
   soundness reasoning.

**Triage:** Items 3 and 8 worth fixing now. Items 1, 2, 4, 5 skip.

---

## 7. Error-message quality

*Convention: (a) what did the user write, (b) workaround, (c) tracked?*

**Findings:**

1. **`sst_exp_to_bit_vector_ast` rejection** (`to_lean_sst_expr.rs`):
   "expression shape {:?} not yet supported inside `by(bit_vector)` —
    use `assert(P) by { ... }` with a custom Lean tactic for non-
    trivial shapes (#130)". Has all three (variant name in {:?} —
   though see lens 6 finding 3, surface syntax via `by(bit_vector)`,
   workaround via `by { ... }`, task ref #130). **Almost good** —
   just needs the variant name fix from lens 6.

2. **`tactus_bit_vector` failure message**: "tactus_bit_vector:
   could not discharge — try `assert(P) by { … }` with a Lean tactic
   instead". (a) implicit (the user wrote `by(bit_vector)`), (b)
   explicit, (c) no task ref but shouldn't need one. **Good.**

3. **`build_wp` AssertBitVector errors** (passing through
   `Validated::check`): inherit from `sst_exp_to_ast_checked` which
   has its own message convention. **No finding.**

4. **HXor Int instances** have an inline comment naming what would
   be needed if Tactus ever emits on negative Ints. Not an error
   message but a future-investigation pointer. **Good.**

**Triage:** Lens 6's variant-name fix covers this lens too.

---

## 8. Identifier-conventions

*Reserved names; gensyms; documented in single source.*

**Findings:**

1. **`tactus_bit_vector` macro name** follows the `tactus_<name>`
   user-visible-tactic convention from `expr_shared.rs`. **Good.**

2. **`needs_bitvec_instances` field**, `BITVEC_INT_INSTANCES`
   constant, `bitvec_mode` parameter — internal, naturally named, no
   collision risk. **No finding.**

3. **`BitVec.ofInt` calls** emitted via `LExpr::var_lit("BitVec.ofInt")`.
   Dotted name resolves natively in Lean (see sanity-allowlist
   convention). **Good.**

4. **`x_bv` synthetic names** — not used (we don't introduce fresh
   BitVec witnesses; bv_decide handles parameterized terms). **No
   finding.**

5. **Test helpers `mk_test_path` / `typ_datatype` / `empty_krate`
   / `empty_func_check` / `old_exp` / `loop_inv`** are inside test
   modules with no production-side risk. Names are descriptive. **Good.**

**Triage:** No findings.

---

## 9. Simplify (reuse / quality / efficiency)

*Could it use existing helpers? Hidden state? Missed early-exit?*

**Findings:**

1. **`bv_exp_to_node` duplicates rendering for Var/Const/BinaryOp/UnaryOp**
   from `sst_exp_to_ast_checked` (`to_lean_sst_expr.rs`). The Var arm
   has a bit_vector-specific tweak (BitVec.ofInt wrap); the rest is
   identical. Could share via a mode parameter, but that'd thread
   bv-mode through every arm of the main renderer. **Skip** — the
   focused-renderer approach scoped the change cleanly. If the
   bit_vector renderer grows, revisit.

2. **`collect_referenced_datatypes`'s `path_to_dt` map** and
   `order_datatypes`'s `dt_by_path` map have the same shape with
   slightly different filters. Considered extracting a shared
   `is_emittable_datatype` predicate; trade-off too small. **Skip.**

3. **`map_binders` helper** in `lean_ast.rs:866` is used in three
   places (Lambda/Forall/Exists arms of `map_children`). Good
   factoring. **No finding.**

4. **`substitute_match_arm` factoring** done in commit `b445785`
   (today's earlier review pass). Already addressed. **No finding.**

5. **`HXor`/`HAnd`/etc. instance bodies** all follow the same shape:
   `fun a b => ((a.toNat OP b.toNat : Nat) : Int)`. Could macro-
   define them but five instances and Lean instance syntax is verbose.
   **Skip.**

6. **`tactus_bit_vector` ladder** has explicit `intros <;> X` and
   bare `X` rungs paired. Could collapse via `(try intros) <;> X`.
   **Skip** — explicit pairing is more debuggable.

**Triage:** No fix-now items.

---

## 10. Right-way

*Most direct expression of meaning?*

**Findings:**

1. **`bitvec_mode: bool` flag** on `krate_preamble` is the right
   shape for "conditionally emit one of two preamble variants." An
   enum would be more typeful but the binary nature is explicit.
   **Right way.**

2. **`Wp::AssertBitVector` carrying pre-rendered LExprs (req_conj,
   ens_conj, rust_loc) rather than `Validated<'a>`**. The rendering
   happens at build time because the goal is constructed from a list
   of SST exps, not borrowed from one. LExpr-direct matches `Wp::Hyp`'s
   pattern. **Right way.**

3. **`bv_decide` as the primary tactic** rather than building our
   own bridging machinery. Lean core has the right tool; using it
   directly is the right way. **Right way.**

4. **Conditional preamble emission** rather than always-emit-with-
   skip-if-unused. Other Tactus generated files don't pay the cost,
   and `Mathlib.Data.BitVec`'s simp lemmas don't affect unrelated
   proofs. **Right way.**

5. **`ScopeKind` enum + `scope_kind()` method** rather than the
   prior `_ =>` fallthrough convention. Forces positive
   categorization. **Right way.** (Already landed via review pass
   1 of #98.)

6. **`obl.wrap_no_hyps`** is the right shape for "drop hypothesis
   frames but keep binders/lets." Matches Verus's bit_vector queries
   running with a clean context. **Right way.**

7. **`field_recursive_target` returning `Option<&Path>`** rather than
   `bool` — the path is what the height fn emitter needs to dispatch
   correctly for cross-type recursion. **Right way.**

**Triage:** No findings.

---

## 11. Rust-antipattern

*Arc/RefCell/clones/Box<dyn> where direct refs would work?*

**Findings:**

1. **`Box<Wp<'a>>` recursion** in `Wp::AssertBitVector.body` —
   necessary for self-referential enum. Standard Rust pattern.
   **No finding.**

2. **`String` for `rust_loc`** in `Wp::AssertBitVector` — could be
   `&'a str` borrowed from the source span, but the span is mediated
   through `format_rust_loc()` which produces an owned String. The
   ownership matches the upstream API. **No finding.**

3. **`HashMap`/`HashSet` allocations** in `collect_referenced_datatypes`
   are O(n) once per fn-verification — not on a hot path. **No
   finding.**

4. **`sst_exp_to_bit_vector_ast` returns `Result<LExpr, String>`** —
   the String is the error message. Standard error pattern. **No
   finding.**

5. **`ExecFnTheorems` struct field access** is by value (`exec_fn.theorems`).
   No clone, no Arc. **No finding.**

**Triage:** No findings.

---

## 12. Edge-case

*Silent acceptances of cases we don't handle?*

**Findings:**

1. **`sst_exp_to_bit_vector_ast`'s catch-all rejection** uses
   `std::mem::discriminant(&e.x)` and explicitly errors. Good — not
   a silent accept. **No finding.**

2. **`order_datatypes` with empty `referenced_datatypes`** — returns
   empty Vec. Walked the code; no panic, no degenerate behavior. **No
   finding.**

3. **`Wp::AssertBitVector` with empty `ensures`** — `and_all([])`
   produces `LitBool(true)`. The walker emits a theorem with goal
   `True` (or `req → True`). `bv_decide` closes it trivially. Edge
   handled. **No finding.**

4. **`Wp::AssertBitVector` with empty `requires` AND empty `ensures`**
   — both `LitBool(true)`. The collapse check fires (req is True),
   goal becomes `True`. Trivial theorem emitted. **No finding.**

5. **`field_recursive_target` for `Dt::Tuple`** — the match's `_ =>
   None` arm catches it. Tuples can't be in an SCC because they have
   no path. **No finding.**

6. **`order_datatypes` with a single self-recursive datatype** —
   Tarjan returns `Single(dt)` because the self-loop doesn't make a
   size-2 SCC. Test coverage via existing `test_exec_call_recursive_datatype_termination`.
   **No finding.**

7. **`bv_decide` timeout / failure**. `bv_decide` invokes a SAT
   solver which can be slow for high bit-widths (u128) or complex
   goals. The `tactus_bit_vector` ladder has fallback rungs (decide,
   simp_all), but if all fail the `fail` rung fires with a clear
   message. **No finding** — well-handled.

8. **HXor Int instances on `Int.toNat` for negative inputs** — the
   instance returns `0 OP b.toNat` for negative `a`. Wonky but total.
   Documented as soundness trade-off. **No finding** (file separate
   coverage if desired — see lens 3 finding 6).

9. **AssertBitVector inside a closure body**. Untested. The
   `Wp::ClosureBody` wraps the body in `∀ p : T, h_p_bound → ...`;
   if an AssertBitVector appears inside, the BV-mode goal would have
   the closure's `p` as a free variable. Should work via bv_decide;
   unverified. **File** — coverage gap.

**Triage:** Item 9 file for coverage. Others pass.

---

## 13. Typed-invariant

*Runtime checks that could be type-system-enforced?*

**Findings:**

1. **`ExecFnTheorems` carries `(Vec<Theorem>, bool)` together** —
   the type guarantees the flag and theorems came from the same
   emission. Can't get out of sync. **Right way.**

2. **`Wp::AssertBitVector` carries pre-rendered LExprs** — the type
   guarantees the rendering already happened. No runtime check
   needed at the walker level. **Right way.**

3. **`ScopeKind` enum** (#98 follow-up) lifts the binder-soundness
   convention from doc to type. New `ExprNode` variant compile-errors
   in `scope_kind()`. **Right way.**

4. **`needs_bitvec_instances` is a runtime flag**. Could it be type-
   level? Conceptually: the file's emission style depends on a
   property derivable from the body. Type-level encoding would need
   indexed types or const generics. Trade-off too high. **Skip.**

5. **`bitvec_mode: bool` parameter** on `krate_preamble`. Could be
   an enum with associated data (`Standard` / `BitVector`). For two
   variants, the bool is fine. **Skip.**

6. **`obl.wrap` vs `obl.wrap_no_hyps`** as two methods is a
   poor-man's typestate (caller chooses which is appropriate). A
   newtype `BitVectorObl(OblCtx)` with only `wrap_no_hyps` available
   would be more typeful but adds friction. **Skip** — bool-ish
   discrimination via method choice is fine for two cases.

**Triage:** No fix-now items.

---

## 14. Regression-test

*Every fix has a test for the bug class?*

**Findings:**

1. **Single-variant non-eponymous enum accessor wildcards bug** (fixed
   today) — pinned by `test_exec_single_variant_non_eponymous_enum`.
   **Pinned.**

2. **Cross-type CheckDecreaseHeight per-side dispatch** — pinned by
   the unit test `check_decrease_height_cross_type_shape_pinned` AND
   the e2e `test_exec_cross_fn_scc_cross_type_decreases`. Both
   directions covered. **Pinned.**

3. **#98 walk_children helpers** — `map_children_identity_roundtrips_all_variants`
   pins per-variant fidelity. `walk_children_counts_match_expected`
   pins child counts. **Pinned.**

4. **#109 mutual SCC inductive emission** — `test_exec_mutually_recursive_datatypes`.
   **Pinned.**

5. **#109 cross-type recursive height fns** — `test_exec_call_recursive_over_mutual_datatype`.
   **Pinned.**

6. **#111 AssertBitVector basic routing** — `test_exec_assert_bit_vector_concrete`
   + `_false`. **Pinned.**

7. **#130 BitVec rendering** — `_xor_comm` + `_xor_self` + `_xor_assoc`
   + `_and_or_comm`. Cover commutativity, identity, associativity,
   multi-statement. **Pinned.**

8. **`scope_kind` categorization** — `scope_kind_categorizes_each_variant`
   pins per-variant assignment. **Pinned.**

9. **`Pattern::Binding` shadowing in substitute** — `match_arm_binding_pattern_shadows`
   + `capture_alpha_renames_match_binding_pattern`. **Pinned.**

10. **SpanMark metadata preservation through substitute** —
    `substitute_preserves_span_mark_metadata`. **Pinned.**

11. **walk_loop init-emission filter** — `walk_loop_skips_init_for_ensures_kind_invariant`
    + `walk_loop_emits_init_for_at_entry_invariant`. **Pinned.**

12. **WpCtx::new error propagation** — three direct tests covering
    happy path + reject in reqs + reject in ens. **Pinned.**

**Bug classes NOT pinned:**

- **Wrong-but-explicit ScopeKind miscategorization** (e.g., a
  contributor labels a binder as `Other`). Type system can't catch.
  Documented; coverage tests only catch existing variants.
- **Verus pre-injection shape drift** (Assume(ens) before
  AssertBitVector) — see lens 4 finding 2.
- **Conditional bitvec_mode emission correctness** for files that
  DON'T use bit_vector. We have e2e tests for both (bit_vector files
  pass; others remain unchanged since #130 only adds conditional
  imports). Could add an explicit "no bit_vector → no bitvec
  preamble" assertion. **File.**

**Triage:** Items in "NOT pinned" worth filing for follow-up.

---

## Summary

**Fix now (3 items):**

* Lens 5 finding 4 — Sanity.rs Mutual arm comment: explain Datatype
  predefinition reason.
* Lens 6 finding 3 — `sst_exp_to_bit_vector_ast` rejection: replace
  `std::mem::discriminant` with a helper that names the variant.
* Lens 6 finding 8 — `obl.wrap_no_hyps` doc: add soundness reasoning
  sentence.

**File for follow-up (8 items):**

* Lens 3 findings 3, 4, 6, 8 — coverage gaps (AssertBitVector in
  branches/loops/closures, with non-empty requires, on negative Ints,
  direct `order_datatypes` test).
* Lens 4 findings 1, 2, 3 — shape-drift tests for upstream changes
  (closure prefix, Verus pre-injection, BVDecide module path).
* Lens 5 finding 3 — DESIGN entry for AssertQuery::BitVector being
  defensive.
* Lens 14 — bitvec_mode-not-emitted assertion test.

**No findings (5 lenses):**

* Lens 7 (subsumed by Lens 6 fix), Lens 8, Lens 11, Lens 13, Lens 10
  (all positive — code is right-way).

**No fix-now items in 6 lenses; 3 fix-now in 2 lenses.** Code is in
good shape — the structural locks (`ScopeKind`, exhaustive matches,
typed enum dispatch) are doing their job; the documentation is
comprehensive after today's catalog updates; the test coverage is
solid for the explicitly-tested paths.

The "file for follow-up" items represent known-unknowns —
documented gaps, not silent acceptances. Future sessions can pick
them off as they become motivated by user-encountered cases.

---

## Process notes

This review took ~30 minutes of reading + ~30 minutes of writing. It
surfaced 3 fix-now items (small) and 8 file-for-later items (none
urgent). Compared to the in-flight review passes during the day
(`b445785`, `cfa5fd4`, `70d8eed`), this end-of-day review found
fewer high-impact issues — consistent with the discipline working:
each landing got reviewed before the next started.

The bug-class with the highest residual risk is the "wrong-but-
explicit ScopeKind miscategorization." The type system catches
forgetting to categorize, but a contributor *positively lying* still
compiles. Mitigation today: comprehensive `scope_kind_categorizes_each_variant`
test, plus DESIGN-level documentation. A future session that adds a
new binder variant should add a corresponding test for that variant's
scope semantics; the test is the only catch for the wrong-but-explicit
case.
