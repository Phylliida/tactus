# `--lean-all-proofs` follow-on arcs (post B1–B4) — spec

**Date:** 2026-07-10
**Status:** F1 IMPLEMENTED & COMMITTED (`25970a5`) — validated on the worst-offender file
(12 error blocks → 0 parse errors) + unit tests + both gates. F2a IMPLEMENTED & COMMITTED
(`2e203dc`) — scheduling half pinned by disable-repro (`failed to prove termination`),
plus a second half found during implementation: the companion's canned `⟨⟨_,_⟩,_⟩` proof
only matched one of TWO attested renderings of the axiom's chained-comparison hypothesis
(let-bound left-assoc vs bare right-assoc via `Multi(Chained)`/`and_all`) — replaced with
bare `omega`, which closes every attested shape. The associativity divergence between the
two chained-op rendering paths is a new F6-family unification candidate. F2b PINNED &
DEFERRED (see section). Along the way: fixed a pre-existing B1a-era regression — recursive
datatype declarations rendered their self/sibling references root-anchored (`Unknown
identifier` during elaboration; 8 e2e tests failing at HEAD before today's arcs) — via
`with_self_decls` over the SCC in `datatype_decl_cmd` + a `self_name` field on the
`Datatype` AST for IndexedInductive ctor result types. F3–F7 still spec-only.
**Scope:** everything left on the board after `DESIGN-lean-all-proofs-bugs.md` B1–B4 landed
(`dbc77e5`, `00534c9`, review round `2e43a39`), **except B5** (typed-spine `.deref` arc —
its own doc/arc, per the bugs doc) and except the closer/tactic changes themselves
(policy = `DESIGN-transparent-automation.md`). Baseline numbers are §10.1 of
`DESIGN-lean-all-proofs.md`: 8,950 errors, 253/1,338 codegen'd fns pass.

---

## TL;DR

| # | Item | Errors today | Fix shape | Size |
|---|---|---:|---|---|
| F1 | pretty-printer `let`-continuation indent | 39 parse errors | indent-aware `;\n` in `ExprNode::Let` | XS–S |
| F2a | seq measure companion dep-walk gap | 68 | force `axiom_seq_subrange_len` into the axiom set when `drop_first`/`drop_last` emits | S |
| F2b | `sizeOf (if …)` / Int-abs measures | 13 | pin goal shapes; likely one `split <;> omega` rung | XS, P2 |
| F3 | multi-element `seq![a,b]` / array literals | 142 rejections + 1,145 mistypes | render `Vector` literals; unify both paths | M |
| F4 | `StmX::DeadEnd` lowering | 1,267 rejections | `Wp` scope node reusing the `ClosureBody` shape | M |
| F5 | check.sh `--emit-lean` hygiene | (gate honesty) | one line | XS |
| F6 | deferred altitude refactors (5 items) | 0 | fold into adjacent arcs, see table | S–M each |
| F7 | the auto bucket | 5,987 goals | measurement + per-cluster policy, NOT a code fix | own arc |

Recommended order: **F1 → F2a → F3 → F4** (signal cleanup first, then the two coverage
features), F5 when experimentation settles, F6 opportunistically alongside the arc named in
its row, F7 as its own arc after F3+F4 stabilize the population (both grow it — that's the
point). Full-crate re-measure once after F4, not per-fix.

---

## F1. Pretty-printer `let`-continuation indent (39 × `unexpected token '('; expected 'else'`)

**Mechanism (pinned in code, not yet repro'd).** `ExprNode::Let` printing
(`lean_pp.rs:689–696`) emits the body as `";\n    "` — a newline plus a **hardcoded
4-column indent** — regardless of the current column. It is the only newline source in term
printing, matching the review-round symptom ("application continuation dedented below its
enclosing `let` in an if-branch"). When the `let` sits inside an if-branch (or any context)
at column > 4, the body lands **left of** the `let` keyword; Lean's whitespace-sensitive
parser closes the enclosing construct early and the next token — typically the `(` opening
the continuation — errors with `expected 'else'`. 136 occurrences pre-B1–B4, 39 post
(the fixes changed emitted shapes, not this bug).

**Fix.** Capture the column at which the `let` keyword starts (cursor position before
pushing `"let "` — `out.len() - line_start`, same computation as the existing
`current_line_indent` helper at `lean_pp.rs:195`, generalized to mid-line) and emit
`;\n` + that many spaces. Body aligned exactly under `let` is always legal Lean.

- **Rejected: same-line `; ` (no newline).** Always parses, but produces very long lines —
  a real cost, since emitted Lean is what we debug against.
- **Rejected (for now): threading an indent parameter through `write_expr`.** The
  principled fix, but touches every arm of a shared printer for one bug. If a second
  indent-sensitive symptom appears, revisit.

**Watch:** the printer is shared with exec-fn emission — gate by error locations, per
`reference_tgt_gate_baseline_errors`.

**Acceptance:** the 39 `unexpected token '('` errors → 0 on a britton-module re-run; unit
test = a let-chain inside an if-branch nested under another `let` (the emitted `.lean`
must parse, i.e. the theorem elaborates or fails only in the closer).

---

## F2. Termination residual (81 errors)

### F2a. Companion dep-walk gap (68)

**Mechanism (already diagnosed, §10.1).** The B3 measure companion
(`generate.rs:1248 seq_measure_companion_cmd`) is gated on `axiom_seq_subrange_len` being
part of the emission (`bc_lemma_funcs`) — review finding #7 made that gate correct, since
the canned proof cites the axiom by name. But files whose own broadcast dep-walk never
pulls the axiom in silently get **no companion**, and every fn recursing through
`drop_first`/`drop_last` in that file fails termination exactly as pre-B3.

**Fix.** Make the companion's citation a real dependency edge: when the emission set
contains `Seq.drop_first`/`Seq.drop_last`, force-add `seq.axiom_seq_subrange_len` to the
axiom set before ordering (the def's group is already ordered after the axiom's deps, per
the comment at `generate.rs:1194–1198`, so no ordering change — only set membership).
Edit site: where `bc_lemma_funcs` is assembled for the emission, not inside
`seq_measure_companion_cmd` (keep the finding-#7 gate as a backstop; it becomes
dead-in-practice rather than load-bearing).

**Interaction with F6-1** (broadcast axioms as real `EmitStep`s): if F6-1 lands first, this
is a normal dep edge and F2a is one line. It won't — so land F2a as the special case and
fold it in when F6-1 happens. Note the special case in a comment pointing here.

**Acceptance:** termination family 81 → ≤13 crate-wide; zero new axioms (the companion is
a theorem; the axiom being force-added is one the crate's vstd surface already stipulates
— confirm it appears in the axiom-closure report unchanged, `DESIGN-axiom-closure-check.md`).

### F2b. `sizeOf (if …)` / Int-abs measures (13) — PINNED 2026-07-10, deferred

Shapes pinned from the post-fix log — exactly two, both `sizeOf` over an **Int-typed
measure** (Lean wraps non-Nat `termination_by` values in `sizeOf`):
`sizeOf (↑(len w) - (from + 1)) < sizeOf (↑(len w) - from)` (Int subtraction) and
`sizeOf (if 0 ≤ t then t else -t)` (Int-abs). A rung can't close these: `sizeOf (t : Int)`
unfolds to raw `Int.rec` (opaque to omega, verified in scratch), and the natAbs bridge is
asymmetric (`sizeOf = natAbs + 1` for nonneg, `= natAbs` for negSucc) — a bespoke bridging
lemma, not a tactic.

**Right fix (deferred, not a rung):** emit Int-typed `termination_by` measures wrapped in
`.toNat` — goals become `(e').toNat < (e).toNat`, which omega closes natively given the
branch guards already in the decreasing_by context (the same guards that make the sizeOf
goal true; Verus proved the measure nonneg + decreasing on the Z3 side). Touches the
termination_by emission (`to_lean_fn.rs` / `lean_pp.rs:303–352`), so it's a small focused
arc, not a companion to F2a. 13 goals; P2.

---

## F3. Multi-element `seq![a, b]` / array literals (142 rejections + 1,145 List/Vector mistypes)

Now the **largest translator-bug family** (the choose family's successor). Two halves that
are the same fix on two paths — mirror of B2's unify-the-paths move.

**Known mechanism.** Verus `[T; N]` renders as Lean core `Vector T N`
(`to_lean_type.rs:198`), but array *literals* render as `ExprNode::ArrayLit` → `[a, b, c]`
(`lean_pp.rs:774`) — a **List** literal. Type mismatch wherever the expected type is the
array type. The observed `{ deref := [a, b, c] }` shape says the literal typically sits
inside a `Tactus.*` single-field wrapper ctor (`TactusPrelude.lean:98–114`), i.e. vstd's
`seq!` lowers through a boxed/ref'd array; the wrapper ctor is fine, the inner literal isn't.

- **F3a — SST path**: `ExpX::ArrayLiteral` is rejected outright
  (`to_lean_sst_expr.rs:1349`) — this is the 142 codegen rejections. Implement it.
- **F3b — VIR path**: `ExprX::ArrayLiteral` renders the wrong literal form
  (`to_lean_expr.rs:798`) — this is the 1,145 mistypes (previously *hidden behind* the
  F3a rejections; §10.1 exposed them).

**Fix.**
1. **Pin first** (half a day): 5-line repro `proof fn f() { let s: Seq<int> = seq![1int, 2int]; }`
   through `--emit-lean`; read the emitted Lean and the SST shape. Two things to confirm:
   the exact wrapper nesting (which `Tactus.*` ctor), and **why single-element `seq![x]`
   already works** — there is no len-1 special case in either renderer, so the single-element
   form must lower through a different vstd path entirely. Knowing which path tells us
   whether fixing the literal also needs a corresponding `Seq`-construction axiom/def to
   already be in the preamble (it should be — single-element works — but confirm).
2. **Render a Vector literal**: one shared helper (new home: `expr_shared.rs`, next to
   `ctor_node`) used by both paths — either `#v[a, b, c]` (Lean core Vector-literal syntax;
   confirm available on the pinned 4.25.0 toolchain) or the anonymous-ctor fallback
   `⟨#[a, b, c], rfl⟩` (`Vector.mk` array + length proof — `rfl` closes it for literals,
   lengths are concrete). Prefer `#v[…]` if it elaborates: it's what a Lean user writes and
   keeps the printer trivial (`ArrayLit` grows a `vector: bool` flag or a sibling node).
3. **Keep `ExprNode::ArrayLit` as-is for genuine List positions** (`Primitive::Slice` →
   `List`, `to_lean_type.rs:199`) — the fix must dispatch on the literal's SST/VIR typ, not
   replace the node globally.

**Acceptance:** 142 rejections → 0; the 1,145 List/Vector mistypes → 0; `m4_qpow`'s six
`seq![a,b]`-rejected lemmas codegen (parent doc §5); repro test with 2- and 3-element
literals in both spec-fn-body (VIR) and proof-obligation (SST) position.

---

## F4. `StmX::DeadEnd` lowering (1,267 rejections — ~90% of the codegen gap)

**Semantics (from the desugar, `vir/src/ast_to_sst.rs:~2270–2316`).**
`assert(P) by { proof }` / `assert forall … by { … }` desugars to

```
DeadEnd(Block([ Assume(require), <proof stms…>, Assert(ensure) ]))
Assume(forall vars, require ==> ensure)      // separate statement, already emitted
```

So the WP job for `DeadEnd(block)` is exactly: **verify the block's internal obligations in
a scope whose effects are discarded**; the proven fact re-enters the main flow via the
`Assume` Verus already emits after it. No new fact-plumbing is needed on our side.

**The machinery exists.** `Wp::ClosureBody` (`sst_to_lean.rs:4189`) is documented as "the
body is its own dead-end — its theorems are emitted … but its terminator doesn't carry
through; the surrounding fn's flow continues with `after` unchanged." And the
`StmX::ClosureInner` arm (`sst_to_lean.rs:~4975`) already shows the exact construction:
`build_wp(block, Wp::Done(lit_bool(true)), ctx, loop_stack)` then wrap with `after`.

**Fix.** New arm at the rejection site (`sst_to_lean.rs:4942`):

```rust
StmX::DeadEnd(block) => {
    let body = build_wp(block, Wp::Done(LExpr::lit_bool(true)), ctx, &[])?;
    Ok(Wp::Scope { body: Box::new(body), after: Box::new(after) })
}
```

with `Wp::Scope` a new variant whose walker arm is `ClosureBody`'s minus the param
binders — **do not** reuse `ClosureBody { closure_params: vec![] }` directly: its contract
(doc comment, `push_mod_var_frames` interplay) is closure-specific, and a dedicated variant
keeps both auditable. Design points to settle at impl time:

- **Trivial-terminator noise.** The inner walk's `Done(true)` leaf emits one trivially-true
  theorem per assert-by (same as empty-ensures fns today — see `emit_done_or_split`'s
  unwrapped-leaf arm, `sst_to_lean.rs:~2185`). At 1,267 sites this is real bloat: add a
  skip for `LitBool(true)` leaves in `emit_done_or_split` (also de-noises empty-ensures
  fns and closures). Check nothing depends on the anchor theorem existing (sourcemap,
  per-fn theorem counting in the pass/fail bookkeeping).
- **`loop_stack`: pass empty** (`&[]`), not the current stack. `break`/`continue` cannot
  legally cross an assert-by boundary (mode checker); an empty stack turns any leak into
  the existing clean error instead of silently jumping to an outer loop's leaf.
- **Hypothesis flow INTO the scope** — outer facts must be visible to the proof body's
  obligations. This falls out of the walker shape (the scope's body is walked under the
  current `OblCtx`, same as `ClosureBody`'s `body`), but assert it in the repro: an
  assert-by whose proof needs an outer `let` and an outer hypothesis.
- **Nesting** (assert-by inside assert-by) recurses with no extra work.
- **`assert forall` variant** rides the same desugar (the `Assume(forall …)` after the
  DeadEnd carries the binders) — covered by the same arm, but include one in the repro.

**Consequences, stated up front:** every unlocked fn flows into the auto bucket — expect
the bucket to grow substantially (the §10.1 "walls fell" effect, round two) and the fn-level
pass count to move little at first. That is the honest measurement, not a regression. Also:
exec fns using Verus-body `assert … by { }` become translatable — the exec gate's coverage
*grows*; compare error locations, not counts.

**Acceptance:** `DeadEnd` rejections → 0 crate-wide; britton's assert-by-heavy lemmas and
the commented-out `lemma_qpow_conj` (parent doc §5) codegen; repro tests: plain assert-by,
assert-forall-by, nested, and one requiring outer-context facts. Exec gates green by
location.

---

## F5. check.sh hygiene (gate honesty)

Drop the uncommitted `--emit-lean` from tactus-group-theory's default `check.sh` line
(keep `-V cache` + tee-to-log; `--emit-lean` stays passable via `"$@"`). Today the standing
gate is **codegen-only** for every Lean-routed fn (§10 gate-hygiene note). Cost check
before landing: the committed gate routes only the ~24 exec fns through Lean (the ~90-min
number is `--lean-all-proofs` crate-wide, which the gate does not pass), so a real Lean run
in the gate is minutes, not hours. Land it the moment the in-flight experimentation no
longer needs codegen-only runs as the default — it is one line, and every session the gate
stays emit-only is a session `reference_tgt_gate_baseline_errors` drifts.

---

## F6. Deferred altitude items (from the `2e43a39` review round)

All five are "right depth, wrong day" refactors. None should be its own arc; each rides
the arc that next touches its machinery:

| Item | Ride with | Note |
|---|---|---|
| Broadcast axioms as real `EmitStep`s in `dep_order::order_emission` (replace the greedy `flush_ready_axioms` loop) | F2a's neighborhood, **after** it | Absorbs F2a's special case into a normal dep edge; also owns the "final forced flush" soundness comment |
| Seq companion via `lean_ast::Theorem` instead of `Command::Raw` | F2a | Same function, same test module |
| One `EmitEnv` struct for the ambient thread-locals (`install_emit_tables`'s renames / `CRATE_NS` / `CRATE_DECLS`, plus self-decls) | any emission-layer arc | Kills the with-restore/Drop-guard panic-leak *class* the review found an instance of |
| `choose_node` deriving names from binders instead of the parallel `names` slice | next B2-adjacent touch (`expr_shared.rs:1156`) | Pure API tightening |
| Hyp attachment at Wp-build chokepoints instead of walker arms | **F4** | F4 adds a walker arm; the `obl_with_choose_hyps` sprinkle (6+ sites: `sst_to_lean.rs:1817,1844,1962,2001,2028,…`) is exactly the pattern a new arm can forget. Doing this refactor first (or with F4) means the scope arm can't miss witness hyps by construction |
| Chained-op rendering divergence (found during F2a) | F3 (same unify-the-paths move) | The same chained comparison (`0 <= j <= k <= len`) renders let-bound **left-assoc** on one path and bare **right-assoc** (`Multi(Chained)`/`and_all`) on the other. F2a's companion proof was the first casualty (fixed by shape-robust `omega`); any consumer pattern-matching conjunction structure is exposed until the paths agree |

---

## F7. The auto bucket (5,987 goals / ~1,024 fns) — measurement and policy, not a fix

This is the arc the bugs doc said "decides everything after this doc," and it is **genuine
proof work**: goals Z3 closed via quantifier instantiation + fuel idioms that
`tactus_auto`'s toolbox doesn't attempt. It should NOT start until F3+F4 land — both grow
the population, and any taxonomy built before them is on a biased sample.

Shape of the arc (spec'd here so it's ready; policy details belong to
`DESIGN-transparent-automation.md`):

1. **Cluster** the post-F4 log's auto-failures by goal shape (mechanical: goal-head symbol
   + hypothesis fingerprint). Predicted clusters from the corpus: recursive-spec-fn
   unfolding depth, quantifier instantiation (the trigger idioms), seq extensionality,
   nonlinear/mod-div arith, `reveal`-dependent opaque fns.
2. **Sample and hand-close** 30–50 goals across clusters in a scratch Lean file (the 10s
   scratch loop from `project_tactus_gt_migration_idioms`); record the closing tactic per
   goal.
3. **Decide per-cluster**, three buckets: (a) a **closer rung** — only when one enumerated
   tactic closes essentially the whole cluster (layered `<;>` composition, no open-ended
   simp sets); (b) **explicit-tactic migration** — per-fn work using the validated
   gt-migration idioms (by-body lemmas, site assert-by); (c) **`#[verifier::z3]` opt-out**
   for fns whose proof style is Z3-idiomatic and not worth migrating (this keeps the
   opt-out honest: chosen per-fn, recorded, revisitable).
4. Output = a numbers-backed split of the corpus across (a)/(b)/(c) and an updated
   automation doc. Expect (b) to dominate — that was the transparent-automation bet.

---

## Sequencing, gates, measurement

**Order: F1 → F2a(+F2b) → F3 → F4**, with F6 items riding as tabled and F5 when
experimentation settles. Rationale: F1/F2a are pure signal cleanup (parse errors kill whole
files; missing companions fail whole fns) and are each ≤ a day; F3 before F4 because F4's
unlocked population includes many `seq!`-using proof fns — landing F3 first means F4's
measurement isn't polluted by known mistypes.

**Per-fix loop** is unchanged from the bugs doc: fix in `tactus/source/lean_verify/`;
`vargo build --release`; minimal repro in the tactus test suite; module-scoped re-run
(britton for F1/F4, base_swap/m4_qpow for F2/F3); tutorial + tgt exec gates green **by
location**.

**Measure once, after F4**: full-crate `--lean-all-proofs` real run, update §10.1's table.
Expected shape: codegen rejections 1,409 → ~0, type-mismatch ~1,145 → ~0, parse errors
39 → 0, termination 81 → ≤13, auto bucket grows past 6k — at which point F7's taxonomy
starts from an honest population.

---

## Key file/line references

| What | Location |
|---|---|
| `let` printing (hardcoded indent) | `lean_verify/src/lean_pp.rs:689–696` |
| `current_line_indent` helper | `lean_verify/src/lean_pp.rs:195` |
| Companion emission + axiom gate | `lean_verify/src/generate.rs:1194–1218, 1248` |
| Decreasing tactic rungs | `lean_verify/src/to_lean_fn.rs:82` |
| ArrayLiteral rejection (SST) | `lean_verify/src/to_lean_sst_expr.rs:1349` |
| ArrayLiteral render (VIR) | `lean_verify/src/to_lean_expr.rs:798` |
| ArrayLit printing | `lean_verify/src/lean_pp.rs:774` |
| Array→Vector type mapping | `lean_verify/src/to_lean_type.rs:198` |
| `Tactus.*` deref wrappers | `lean_verify/TactusPrelude.lean:98–114` |
| DeadEnd rejection | `lean_verify/src/sst_to_lean.rs:4942` |
| DeadEnd desugar | `vir/src/ast_to_sst.rs:~2270–2316` |
| `Wp::ClosureBody` (the shape to copy) | `lean_verify/src/sst_to_lean.rs:4189` (variant), `:4975` (construction), `:1976` (walker) |
| Trivial-leaf emission | `lean_verify/src/sst_to_lean.rs:2164` (`emit_done_or_split`) |
| Witness-hyp sprinkle (F6-5) | `lean_verify/src/sst_to_lean.rs:1817,1844,1962,2001,2028` |
| Baseline numbers | `DESIGN-lean-all-proofs.md` §10.1 |
