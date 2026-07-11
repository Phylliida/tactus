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
`Datatype` AST for IndexedInductive ctor result types.

**Same-day follow-up: F3 IMPLEMENTED & COMMITTED (`8171498`), F4 IMPLEMENTED & COMMITTED
(`95c5b1b`).** F3: `seq![a, b]` pins — multi-element lowers through `View for [T; N]`
over an array literal (single-element is a push chain, hence always worked); the mistype
is a List literal ascribed at `Vector` inside `Tactus.Ref.mk` (whose anon-struct display
is the `{ deref := … }`); fix = new `ExprNode::VectorLit` (`#v[…]`, validated on 4.25.0)
via a shared typ-dispatched `expr_shared::array_literal_node` on BOTH paths; decoration
handling stays per-path (VIR's `apply_ref_coercion_if_needed` already bridges — the SST
legacy arm wraps explicitly via `collect_ref_wraps`). m4_qpow: rejections 6 → 0, files
2 → 8. F4: `Wp::Scope` per the spec, plus two sub-fixes the repros surfaced — zero-binder
`∀`/`∃` printed as the parse error `∀, P` (plain assert-by's re-assumed
`Quant(FORALL, [], …)`; now print the body alone), and assert-forall skolems
(`LocalDeclKind::AssertByVar`, no `Wp::Let`) are ∀-bound on scope theorems (occurrence-
collected per block, minus names an enclosing scope already bound). The trivial-True
terminator theorem per scope is KEPT for now (closure precedent) — the skip in
`emit_done_or_split` is a deferred follow-up. **Crate-wide codegen rejections 1,409 → 0;
2,747 of 2,747 proof-obligation fns emit (100% codegen coverage).** e2e suite 532/0.

**Overnight re-measure DONE (2026-07-11, §10.2 of the parent doc):** 723/2,953 fns pass
(was 253) — 2.9×; every targeted structural family at 0; honest auto bucket = 24,080
goals across ~2,230 fns. **Deferred batch IMPLEMENTED & VALIDATED (`62f8bb0` + rung fix):
F2c via two proved @[wf_preprocess] prelude theorems (Tactus.or_eq_dite/and_eq_dite —
the transparent replacement for the rejected ite-rewrite; guards thread during
termination elaboration only, eq_def keeps user shape; m3_blinker termination 2 → 0),
F2b via expr_shared::wrap_int_measure Int.toNat (both pinned shapes close in
m4_defect_flow), Wp::DoneEmpty (no trivial-True scope theorems), and the preventive
sanity-checker rule (anchored self-refs inside declarations; 3 unit tests).** Remaining:
F5 one-liner (Danielle's call), F6 altitude items (ride adjacent arcs; chained-op
divergence → B5), F7 auto-bucket taxonomy (NOW unblocked with honest numbers), B5
(parallel session), heartbeats triage (998 blocks), the 61-error tuple-Int residual
(B5-adjacent), trivial-True... done. Next = F7.
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

### F2c. Recursion under Prop connectives (pinned 2026-07-10 during F2a validation, deferred)

A drop_first-termination sub-family the companion can NOT close: spec fns whose recursive
call sits under `||`/`&&` rather than an `if` — e.g. `m3_blinker.no_sym`:
`len w = 0 ∨ (¬(index w 0 = t) ∧ no_sym (drop_first w) t)`. Verus's spec `||`/`&&` are
short-circuit (the recursive arm is guarded), but Lean's `Or`/`And` are plain
applications — the termination checker provides **no branch hypothesis**, so
`len (drop_first w) < len w` arrives without `¬ len w = 0` in context and is genuinely
unprovable. Fix shape (deferred): lower spec `||`/`&&` whose RHS contains a self-call to
the `if-then-else` form (semantically identical by short-circuit definition) — a
rendering change, not a tactic. Size of family: the post-F4 full-crate re-run measures it
(≤ 68 goals; at least 2 attested in m3_blinker).

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

---

## Deferred-item specs (2026-07-10 second pass) — root-cause clustering

Question prompting this pass (Danielle): are the deferred items independent chores, or do
they share underlying causes that infra work would address together? Answer: they cluster
into four causes plus a preventive check. Two "items" dissolve entirely into their
cluster's fix.

### Cluster 1 — termination fidelity (F2b + F2c, one small arc)

**Shared cause:** Lean's termination checker derives its goals from the def's *syntactic*
structure, which sees strictly less than Verus's VC generator: it wraps non-Nat measures
in opaque `sizeOf` (F2b) and provides branch hypotheses only for control flow it
recognizes — `if`/`match`, not Prop `∨`/`∧` (F2c). Verus's own SpecTermination VC has
both right, but its proof cannot be transplanted: the guard hypotheses must exist *in the
decreasing goal's context*, which only the def's syntax provides. (Checked: no
tactic-side fix exists for F2c — the hypothesis is genuinely absent and the goal false
without it.)

**Fix, both halves at recursive-def emission** (`spec_fn_to_ast` + termination_by
rendering):
- F2b: wrap Int-typed `termination_by` measures in `.toNat` (omega handles `Int.toNat`;
  Nat measures unchanged). Closer rung if needed: `(split <;> omega)` for measure-position
  ifs — settle empirically.
- F2c: render spec `&&`/`||` **whose RHS subtree contains a self-call** as
  `if a then b else False` / `if a then True else b` — propositionally identical, and
  if-on-Prop is already pervasive in emitted code (Classical decidability is ambient in
  the prelude). Scope tightly: recursive spec-fn def bodies only, only the connectives on
  the path to a self-call — everything else keeps `∧`/`∨` (better for simp and for
  humans).

Pin targets: m3_blinker's `no_sym`/`drop_base_run`/`no_sub3` (F2c, attested) + a synthetic
Int-abs measure (F2b). One arc, S–M total.

### Cluster 2 — two renderers, one language (F6f; the B5 umbrella)

**Shared cause:** the VIR and SST paths render overlapping expression forms with separate
code, and every divergence becomes a bug family eventually (B2 choose, F3 literals, F2a's
companion, B5's claimed-vs-actual). The standing remedy is the one B2/F3 followed —
shared node builders in `expr_shared` — and, long-term, the typed-renderer migration
(DESIGN-typed-renderer.md, B5's arc, running in a parallel session).

**F6f specifically** (chained-op associativity: `0<=j<=k<=len` renders let-bound
LEFT-assoc via the SST desugar but bare RIGHT-assoc via `Multi(Chained)`/`and_all`): the
inputs differ (ast_to_sst desugars chained ops before the SST path ever sees them), so
full unification means desugaring on the VIR path too — but the *cheap* fix is a
fold-direction change in `and_all` to match the SST shape, plus the suite. Likely ~1 line
+ tests. Do it opportunistically; anything pattern-matching conjunction shape (the
companion was the first casualty) is exposed until then.

### Cluster 3 — scheduling as a real graph (F6a + F6b; F2a's special case dissolves)

**Shared cause:** broadcast axioms (and now the seq companion) are emitted by a parallel
greedy flusher (`flush_ready_axioms` + a final forced flush + F2a's forced-add special
case) instead of being nodes in `dep_order::order_emission`'s graph. Making them real
`EmitStep`s with real edges: the F2a special case becomes an ordinary edge
(companion → axiom → defs), the final-flush soundness comment localizes, and the
companion can go through `lean_ast::Theorem` (F6b) instead of `Command::Raw` in the same
touch. One self-contained M refactor in `generate.rs`/`dep_order.rs`; the e2e suite +
britton emission diff are the gate.

### Cluster 4 — ambient thread-local state (F6c)

**Cause:** five-ish install/restore thread-locals with per-site Drop-guard discipline;
the class already produced one real bug (the `with_self_decls` panic leak, review finding
#3). One `EmitEnv` struct — either passed explicitly or a single thread-local holding the
whole struct with one guard — kills the class. Compiler-guided churn, M, no behavior
change; ride any emission-layer arc.

### Preventive check — the B1a-regression class (NEW, recommended soon)

Three same-class bugs in one day (datatype ctor fields, IndexedInductive ctor results,
trait sibling refs): **a reference to a declaration-in-progress rendered root-anchored**,
each failing only at lake time. The debug reference sanity checker already registers
decls and references — add the rule: *flag any `_root_.…X` reference emitted inside the
declaration of `X`* (it knows the current decl from the self-decls set / command
structure). Catches the whole class at codegen time, including any not-yet-discovered
sites (structure field types? instance heads?). XS–S, high leverage. A one-shot audit of
remaining declaration-body renderers (instances, classes, defs with where-clauses) rides
along.

### Independent smalls (no shared cause)

- **Trivial-True scope terminators** (F4 leftover, ~1,267 extra goals/run): simplest safe
  form is a `Wp::DoneEmpty` terminator variant whose walker arm emits nothing — used ONLY
  by the Scope arm, so empty-ensures fns keep today's `True` theorem and no bookkeeping
  changes (fns always retain ≥1 theorem from their own ensures). XS once the crate re-run
  quantifies the lake-time cost; skip if negligible.
- **F6d** (`choose_node` names from binders): pure API tightening, ride the next
  expr_shared touch.
- **F6e** (hyp attachment at Wp-build chokepoints): F4's Scope arm turned out not to need
  the witness-hyp sprinkle (body/after arms handle their own), so the motivating risk
  didn't materialize — downgraded to pure altitude; ride a future Wp-arm change.
- **F5** (check.sh `--emit-lean` drop): one line, gated on Danielle (uncommitted
  working-tree edit is hers).

---

## Naming: Option B — no namespace wrapper, full dotted names (2026-07-11)

Danielle flagged the post-B1a `_root_.{ns}.…` anchoring as clutter; a shadow-gated
print-time de-anchor was proposed and REJECTED (context-sensitive display = the ite-
rewrite mistake in display form). Two predictable alternatives were weighed — B: full
path always, no `namespace` wrapper (`lib.word.empty_word` uniformly, zero context
sensitivity, zero source impact); C: relative always + deterministic binder-suffix on
module-segment collisions (~25 sites in gt: `symbol`×8, `h1`×8, `h2`×8). **Danielle
picked B as most transparent.**

Implementation (same day): `lean_name` drops the `_root_.` anchor (in-crate →
`{ns}.{rel}`, cross-crate → bare); no `NamespaceOpen`/`Close` emission; the
`CURRENT_DECL_SELF` machinery is RETIRED ENTIRELY — empirically at root scope (4.25),
full-name self-references resolve fine mid-declaration for defs, inductives, and mutual
groups (the `_root_.` prefix was what broke them, not mid-decl-ness; the `List.myLen`
idiom generalizes). Class sibling refs keep strip-to-bare (only bare resolves in class
bodies — unchanged empirics). One reserved name: a binder equal to the crate namespace
would capture every crate-internal reference's leading segment — the sanity checker
rejects it at every scope-insertion point (`check_reserved_binder`). The anchored-self-
ref preventive rule stays as a regression tripwire.
