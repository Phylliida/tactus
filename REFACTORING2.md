# Refactoring Survey 2 — 2026-06-12 (the plan for the next push)

Companion to `REFACTORING.md` (the 2026-06-05 session record). That document
records a push that already happened; **this one is a survey written before
any code moves** — findings, proposed arcs, and sequencing for a "same
functionality, more maintainable, fewer lines where that's honest" push.

## Progress ledger

| Item | Status | Commit |
|---|---|---|
| 1.1 smart-constructor adoption | **DONE** (same day) — raw sites 48→0 in to_lean_fn, LBinder literals 37→3, net −165 lines | `a74ce99` |
| 1.2 EmitCtx | **DONE** — all-fn map built 3×→1×, trait_impl_to_ast 9→6 params, trait_to_ast 5→2 | `58f5277` |
| 1.3 trait_emit.rs extraction | **DONE** — pure move, to_lean_fn.rs 2506→1380 lines | `680a6c8` |
| 1.4 god-function splits | **DONE 2026-07-02.** krate_preamble: split landed via 2.B step 1a (`spec_world_cmds` extracted, ~470 lines; the survey's predicted deletion is deferred until/unless defs mode becomes the default and standalone retires — wait on real-crate experience). push_post_call_frames → per-phase helpers (orchestrator reads as the phase diagram; also fixed the fn's doc block being rustdoc-attached to `struct ReturnProphecy`). build_wp: re-survey found Call/Loop arms were ALREADY extracted — only AssertBitVector + AssertQuery warranted it (done, same #104 destructure-at-dispatch pattern); two stale comments corrected in the move | `011dd62`, `1012038` |
| 1.5 comment policy | open — owner's call | |
| 2.A typed-expr unification | **step 1 DONE** — READPLACE_LIFT_ENABLED thread-local → `RenderCtx.inlining`; missing DESIGN § "TypedExpr-with-smart-ctor" written. **Reassessment while in there:** the typed-substitution gap § 2.A leads with is *largely already closed* by intervening work — value-level param substitution moved to typed render-time `value_subst` (see sst_to_lean.rs ~3074 comment); remaining post-render `substitute` calls are type-level or same-typ name swaps, safe untyped. **Step 2 DONE** — BinderCtx merged into RenderCtx (`8d559e6`): VIR renderer internals single-ctx, binder map rides `ctx.binder_typs`, extended at binder sites; trap handled structurally (inlining entry clears via `without_binder_typs()`); public `vir_expr_to_ast_with_binders(expr, binders, ctx)` signature kept, external callers untouched. **2.A is architecturally COMPLETE** — the bug genus (context/typing info not local to use sites) is closed: typed substitution (pre-existing, verified), render-mode state on ctx (step 1), binder scope on ctx (step 2). Honest reassessment of the remainder: the ~71 coercion call sites already funnel through the shared `coerce_lexpr`/`apply_deref_chain` primitives; per-site TypedExpr restyling is opportunistic polish, NOT a scheduled arc — do it only when touching a site anyway | `35a1f34`, `8d559e6` |
| 2.B shared crate module | **design pass DONE** (same day) → `CRATEDEFS.md`, with measurements: inline prelude costs ~1.3s/check (~2.6s → ~1.3s with prebuilt .olean; one-time 2.7s build). **Step 0 LANDED** (`5ff8d61`): prebuilt TactusPrelude.olean in user-level content-hashed cache — **suite 59s → 36.85s (−37%)**, 505/0. **Step 1a LANDED** (same day): flag-gated `--tactus-crate-defs` shared spec-world module; suite unchanged 508/0; deep-closure crates −12% at 10-fn miniature scale (scales with closure × N — the group-theory shape); helpers stay per-file (1b = move proof fns into defs w/ per-theorem attribution, kills quadratic helper re-verification). **Step 1b LANDED** (same session): TactusProofs_{crate}.lean batch — all ordinary proof fns verify in ONE Lean run with per-theorem line attribution; deep-closure miniature **25.1s → 5.9s (−76%)**; 2 + N_exec runs per crate at any proof-fn count; quadratic helper re-verification dead. Suite 510/0. Step 2 worker pool remains for the exec-fn / per-check floor | `5ff8d61` |
| 2.C persistent Lean worker | **largely subsumed by 2.B step 1b** for proof fns (one run per crate IS the amortization); remaining scope = exec-fn per-check floor (~1.3–2s spawn+import each). Warm-worker infra exists (`tactus-lsp`); gate on measuring an exec-heavy real crate before building | |
| EmitCtx follow-ups | `RenderCtx::empty()` upgrade sites remain open (behavior changes, one at a time with e2e). Thread-local fold-in **REJECTED 2026-07-02** (owner-approved close): re-scoped after 2.A and the economics are upside-down — retiring `INHERENT_METHOD_RENAMES` means threading ctx into `lean_name`, which is called from `typ_to_node` and ~34 direct sites across 10 files (+150–200 lines of signature noise); both tables are krate-derived, idempotent, installed at every entry point, and fail LOUDLY when missing (unreferenceable `impl__N` names / missing bound hypotheses → Lean errors, not silent wrongness). Done instead: all three entry points now funnel through `install_emit_tables` (the single install chokepoint — the pair can't drift), reasoning recorded at the wrapper | |

Every step gated on the full e2e suite (505/0 at time of writing) + unit
tests (275/0). All three landed commits are mechanical/behavior-preserving.

Method: read `REFACTORING.md`, the relevant `DESIGN.md` §§, and the HANDOFF
history; measured the `lean_verify` crate; read the large files and the
newest (trait/extends/closure-ABI-adjacent) code directly. Every claim below
is pinned to a file:line or a measurement so a later session can re-verify.

---

## Part 0 — The shape of the problem (measure first)

The crate *looks* huge (~27.3k lines) but decomposes as: ~5.7k unit tests
(`src/tests/`), and of the remaining production lines, **roughly half are
comments**. Measured 2026-06-12:

| File | Total | Comments | Blank | Code |
|---|---|---|---|---|
| `sst_to_lean.rs` | 5572 | 3029 (54%) | 162 | 2381 |
| `to_lean_fn.rs` | 2643 | 1122 (42%) | 98 | 1423 |
| `lean_ast.rs` | 1858 | 771 | 91 | 996 |
| `generate.rs` | 1443 | 614 | 72 | 757 |
| `to_lean_sst_expr.rs` | 1329 | 625 (47%) | 44 | 660 |
| `to_lean_expr.rs` | 1118 | 423 | 60 | 635 |
| `expr_shared.rs` | 973 | 557 (57%) | 41 | 375 |
| `dep_order.rs` | 948 | 263 | 66 | 619 |
| `lean_pp.rs` | 885 | 124 | 51 | 710 |
| `impl_subst.rs` | 854 | 373 | 32 | 449 |
| `mut_ref_normalize.rs` | 741 | 349 | 21 | 371 |

Actual production code across the backend is **~10k lines** — small for what
it does (WP engine, two expression renderers, trait/class/instance emission,
dep ordering, pretty-printer, sanity checker). The comment mass is largely
bug-archaeology and invariant documentation that past sessions demonstrably
relied on. Consequence: **code golf has limited headroom (~10–15% of code)**;
the real levers are a handful of structural consolidations (Part 1), three
infrastructure arcs (Part 2), and one values decision about comments (§ 1.5).

### Already rejected — do NOT re-litigate

These were investigated with recorded reasoning that still holds:

* **`Exp`/`Expr` twin-renderer unification** — rejected; the trees are
  genuinely asymmetric (VIR-AST `Block`/`Match`/`Ctor`/`Place` vs SST
  `CheckDecreaseHeight`/`InternalFun`/flattened stmts). Shared rules live in
  `expr_shared.rs`. See DESIGN § "Two parallel expression renderers" and the
  `expr_shared.rs` header.
* **Deleting `mut_ref_normalize.rs`** — rejected; ~600 of its lines are
  experimental `--new-mut-ref` support, not a gateable Verus artifact. See
  REFACTORING.md Part 3.
* **Fusing `build_wp_loop`'s two passes** — audited 2026-05-11 (#117), keep.
  See DESIGN § "Two-pass over loop bodies".
* **Folding the two ambient thread-locals into EmitCtx/RenderCtx** —
  rejected 2026-07-02 (see the "EmitCtx follow-ups" ledger row): ctx would
  have to reach `lean_name` (called from `typ_to_node` + ~34 direct sites)
  for two idempotent, loud-failing, krate-derived tables. All entry points
  funnel through `generate::install_emit_tables` instead.
* **`tactus_auto` retirement via lean-backend DETECTION (inference)** —
  rejected 2026-07-02: no flag can infer per-fn block language. What
  landed the same day instead (owner decision) is a SEMANTICS CHANGE —
  block language follows routing, `#[verifier::z3]` is the combined
  opt-out. Don't re-attempt inference; the settled rule is in Part 3.

---

## Part 1 — Tactical bundle (low risk, roughly one session, do first)

### 1.1 Adopt the existing smart constructors; add `LBinder` helpers

`lean_ast.rs` already has ~30 convenience constructors (`LExpr::var`,
`::app`, `::implies`, …) but the newest code doesn't use them:

* `LExpr::new(ExprNode::…)` raw sites: **48 in `to_lean_fn.rs`**, 14 in
  `to_lean_expr.rs`, 4 in `to_lean_sst_expr.rs`, 2 in `sst_to_lean.rs`.
* `method_type` (`to_lean_fn.rs:1520`) hand-builds
  `ExprNode::BinOp { op: Implies, lhs: Box::new(…), … }` where
  `LExpr::implies` exists.
* The 5-line `LBinder { name: Some(…), ty, kind: BinderKind::X }` literal
  recurs **25× in `to_lean_fn.rs`**, 11× in `sst_to_lean.rs`. Add
  `LBinder::explicit(name, ty)` / `::implicit_ty(name)` / `::instance(ty)`
  and each collapses to one line.

~200 lines, zero behavioral risk, and it makes the trait-emission code (the
part most likely to grow next) read at the density of the older code.

### 1.2 An `EmitCtx` for krate-level tables (kills a recurring bug class)

Symptoms today:

* `trait_impl_to_ast` (`to_lean_fn.rs:1957`) takes **8 parallel parameters**
  (`tactic_bodies`, `subst`, `nonempty_bounds`, `unemittable`,
  `trait_outparams`, …), each documented inline, each threaded through every
  intermediate signature. Adding the next table = N signature edits.
* ~80 fully-qualified `crate::expr_shared::RenderCtx::empty()`-style call
  sites. Every `::empty()` is a site where context is **dropped** — and the
  RenderCtx history (HANDOFF 2026-05-25/26) shows "renderer lacked context"
  was the root of a real bug cluster.
* Three **ambient thread-local tables** installed before rendering:
  the inherent-method rename map (`to_lean_type.rs:294`, set by
  `generate.rs install_inherent_method_renames`), the datatype-field-bounds
  map (`to_lean_sst_expr.rs:256`, set by `install_datatype_field_bounds`),
  and the `READPLACE_LIFT_ENABLED` render-mode flag (`to_lean_expr.rs:102`).
  Render output depends on ambient installation order.

Proposal: build the krate-level tables **once** into an `EmitCtx` (fn_map,
unemittable, trait_outparams, tactic_bodies, renames, field bounds) and
thread that single reference. `RenderCtx` becomes a view into it (or merges
into it). The thread-locals fold in last — they exist precisely because
`lean_name::from_path` / `type_bound_predicate` are called from deep sites
with no ctx param; once the ctx reaches those sites the globals retire.

### 1.3 Carve trait/class/instance emission out of `to_lean_fn.rs`

`to_lean_fn.rs:1321–2643` (~1300 lines: `trait_to_ast`, `trait_impl_to_ast`,
`method_type`, `proof_fn_method_type`, `class_method_value_binders`,
`strip_class_qualifier*`, `class_extends_to_ast`, `compute_trait_outparams`,
`trait_bounds_to_ast*`) is a cohesive subsystem — and the **active closure-ABI
frontier is about to add more code exactly here**. Pure code move into a
`trait_emit.rs` sibling, same playbook as the 2026-06-05 push's five
extractions. Lesson carried forward from that push: the unit tests reach
private items via `use super::*` — compile the **test** target
(`cargo check -p lean_verify --tests`), and re-export moved items.

### 1.4 Split the two-and-a-half god functions

* `krate_preamble` (`generate.rs:200–888`, ~690 lines) — the file-emission
  god function: helper collection, dep walk, imports, ordering, emission.
  Wants to be named phases. (Note: **Part 2.B may delete most of it** — if
  2.B is greenlit soon, don't polish this first; do the cheap phase-split
  only if 2.B is deferred.)
* `build_wp` (`sst_to_lean.rs:4130–4629`, ~500 lines) — one match over ~15
  statement variants; extract per-arm `wp_assign` / `wp_if` / … functions.
* `push_post_call_frames` (`sst_to_lean.rs:2928–3288`, ~360 lines) — already
  phase-commented internally; extract the phases.

### 1.5 Comment policy — the only "substantially fewer lines" lever (owner's call)

~9k comment lines in production files. A meaningful fraction are multi-
paragraph narratives that duplicate content also recorded in DESIGN.md /
BUG-*.md / HANDOFF.md. A "one paragraph in code + pointer to the DESIGN §"
policy could cut 2–3k lines.

**Recommendation: mostly against.** These comments are load-bearing for
future sessions in a way ordinary codebases' comments aren't — they are the
in-context memory. Safe subset only: where a comment block is a *verbatim*
duplicate of a DESIGN section, keep the one-paragraph version + pointer.
This is a values decision, not a technical one; it stays open until the
owner decides.

---

## Part 2 — Infrastructure arcs (the "are we doing this in a silly way" findings)

### 2.A Typed-expression unification — finish what `typed_expr.rs` started

**Finding: the wrapper-coercion machinery has three coexisting generations,
all live simultaneously.** `lean_ast::Expr` is untyped syntax, but
composition constantly needs "what Lean type does this rendered value have
vs. what the slot expects" (the `Tactus.Ref.mk` / `.deref` wrapper-depth
bridging). Three successive partial solutions accreted:

1. **Ad-hoc per-site coercion** — `coerce_lexpr` / `apply_ref_coercion_if_needed`
   / `BinderCtx` / `caller_arg_actual_typ` at ~124 sites across 6 files
   (29 `to_lean_expr`, 16 `expr_shared`, 12 `to_lean_sst_expr`,
   10 `sst_to_lean`, 5 `typed_expr`, 3 `to_lean_fn`), including the
   `READPLACE_LIFT_ENABLED` **thread-local** toggling renderer behavior per
   context (`to_lean_expr.rs:102–109`).
2. **`TypedExpr` smart constructors** (`typed_expr.rs`) — the Phase-1
   scaffold landed 2026-05-25; Phase-2 migration reached exactly ~6 sites in
   `push_post_call_frames` (`sst_to_lean.rs:2977–3248`) and stalled.
3. **`RenderCtx` threading** — landed across both renderers 2026-05-26, but
   per the HANDOFF's own record: "the test wins didn't materialize for the
   inlining-context cases — **those need typed substitution**, which is
   bigger than this session."

The HANDOFF names the root cause precisely: **substitution is untyped**, so
a substituted value's actual typ is unknowable at use sites, so every
generation of fix hits the same "info-not-local" wall. The tests were
eventually closed by other means (callee rewrites, use-site fixes —
REFACTORING.md Part 4), but the *bug genus* remains; it has consumed
multiple sessions (β refactor, U2, the three SST clusters of 2026-05,
Cluster A).

**Proposal:** make typed expressions the currency of both renderers —
rendering produces `(expr, typ)` everywhere, `substitute` carries typs (the
`RenderSubst` map in `expr_shared.rs` already half-does this with its
`(rendered_value, value_typ)` pairs), bridging happens at composition time
in ONE place, `into_untyped` only at the pp boundary. Generations 1–3
collapse into one mechanism; the thread-local dies; `BinderCtx` merges into
the typed renderer state.

Expected: ~400–600 line reduction, but the line count is not the point —
this closes the most expensive recurring bug class in the project, **and
every closure-ABI feature added before this lands will pay the
three-generation tax** (more sites to migrate later). Sequencing: after 1.2
(EmitCtx gives the migration a clean substrate), before the closure-ABI arc
resumes in earnest.

Housekeeping while there: `typed_expr.rs`'s header cites
"DESIGN.md § 'TypedExpr-with-smart-ctor'" — **that section does not exist**
(the analysis lives only in HANDOFF ~§ 2026-05-25/26). Write the DESIGN
section as part of this arc.

### 2.B Shared crate module instead of per-fn preamble re-emission

**Finding: every per-fn `.lean` file re-derives and re-contains the world.**
`emit_proof_fn` / `emit_exec_fn` call `krate_preamble` per function: re-walk
dependencies, re-run `dep_order`'s topological sort **per file**, re-emit
every transitively referenced spec fn / datatype / class / instance into
every file. Worse: referenced helper proof fns are re-emitted as **full
theorems with their tactic bodies** (`generate.rs:848`), so Lean
re-elaborates — i.e. **re-verifies — every helper inside every file that
references it.** Quadratic re-checking along lemma dependency chains.
(Cross-crate broadcast lemmas are already axioms — `generate.rs:853–871` —
it's same-crate helpers that re-verify.)

**Proposal** (the standard design — it is literally how Lean projects
structure themselves): emit one `CrateDefs.lean` per crate (spec fns,
datatypes, classes/instances, topologically ordered **once**); Lean compiles
it to `.olean` once; per-fn theorem files `import` it. Helper proof fns
become their own imported theorems (verified once) rather than re-inlined
text.

Expected wins:
* `krate_preamble` (~690 lines) shrinks to a fraction;
  `collect_referenced_proof_fns` / `collect_referenced_datatypes` and the
  per-file dep-walk machinery mostly delete. Likely the **single biggest
  honest code deletion available** (~800+ lines).
* Eliminates quadratic helper re-verification → faster suite, faster
  interactive checks.
* Converges with SERVER.md: a goal-state server wants stable imports, not
  per-fn regenerated preambles.

Costs / open questions (why this is an arc, not a cleanup):
* Incrementality semantics change: a spec-fn edit rebuilds the shared module
  (Lean is module-incremental, so this is bounded, but it's a behavior
  change from "each file self-contained").
* Per-fn augmentations need rehoming: the `[Nonempty T]` inference
  (`nonempty.rs`) and unemittable filtering currently run per-render.
* Debugging ergonomics: "cat one self-contained file" becomes "cat two
  files." Acceptable, worth noting.
* Test harness: per-file parallel checks gain a shared build dependency
  (lake handles this, but the harness invokes `lean` directly today).

### 2.C Persistent Lean worker instead of process-per-check

`lean_process.rs:171–177` spawns a fresh `lean --json` / `lake env lean
--json` per checked fn — paying Lean startup + import initialization every
time, for every fn in the e2e suite. SERVER.md already plans a
`lean --server` proxy for the infoview; **the same persistent worker can
service batch verification** (module init paid once per session). Small code
delta, large wall-clock win, and it merges two roadmap items into one piece
of infra. Natural rider on the 2.B arc (shared `.olean` + persistent worker
compound).

---

## Part 3 — Smaller items

* **Retire `tactus_auto` fully** — **DONE for lean-backend crates
  2026-07-02, by owner decision ("flag decides"), same day the refactor-
  only version was found impossible.** The scoping finding stands: the
  attr's FileLoader role was per-fn **content-language marking** (exec-fn
  `proof { }` / `assert … by { }` blocks legitimately came in both Verus
  and Lean, per fn — tactus-group-theory's `runtime.rs` used attr-less
  Lean-routed exec fns with Verus ghost blocks), so no crate flag could
  *infer* the language. Danielle resolved it by **changing the
  semantics**: in a `--lean-backend` crate, block language now FOLLOWS
  ROUTING — a Lean-routed exec fn's blocks ARE Lean tactic text, no attr
  needed; `#[verifier::z3]` keeps a fn (routing and blocks) on the
  Verus/Z3 side. The Verus-blocks-in-Lean-routed-fns pattern is no longer
  a supported state; the group-theory runtime fns were `z3`-marked as the
  migration interim (commit in that crate). `tactus_auto` remains
  accepted (redundant under the flag; still the per-fn opt-in for
  non-lean-backend crates). Implementation: `file_loader.rs` pass-2 gate
  + textual routing mirror, flag threaded through both compiler-callback
  constructions, `enclosing_fn_has_lean_tactic_blocks` at the three
  TactusSpan sites, 7 unit + 3 e2e pins | `e1ddfaa`
* **Ambient thread-locals → EmitCtx** — covered in § 1.2; listed here so the
  three sites are findable: `to_lean_type.rs:294`, `to_lean_sst_expr.rs:256`,
  `to_lean_expr.rs:102`.
* **`lean_pp` via a Wadler-style pretty library** — considered, **rejected
  for now**: the hand-rolled indentation is ~710 lines of straightforward
  code, and the `Landmarks` source-map threading (which SERVER.md depends
  on) is bespoke enough that a library port is churn without clear win.

---

## Part 4 — Sequencing

```
Session 1 (tactical):   1.1 constructors → 1.2 EmitCtx → 1.3 trait_emit.rs
                        (1.4 splits opportunistically; skip krate_preamble
                         polish if 2.B is greenlit)
Arc A (before more      2.A typed-expression unification
closure-ABI work):          + write the missing DESIGN section
Arc B (own push):       2.B shared crate module, with 2.C riding along
Anytime / owner call:   1.5 comment policy; tactus_auto retirement (#3)
```

Verification protocol, every step: full e2e suite green (0 failures) + the
`lean_verify` unit tests + `cargo check -p lean_verify --tests` (the
`use super::*` lesson). Pure code moves commit separately from behavior
changes. Commit small and often.
