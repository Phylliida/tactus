# Refactoring Push — 2026-06-05 (the new HANDOFF for this push)

This push had one through-line: **stop working around Verus's SMT-shaped
decisions in Tactus, and either tidy the workaround or move the decision into
Verus where it belongs.** It started as a polish pass (golf + splitting the
megafile) and turned into an architectural one (replacing a 200-line Tactus
normalization pass with a 20-line gated Verus change, then making it a real
per-crate flag).

State at the end: **vstd 1530/0, e2e 482/0** (a plain `vargo test --test tactus`
is green — no env var). `sst_to_lean.rs` went **6689 → 5378 lines (−20%)**.

---

## Part 1 — Polish: golf + splitting the megafile

The audit (clippy + three read-only Explore passes) found the code was already
clippy-clean and the biggest line-duplication (`Exp`/`Expr` twin walkers) is
*deliberate* per DESIGN § "Two parallel expression renderers". So the real lever
was **navigability**, not byte count: carve cohesive passes out of the
6689-line `sst_to_lean.rs`.

**Golf** (`cae9e92`): two clarity-positive simplifications —
`type_bound_predicate`'s four near-identical arms collapsed to `unsigned(hi)` /
`signed(hi)` closures; the `if needs_nat_coercion {wrap} else {clone}` idiom
(6×) factored to one `coerce_arg_to_nat_{exp,expr}` helper per IR enum.

**Five new sibling modules** carved out of `sst_to_lean.rs` (all pure code
moves, re-exported so call paths + the `use super::*` unit tests stayed put):

| Module | Commit | What |
|---|---|---|
| `nat_coercion.rs` | `8a2a1d8` | the Clip{Nat} insertion pass (later *deleted* — see Part 2) |
| `broadcast_collect.rs` | `8a2a1d8` | #122 cross-crate broadcast-lemma collection |
| `mut_ref_normalize.rs` | `c8e4c6b` + `265f050` | the unified mut-ref rewrite pass **+** BorrowMut elimination (folded in) |
| `ret_subst.rs` | `265f050` | #128 ret-substitution detection (LExpr And-tree helpers) |
| `obligation_naming.rs` | `41d8310` | theorem-naming / obligation-classification metadata |

Two things learned here, worth carrying forward:
- **The unit tests reach deep into `sst_to_lean` internals via `use super::*`**
  (51 refs to the BorrowMut fns, plus `sanitize_loc_for_name`). Extractions that
  move unit-tested items need re-exports (or `#[cfg(test)] pub(crate) use`).
  *Catch them by compiling the **test** target (`cargo check -p lean_verify
  --tests`), not just the lib.*
- A couple of **back-imports** are intentional and precedented:
  `mut_ref_normalize` / `obligation_naming` import `peel_transparent` /
  `extract_simple_var_ident` back from `sst_to_lean` (which is where those shared
  SST helpers live, `pub(crate)`), the same way `nat_coercion` imported `FnMap`.

---

## Part 2 — The nat-coercion gate (the architectural win)

**The thread Danielle pulled:** "lots of our code works around decisions Verus
made that don't make sense for Lean — could we change Verus instead?"

**The case:** Verus's `fn_call_to_vir.rs` drops `uN/usize → nat` casts as no-ops
(`Ok(source_vir)`). Sound for Z3 (both are `Int`-with-refinement); wrong for
Lean (distinct `Int`/`Nat`). Tactus undid this with a ~200-line `nat_coercion.rs`
pre-pass that re-materialized the `Clip` at fn entry.

The DESIGN's recorded reason for *not* fixing it in Verus was that the **global**
change breaks 7 vstd bit-shift lemmas. Danielle's insight: make it **optional**
(gated), and that objection evaporates.

### The gate (`5b2cb7b`)

A new `--lean-backend` config flag (`config.rs`, mirroring `--emit-lean`). The
two cast-drop arms in `fn_call_to_vir.rs` now emit `mk_ty_clip(..., Nat)` when
the flag is set, drop as before when it isn't (~20 lines total). **`nat_coercion.rs`
deleted** (−202), its 8 call sites retired (`sst_to_lean` + `to_lean_fn` render
the rewritten VIR directly), the dead `fn_map` param dropped from
`spec_fn_to_ast`. The gate **subsumes the whole pass**, including the Friction-2
arith-operand case, and is strictly more uniform (covers comparisons too).

Validated by probe first: vstd build (no flag) → 1530/0 (Z3 path byte-identical);
e2e with `--lean-backend` + the pre-pass no-op'd → 482/0. *Not vacuous* — the
suite includes the `u64_as_nat` / `arith_operand_as_nat` tests, which would have
failed with the pass disabled if Verus's Clip didn't cover them.

### Why per-crate, not per-fn (the granularity question)

For exec/proof fns we *do* know the target per-fn (the `tactus_auto` / tactic-body
attr). But the cast also appears in **spec-fn bodies** (`spec fn f(x: u64) -> nat
{ x as nat }`) — shared *definitions* with no per-fn target, lowered once before
any caller is known. So the real granularity is **per-crate**: a Tactus crate
renders entirely to Lean; vstd is the Z3 crate. `--lean-backend` = "this crate
targets Lean." (Doing per-fn *after* VIR is literally the pre-pass we deleted.)

### The per-crate invariant + a deferred boundary

**A crate is either Lean or Z3, and depends only on crates of the same choice.**
The one exception is **vstd** (Z3, can't be Lean-built — its bit-shift lemmas
need the drop), which every Tactus crate uses. So a Lean crate consuming a
Z3-built dep inherits that dep's casts in their *dropped* form — its VIR is
frozen at the dep's build time. This is **latent but unhit** (vstd's spec layer
is nat/int-typed, so no `uN→nat` casts reach Lean goals), and **no worse than
before** (the old pre-pass also skipped cross-crate). If a Z3 dep with a breaking
cast ever surfaces, the fix-location is Tactus's cross-crate spec-fn inliner
(#122) — the one place that knows, per-render, "I'm emitting for Lean." Deferred.
*(Danielle's note: "pre-existing ≠ not-worth-fixing" — recorded as a known
boundary to relax later, not as acceptable forever.)*

### Per-crate wiring, two contexts (`9fea1b8`, `359d100`)

- **Real crates → Cargo.toml.** Added `lean-backend` to cargo-verus's
  `[package.metadata.verus]` reader (`cargo-verus/src/metadata.rs` +
  `subcommands.rs`), mirroring the existing `no-vstd` / `is-vstd` keys. A crate
  declares `[package.metadata.verus] lean-backend = true` and cargo-verus
  forwards `--lean-backend`. (Plumbing validated by compile + pattern-match; no
  real Lean crate exists yet to run it end-to-end.)
- **Test snippets → structural shadow.** The harness invokes verus directly (no
  Cargo.toml). Rather than sniff each test's content (rejected as fragile),
  `tactus.rs` shadows the harness's `verify_one_file` — which the
  `test_verify_one_file!` macros call by an *unqualified* name resolved at the
  call site (the reason every test file does `use common::*`) — with a one-line
  wrapper that appends `--lean-backend`. The choice is per-file ("this whole file
  is a Lean suite"); the shared Z3 test files keep `common::verify_one_file`.
  `--lean-backend` added to `run_verus`'s forward allowlist. A plain `vargo test
  --test tactus` is now 482/0 with no env var.

Docs: rewrote DESIGN § "U → Nat coercion" (now "gated Verus Clip"), updated
DECISION-cast-rendering (policy unchanged, mechanism moved), the RewritePipeline
note, and the test-run command.

---

## Part 3 — Investigations that did NOT become changes (honest record)

The "gate Verus" lever is powerful but its **clean wins are limited** — most
Tactus normalization is genuine Lean-encoding work or experimental-feature
support, not "working around a dumb Verus decision." Two probes confirmed this:

### The mut-ref "prize" — investigated, not pursued

`mut_ref_normalize.rs` (741 lines) *looked* like the next big gate win. It isn't
— it decomposes into three parts of different natures:
- **Legacy `VarAt(Pre)` rewrite** (~150 lines): a *genuine Lean need*
  (mutation-as-let-shadowing requires distinct pre-state names). Not a Verus
  artifact; can't gate away.
- **New-mut-ref ops** (~350 lines): support for Verus's *experimental*
  `--new-mut-ref` mode (off by default, 15 tests opt in via `["new-mut-ref"]`).
- **BorrowMut elimination** (~250 lines): a pure Z3 artifact, but emitted deep in
  Verus's new-mut-ref `&mut` lowering and only under that mode.

So the big chunk is experimental-feature support, not a gateable transform.
Deleting it = dropping new-mut-ref support (discards #95/#107/vec_index work +
Verus's eventual default). **Not pursued.** Recorded in DESIGN § "U → Nat
coercion" pattern note.

### `tactus_auto` redundancy — probed, ~96% redundant, NOT fully

Question: now that Lean-vs-Z3 is per-crate, is the per-fn `#[verifier::tactus_auto]`
exec-routing marker redundant? **Probe:** route *all* exec fns to Lean under
`--lean-backend` (ignore `tactus_auto`), at `verifier.rs` (routing) +
`enclosing_fn_is_tactus_auto` (proof-block handling). **Result: 475/482.** So
`tactus_auto` is ~96% redundant — but the **7 failures share one root cause**: a
`tactus_auto` Lean *caller* calling a **plain (Z3) exec fn** that does something
Lean doesn't support yet. So `tactus_auto` is really the **per-fn escape hatch to
Z3**, load-bearing where Lean's exec coverage has gaps. A pure-Lean crate is
restricted to Lean-supported features.

The 7, by gap (the probe was reverted — repo is back to 482/0):
- **Rewritable (3)** — field/tuple assignment in the callee (`h.v = h.v+1`,
  `t.0 = t.1`; "assignment with non-simple LHS not yet supported"). Rewriting the
  callee body as whole-value assignment (`*h = Holder{v: h.v+1}`, `*t = (t.1,
  t.0)`) is Lean-supported and preserves the test's focus (the caller's
  `old()`/`&mut` handling). Tests: `test_exec_call_mut_arg_whole_tuple_field`,
  `test_old_view_pre_post_substitution_probe`, `test_old_view_trait_dispatch_probe`.
- **Lean feature gap (4)** — trait-method exec bodies (`salute` / `inc` trait
  *defaults*, `check` an impl method): "Lean tactus_auto failed for …". Routing a
  trait-method exec body to Lean fails `sst_to_lean`'s coverage. Not a test edit
  — needs trait-method-exec-body verification in Lean. Tests:
  `test_exec_call_trait_default{,_overridden,_with_args}`,
  `test_inlined_ensure_references_trait_spec_method`.

**Direction (when worth it):** invert the polarity — under `--lean-backend`, make
Lean the *default* for exec fns and add a per-fn **opt-out** (`#[verifier::z3]`
or similar) for the rare fns that must stay Z3. Drops `tactus_auto` from the ~466
fns that don't need it; marks the ~7 that genuinely can't be Lean yet. Bounded,
but blocked on the trait-method-exec Lean gap (and not urgent — the annotations
are test snippets, not user code).

---

## Open follow-ups

1. **Invert `tactus_auto` → Lean-default + Z3 opt-out** (Part 3). Needs the
   trait-method-exec-body Lean gap closed first (or the 4 tests stay on the
   opt-out). Bounded; not urgent.
2. **Lean coverage gaps** surfaced by the probe: trait-method exec bodies;
   field/tuple assignment in exec bodies (already a documented deferral). Closing
   these shrinks the set of fns that need the Z3 escape hatch.
3. **Cross-crate cast boundary** (Part 2): a targeted coercion in the #122
   cross-crate inliner, if a Z3 dep with a breaking `uN→nat` spec cast ever
   appears. Latent today.
4. **End-to-end cargo-verus run** of a real `lean-backend = true` crate (none
   exist yet — the wiring is validated by compile + pattern-match only).

## Commits this push

```
359d100 test harness: pass --lean-backend for the tactus suite structurally
9fea1b8 cargo-verus: per-crate lean-backend via [package.metadata.verus]
5b2cb7b nat-coercion: replace Tactus pre-pass with a gated Verus Clip (--lean-backend)
214ec1b poems: 2026-06-05 afternoon — pure moves; the wall
41d8310 lean_verify: extract obligation naming/classification into its own module
265f050 lean_verify: extract ret-subst detection + BorrowMut elimination
c8e4c6b lean_verify: split mut-ref normalization pass out of sst_to_lean
8a2a1d8 lean_verify: split nat-coercion + broadcast-collect passes out of sst_to_lean
cae9e92 lean_verify: tidy — collapse type_bound_predicate shapes + factor nat-coercion leaf
13daf95 poems: 2026-06-05 — arriving into the pause
```
(Plus the `tactus_auto` probe — reverted, uncommitted — and the mut-ref
investigation — no change.)
