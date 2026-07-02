# Refactoring Push — 2026-06-05 (the new HANDOFF for this push)

This push had one through-line: **stop working around Verus's SMT-shaped
decisions in Tactus, and either tidy the workaround or move the decision into
Verus where it belongs.** It started as a polish pass (golf + splitting the
megafile) and turned into an architectural one (replacing a 200-line Tactus
normalization pass with a 20-line gated Verus change, then making it a real
per-crate flag).

State at the end: **vstd 1530/0, e2e 482/0** (a plain `vargo test --test tactus`
is green — no env var). `sst_to_lean.rs` went **6689 → 5378 lines (−20%)**.

> **Continued same day → Part 4 (the trait→inversion arc).** Part 3's two
> deferred follow-ups (close the Lean coverage gaps, then invert `tactus_auto`)
> both landed. **Exec fns now verify in Lean by default under `--lean-backend`,
> with `#[verifier::z3]` as the per-fn opt-out. e2e 485/0 — the full suite
> verifies every exec fn in Lean.** See Part 4 below.

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

## Part 4 — Closing the gaps, then the inversion (continued 2026-06-05)

Part 3 left two coupled follow-ups: close the Lean coverage gaps the route-all
probe surfaced (the "7 failures"), then invert the polarity. This arc did both.
The trigger was Danielle's question — *"don't we support trait-method exec
verification?"* — and the answer turned out to be **yes, modulo a stack of real
bugs.** Re-applying the probe and chasing each "is this a gap or a bug?" to the
bottom found bugs, not gaps.

### The gap-fixes (the "7 failures" decomposed into distinct bugs)

| Commit | Fix | What it was |
|---|---|---|
| `03e1591` | `Self%` type-param sanitization | trait `Self` arrives as `"Self%"` (illegal Lean ident); `build_param_binders` / `typ_to_node` / typ-subst keys emitted it raw → unparseable. New `LeanName::typ_param` normalizes `Self%`→`Self` at all three sites. (Fixed the 3 `_default` trait tests.) |
| `a516a57` | binder-aware receiver deref | SST Field arm counted derefs from the *expression* typ (stripped), not the binder typ → `self.v` where Lean needs `self.deref.v`. Threaded the param typs (`WpCtx::caller_param_typs`) into a `RenderCtx.binder_typs` consulted at Field/IsVariant, mirroring the Exp path's `lean_level_wrap_count`. |
| `aa66508` | abstract trait-method class dispatch | a `<Self as Tr>::m` call in an inherited ensures passed type-args positionally → `Foo.predicate Bar self` (Self is implicit). Extracted `render_class_method_call`, routed both the resolved arm and the unresolved-but-trait-method arm through it → `Foo.predicate (self : …)`. |
| `26e6379` | field-path assignment | `x.f = e` / `t.0 = e` hit "non-simple LHS not yet supported". Lower to a functional update of the root var (`let x := { x with f := e }` / tuple reconstruct), reusing the `&mut x.field` call-rebind machinery (extracted `build_nested_field_update` + `decompose_assign_lvalue`). |
| `76b0218` | inherent-method naming | `impl Holder { spec fn view }` rendered as the codegen-internal `impl__0.view` (no type in the path) — un-referenceable in a proof. Naturalize to `Holder.view` from the receiver's Self type, via a once-built table consulted at the single `lean_name` chokepoint (`from_path` delegates to it, so def + call sites agree). **Danielle's catch** — "why would a proof reference impl__0? That's a bug." |
| `0856387` | struct-field bounds | a `u8` *field* (`h.v`) carried no `0 ≤ v < 256`, so an overflow on a field read couldn't close. `type_bound_predicate` now recurses into single-variant-struct + tuple fields (with a recursion guard; enums excluded — variant-conditional). |

Two of those (`Self%`, deref, dispatch) were the trait-method-exec gap; field-
assignment + naming + field-bounds were the `old_view` tests. Every spec-method
unfold landed as a **visible** body proof (`proof { simp_all [Holder.view] }` /
`[Foo.predicate]` / `[View.view]`) — never a silent closer rung (rejected an
`assumption`/defeq rung as hiding the unfold) and never `tactus_tactic("…")`
(the string-attr hack Danielle wants gone). The transparency bar held.

### The inversion (`41db9bb`)

With the full suite green under the route-all probe, Part 3's "Direction" was no
longer a probe — it was correct. Productionized:
- **`--lean-backend` crate → exec fns verify in Lean BY DEFAULT.** Opt back out
  with **`#[verifier::z3]`** (new attr, full plumbing mirroring `tactus_auto`:
  `Attr::TactusZ3` → `VerifierAttrs.tactus_z3` → `FunctionAttrs.tactus_z3`, read
  by `verifier.rs` routing). Pinned by `test_exec_z3_opt_out` (a spec-fn-ensures
  fn that verifies *only* because z3 routes it to Z3's fuel-1 auto-unfold).
- **non-lean-backend crate → Z3 default,** `tactus_auto` = legacy opt-IN.

`tactus_auto` is now redundant for routing under lean-backend but **remains the
FileLoader's proof-block / assert-by marker** (tree-sitter at file-load, before
flags) — so a Lean-routed fn with a Lean-tactic body proof still needs it today.
Documented in DESIGN § "Exec-fn routing: Lean-default under --lean-backend".

### Deferred / known-incomplete (Part 4)

Everything knowingly left for later, by area. All of these are **sound**
(incompleteness, not unsoundness): a missing bound just means a goal that
*could* close doesn't, never a false goal that does. The full suite is green
because the current tests don't hit these corners.

**Struct-field bounds (`type_bound_predicate` datatype recursion):**
- **Multi-variant enums — excluded.** Enum field access is variant-guarded
  (`Mk_val0`, not `val0`) and the bound is variant-conditional (`is_variant A →
  …`). `install_datatype_field_bounds` only maps single-variant *eponymous*
  datatypes (= structs). [Same as follow-up #2.] Including them produced
  malformed projections — caught by `test_exec_single_variant_non_eponymous_enum`
  + `_scc_plus_standalone_datatype` during the arc.
- **`&T` (immutable-ref) datatype params — no field bounds.** Works for
  by-value and `&mut` params; for `&Holder` the bound would need a `.deref`
  inserted when peeling the `Decorate(Ref)` (the value is `Tactus.Ref`-wrapped),
  which `build_param_binders` pre-does only for `&mut` (it deref's `bound_value`),
  not `&`. So `type_bound_predicate` doesn't peel `Decorate(Ref)` (peeling without
  the deref would type-mismatch). No current test needs it (`get(h: &Holder)` does
  no field arithmetic).
- **Generic struct fields — no bound.** `Pair<T> { a: T }` field typ is a
  `TypParam` → `None` (no `typ_args` substitution into field typs). Concrete-typed
  fields (`u8`, etc.) of a generic struct still get bounds; only the type-param
  fields are skipped.
- **Recursive / self-referential fields — no bound.** `List { next: Box<List> }`:
  the `visited` set stops the recursion at the self-reference, so `next`
  contributes no bound (the leaf scalar fields still do).
- **Accessor logic duplicated.** The builder replicates `field_access_name`'s
  single-variant case inline (`valN` / `sanitize(name)`) rather than calling it —
  fine for eponymous structs, small drift risk if `field_access_name` changes.

**Trait-method class dispatch (`render_class_method_call`):**
- **Cross-crate abstract trait calls — old behaviour.** `fun_is_trait_method`
  consults the RenderCtx `fn_map`; a trait method *not* in the map (cross-crate)
  falls back to the prior positional rendering. Same-crate `<Self as Tr>::m` is
  fixed; cross-crate is unchanged (latent, as before).
- **Recursive trait-method calls — not routed.** Only `Fun(_, None)` (and the
  resolved `Fun(_, Some)`) route through class dispatch; a `CallFun::Recursive`
  to a trait method keeps positional typs. Edge case, no test.

**Field-path assignment (`decompose_assign_lvalue` + `build_nested_field_update`):**
- **Enum field assignment — still rejected.** The decomposer accepts single-
  variant-struct / tuple field paths; a multi-variant enum field LHS returns
  `None` → the "non-simple LHS" rejection stands.
- **No rhs coercion at the field slot.** The rhs is rendered as-is (common case:
  same typ). A wrapper-typed field assignment (e.g. assigning into a `Box<_>`
  field where the rhs needs a `.mk` wrap) is untested — would need the
  `coerce_lexpr` bridge the call-rebind path has.

**Routing / `tactus_auto`:**
- **Full `tactus_auto` retirement** — ~~blocked on the FileLoader~~
  **INVALIDATED 2026-07-02**, see follow-up #3 below.
- **`enclosing_fn_is_tactus_auto` not lean-backend-aware.** Re-read
  2026-07-02: **this is correct behavior, not a gap.** Under the settled
  semantics an attr-less fn's `assert(..) by { }` content IS Verus proof
  code (the supported group-theory `runtime.rs` pattern); only the attr
  declares the content to be Lean tactics. The FileLoader and this gate
  agreeing on the attr is the consistency requirement, not a coupling to
  delete.

**Considered and rejected (decisions, not deferrals):**
- **`assumption`/defeq closer rung** for spec-fn unfold — validated it works
  (defeq unfolds transparent defs, respects `@[irreducible]`), but rejected: it
  unfolds *invisibly*, the "and then something happened" anti-pattern design
  principle #1 forbids. The visible body proof is the chosen path.
- **Codegen auto-emitting `unfold f`** (a transparent fuel-equivalent) —
  considered as a middle ground; not chosen. The manual `proof { simp_all [f] }`
  is the established pattern (dozens of `unfold f; omega` tests) and keeps Tactus
  fuel-free.
- **`#[verifier::tactus_tactic("…")]`** string-attr for the body proofs — Danielle
  wants it deprecated ("the string thingy seems like a hack"); used in-body
  `proof { }` blocks throughout instead.

---

## Open follow-ups

1. ~~Invert `tactus_auto` → Lean-default + Z3 opt-out~~ **DONE (Part 4, `41db9bb`).**
2. ~~Lean coverage gaps (trait-method exec bodies; field/tuple assignment)~~
   **DONE (Part 4).** Remaining sub-gap: **multi-variant enum field bounds** —
   `type_bound_predicate` only recurses into single-variant structs + tuples
   (enum field access is variant-guarded, so the bound is variant-conditional).
3. ~~**Fully retire `tactus_auto`.**~~ **INVALIDATED 2026-07-02** (scoped for
   implementation — see REFACTORING2.md Part 3). The premise "sanitize any
   Lean-routed fn's proof blocks" is wrong: attr-less Lean-routed exec fns
   legitimately carry **Verus**-style proof blocks (tactus-group-theory
   `runtime.rs` — the WP consumes the ghost statements as SST statements).
   The attr is per-fn content-language marking, which a crate flag cannot
   replace. Retirement would need block-level syntax (owner's language call).
4. **Cross-crate cast boundary** (Part 2): a targeted coercion in the #122
   cross-crate inliner, if a Z3 dep with a breaking `uN→nat` spec cast ever
   appears. Latent today.
5. **End-to-end cargo-verus run** of a real `lean-backend = true` crate (none
   exist yet — the wiring is validated by compile + pattern-match only).

## Commits

**Parts 1–2 (the gate + polish):**
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
(Plus the original `tactus_auto` probe — reverted; the mut-ref investigation — no change.)

**Part 4 (gap-fixes + the inversion):**
```
1d3eb00 DESIGN: document the exec-fn routing inversion (Lean-default + #[verifier::z3])
41db9bb verifier: invert exec routing — Lean-default under --lean-backend + #[verifier::z3] opt-out
0856387 lean_verify: materialize struct-field bounds (0 ≤ h.v < 256 for u8 fields)
3fe3442 test: pin inherent-method naming via a tactus_auto exec fn (Holder.view)
76b0218 lean_verify: naturalize inherent impl method names (impl__0.view → Holder.view)
26e6379 lean_verify: lower field-path LHS assignment to a functional update
aa66508 lean_verify: render abstract trait-method calls via class dispatch (+ trait-exec-in-Lean test)
a516a57 lean_verify: binder-aware receiver deref for exec body/ensures field access
03e1591 lean_verify: sanitize trait `Self%` type-param in exec/proof theorem binders
```
(The route-all probe was re-applied to drive Part 4, then retired into the
committed `41db9bb` routing — no longer uncommitted.)
