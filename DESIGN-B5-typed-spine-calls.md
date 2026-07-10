# B5: Calls report actual — completing the typed spine at call nodes

**Date:** 2026-07-10
**Status:** SPEC ONLY — nothing implemented. Written for a fresh session to execute.
**Scope:** the `Invalid field deref` family (55 errors crate-wide, ~25 in britton —
**every single `Invalid field` error in the post-fix run is this one bug**) plus its
exec-path sibling `BUG-call-arg-temp-claimed-typ.md`. Companion to
`DESIGN-lean-all-proofs-bugs.md` (B5 entry, rediagnosis 2026-07-09) and
`DESIGN-typed-renderer.md` (P1/P2 program — this is the natural P3).
**Disjoint from** `DESIGN-lean-all-proofs-followons.md` F1–F7 (deliberately not
covered there).

---

## 1. Problem

Live example (post-fix full-crate run, `lemma_t_free_step_is_base_step`, britton.rs:262):

```
Invalid field `deref`: The environment does not contain `lib.option.Option.deref`
  presentation.apply_step (hnn.hnn_presentation data) w step
has type
  option.Option (seq.Seq symbol.Symbol)
```

**Mechanism.** `exp_to_typed` (`to_lean_sst_expr.rs:603`) is the typed spine: each
migrated arm returns `(rendered value, ACTUAL typ)`, and the Field / IsVariant arms
count `.deref`s from the base's actual typ (`count_ref_decorations(base.typ())`).
`ExpX::Call` is **unmigrated** — it falls to the catch-all (`to_lean_sst_expr.rs:741`):

```rust
_ => TypedExpr::from_untyped(LExpr::new(exp_to_node_checked(e, ctx)?), e.typ.clone()),
```

i.e. calls report their SST **claimed** typ. The claim lies by one ref-decoration
when the call sits in an inlined `&self` receiver position: Verus inlines
`opt.is_some()` to `opt is Some` and re-types the receiver exp at the method's
`self` param typ — `Decorate(Ref, Option<T>)` — while the rendered spec-fn call
has the callee's declared return typ, bare `Option T`. IsVariant counts 1
ref-decoration off the claim → `.deref` lands on a bare `option.Option` →
"Invalid field". A Var receiver doesn't hit this (the Var arm reports the
binder's DECLARED typ — actual); only call-valued receivers do.

**Two sub-items from the original B5 list are already closed:** the
`Invalid projection … has type Int` family (prop_v.rs, 10 errors) is **0** in the
post-fix run — B2's choose rework fixed it, as the plan predicted ("investigate
during B2"). Heartbeats timeouts stay parked (perf is noise until the families are
done). What remains of B5 is exactly the deref family + the exec sibling.

## 2. The exec-path sibling (same root, different site)

`BUG-call-arg-temp-claimed-typ.md` (OPEN since 2026-07-04, probe-verified) is the
same claimed-vs-actual lie on the **exec obligation** path: a call's return dest
(`tmp__1`) binds via `push_ret_frames`, whose non-integer branch SKIPS the
`coerce_lexpr` bridge ("numeric sorts don't apply" — conflating sort-bridging with
wrapper-bridging), so a bare `TypParam(T)` value flows into `Decorate(Ref, T)` slots
un-wrapped. Its doc already names the real fix: **a typed
`render_call_ensure_expr`** returning value + actual typ, then a unified
`push_ret_frames` bridge. That is this same design — the spine extended through
calls — landing on the call-ENSURES path instead of the call-EXPRESSION path.

Pinned by `test_exec_vec_field_index_clone` (currently asserted `Err`; flip to `Ok`
when fixed). ⚠️ Re-baseline before starting: the exec gate is now 24/0 and
`apply_hom_symbol_exec` passes (post B1–B4), so the bug's gt manifestation may have
shifted; the unit test is the stable pin.

## 3. Fix design

### B5a — spec side: migrate `ExpX::Call` (+ `CallLambda`) in `exp_to_typed`

**The rule:** a call's actual typ is the callee's **declared return typ,
instantiated with the call-site typ args**.

- Callee lookup: `ctx.fn_map` — **already present on `RenderCtx`**
  (`expr_shared.rs:107`), no new threading. (Verify `RenderFnMap` exposes the
  declared ret typ; if a caller constructs `RenderCtx` without fn_map on a path
  that renders calls, fall back to claim — status quo.)
- Instantiation: `vir::sst_util::subst_typ` (`sst_util.rs:92`) with the map
  `callee.typ_params ↦ call-site typs` (the `ExpX::Call`'s typ args).
- **Trust guard (Box/Unbox precedent, same file):** only override the claim when
  the instantiated declared typ and the claim differ **by decorations only**
  (equal after `peel_typ_wrappers`/strip-decorations on both). Poly/boxing
  discrepancies are the Box arm's domain — overriding on those would relocate
  lies, which is exactly how the reverted spot-fix in the sibling bug doc failed
  (apply_hom 9→5 but find_cancellation 0→4). When the guard fails: keep the
  claim, unchanged behavior.
- `ExpX::CallLambda`: same rule; declared ret = the head's `TypX::SpecFn` return.
- Interaction check: inlined bodies render receivers via `ctx.value_subst`
  ("actual == claimed by construction" per the Var arm) and `ctx.inlining`
  suppresses ReadPlace lifts — confirm a Call INSIDE an inlined body isn't
  double-bridged (probe, don't reason).

**Empirical-first probes (before any behavior change):**
1. Minimal repro in the test suite: spec fn returning `Option<T>` + a use of
   `f(x).is_some()` (or `matches`) — should emit `.deref` on bare Option today.
2. A probe `eprintln` at the Call fallback comparing claim vs instantiated-declared
   across a britton `--lean-all-proofs` run: measures the lie population and the
   guard's coverage before the fix flips anything.

**Size: S→M.** One arm + a small shared helper; the helper may also serve the VIR
path (`to_lean_expr.rs` `structural_typ` — check parity; the same inlined-receiver
shape exists there).

### B5b — exec side: typed call-ensures path

Per the sibling doc's "real fix" paragraph, in `sst_to_lean.rs`:
- `render_call_ensure_expr` gets a typed variant returning `(LExpr, Typ /*actual*/)`
  — the eq-extraction carries the actual typ of what it rendered.
- `push_ret_frames` unifies its two ret families through `coerce_lexpr(actual →
  ret.typ)` — wrapper-bridging AND sort-bridging, no non-integer skip.
- Expected fallout (pre-diagnosed in the bug doc): gt's `find_cancellation_exec`
  site tactics re-tuned to correctly-wrapped shapes; the "blanket shell instances"
  tripwire (`Fields missing: clone`) needs its own small fix — emit the class as
  shell iff its instances will be shells (one predicate, two consumers).
- Debug aids listed at the bottom of the bug doc (TACTUS_DEBUG_ARGS/WP eprintln
  sites) — re-add temporarily while working.

**Size: M.** Riskier than B5a (exec gate is the crown jewel); its own validation
cycle.

## 4. Sequencing & validation

**B5a first** — small, self-contained, kills a complete error family. **B5b
second**, separate commit(s), possibly a separate session. Independent of F1–F7
(any order); B5a is the highest value-per-risk item left in the bug families.

Per-step gates (the standard loop from the bugs doc):
1. `cargo test -p lean_verify` + the new repro tests.
2. Britton module `--lean-all-proofs`: expect `Invalid field` 25 → **0**, no new
   families, auto/deref-adjacent counts otherwise stable.
3. Exec gate (committed check.sh path): 24 verified / 0 errors — compare
   **locations not counts** (`reference_tgt_gate_baseline_errors`).
4. Tutorial gates.
5. Full-crate measurement only rides the F7 measurement (after F3/F4 too — they
   change the population more than B5 does).

## 5. Risks

- **Guard too loose** (override where declared also lies): decoration-only
  comparison + probe-first keeps this bounded; worst case is status quo per node.
- **Direction symmetry**: claims usually ADD a decoration vs declared (receiver
  inlining), but a spec fn declared `-> &T` would invert it; the rule as stated
  handles both directions identically (it just reports declared).
- **Double-peel with pre-B5 workarounds**: if any site already compensates
  (hand-inserted deref counts against claims — e.g. `binder_typs` consultation at
  Field/IsVariant per its doc comment), fixing the base typ could over-correct
  there. The britton re-run catches this class immediately (family would go
  negative-to-positive, not to zero).
- **B5b relocation risk**: the reverted spot-fix showed partial bridges MOVE the
  lie. B5b must land the typed ensure-render and the unified bridge together, with
  `test_exec_vec_field_index_clone` + gt gate as the pins.
