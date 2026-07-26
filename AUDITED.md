# AUDITED.md — lean_verify line-audit coverage

Tracks which `source/lean_verify/src/` files have received a careful line-by-line
audit, so future sessions know where the eyeballs have and haven't been.

## Audit arc: 2026-07-25 (committed as `e2e898f`, suite 555/0, unit 417/0)

Scope: the four unit-test-free lean_verify files. Findings and fixes are
detailed in the `e2e898f` commit message; open follow-ups listed below.

### Line-by-line audited

| File | Outcome |
|---|---|
| `to_lean_sst_expr.rs` | 3 fixes: SST `HasResolved` collapse (now `Tactus.hasResolved`); `type_bound_predicate` ignoring `TypX::Decorate` (wrapper decorations get `.deref`, MutRef-decoration must not); while-cond `&mut` soundness gate (`cond_setup_user_mutation`) |
| `wf_synth.rs` | 1 fix: `subst_pp` unbounded textual fixpoint capped (honest Lean-level failure instead of hang) |
| `mut_ref_normalize.rs` | Audited, no fix applied. Open follow-up: `rewrite_varat_for_mut_params` is a single post-order pass — the `MutRefFuture(VarAt(x,Pre))` rewrite-order race the SST side two-pass-splits around would be unsound if that shape ever reached AST inlining. Tripwire probe: `audit_probe_mut_arg_false_assert_fails` (green ⇒ shape unreachable today). Defensive fix = mirror the SST two-pass split. |
| `obligation_naming.rs` | Audited clean, no findings |

### Touched while chasing fixes (not full audits)

- `sst_to_lean.rs` — `/- @rust:LOC -/` marker fix: paths containing `/-` nested a Lean block comment, making the generated file unparseable; pp now sanitizes comment text
- `script.rs`, `typed_expr.rs`, `to_lean_expr.rs`, `lean_pp.rs`, `loop_normalize.rs`, `lib.rs` — incidental edits supporting the fixes
- `sst_serialize.rs` — form-C self-referential hoist-eq blowup guard (`apply_let_substs` filters self-refs + 1MB pp growth guard); fixed the pre-existing 81GB runaway in `test_exec_call_mut_arg_whole_tuple_field`
- `rust_verify_test/tests/tactus.rs` — tripwire probes added (`audit_probe_while_cond_mutation_unsound`, `audit_probe_mut_arg_false_assert_fails`, …)

### Not yet line-audited

Everything else in `source/lean_verify/src/`, notably:
`broadcast_collect.rs`, `crate_defs.rs`, `dep_order.rs`,
`driver_client.rs`, `emit_ctx.rs`, `expr_shared.rs`, `generate.rs`,
`impl_subst.rs`, `inline_spec.rs`, `lean_ast.rs`, `lean_name.rs`,
`lean_pp.rs`, `lean_process.rs`, `link_discharge.rs`,
`nonempty.rs`, `prelude.rs`, `project.rs`, `sanity.rs`,
`script.rs`, `sourcemap.rs`, `source_util.rs`, `sst_serialize.rs`,
`sst_to_lean.rs`, `tactic_select.rs`, `to_lean_expr.rs`, `to_lean_fn.rs`,
`to_lean_type.rs`, `trait_emit.rs`, `typed_expr.rs`
(2026-07-26 arc moved `loop_normalize.rs`, `call_inlining.rs`,
`ret_subst.rs` up to audited.)

(Many of these have unit-test coverage, which is why the 2026-07-25 arc
prioritized the four files above — they had none.)

## Audit arc: 2026-07-26 (committed as `77f7fea`, suite 560/0, unit 425/0)

Scope: `loop_normalize.rs`, `call_inlining.rs`, `ret_subst.rs` — chosen as the
soundness-critical unit-test-free remainder (transform pre-pass + inlining
definitions + capture-bug habitat).

### Line-by-line audited

| File | Outcome |
|---|---|
| `loop_normalize.rs` | Pass itself audits clean (break targeting, `continue` semantics, post-order rewrite, cert mirror at `sst_serialize` all check out). But its "one set of walkers sees everything" premise exposed a walker gap — see finding below. Robustness note: the `debug_assert!(original_cond.is_none())` silently overwrites `original_cond` in release builds if Verus ever starts setting it. |
| `call_inlining.rs` | Audited clean. Both consumers (`sst_to_lean::resolve_callee`/`walk_call`, `dep_order::collect_references`) genuinely route through it; trait-default calls (#96) coherently use the trait method decl; `same_fn` guard prevents #86 double-count on the dep-order fallback path. Footnote: `ensures_shape_summary` (closer telemetry, `sst_to_lean.rs`) reads `callee.ensure` directly without the spec-source redirect — heuristic-only, no soundness impact. |
| `ret_subst.rs` | Audited clean (33 lines post-P3). `is_trivial_true` can only err toward keeping a redundant `True` hyp (sound). |

### Finding fixed (soundness): loop havoc missed call-borne mutations

`sst_to_lean::collect_modifications` had no `StmX::Call` arm, so a loop-body
mutation performed *by a call* never entered the havoc set and the post-loop
continuation kept the pre-loop binding — false post-loop asserts verified:

1. **Call-dest writes** — `x = f()` with a simple-var LHS lowers to
   `Call { dest: x, is_init: false }` with no separate Assign
   (`ast_to_sst` `direct_assign`). Both mut-ref modes affected.
2. **Legacy-mode `&mut` args** — `f(&mut x)` passes a `Loc`-shaped L-value
   with no linkage Assign (new-mut-ref mode was covered via its linkage
   Assigns, which is why the 2026-07-25 pins — all `["new-mut-ref"]` —
   stayed green over this gap).

Straight-line code was never affected (per-path `Wp::Call` rebinding is
correct); the gap was loop-havoc-specific. The while-cond shape stayed sound
even in legacy mode via the exit-side setup replay. Fixed by adding the
`StmX::Call` arm (dest root + `Loc`-shaped arg roots); cert lane re-derives
via the same function so both lanes stay coherent. Pinned by
`audit_probe_loop_call_dest_havoc{,_nmr}`,
`audit_probe_loop_mut_arg_havoc_legacy`, plus positive twins in
`test_exec_loop_call_mutations_verify`.

### Open follow-ups from the 2026-07-26 arc (reported, not fixed)

- `original_cond` silent overwrite in release builds (see table) — consider a
  hard error instead of `debug_assert!`.
- `count_breaks_targeting_this_loop` and `collect_modifications` both rely on
  `_ => {}` default arms over `StmX` — sound today (`DeadEnd`/`AssertQuery`
  bodies are proof code, no breaks/persistent exec assigns), but a new
  Stm-carrying variant would be silently skipped. Consider exhaustive matches
  per the DESIGN upstream-robustness pattern.
- Ghost-mutation loop probe (`proof { g = 0; }` in a body) fails in the sound
  direction but with several in-body obligation errors that look like
  incompleteness noise — worth a look separately.
- Bootstrap fixture: cert-bearing fns whose loops call functions now get
  additional havoc binders in their serialized WP — re-run the bootstrap
  probe battery before trusting old fixture certs (expected: honest
  regeneration, no soundness issue).

## Open follow-ups from the 2026-07-25 arc (reported, not fixed)

- `rewrite_varat_for_mut_params` single-pass race (see table above)
- Full while-cond mutation support: walk cond in both pre-passes + iteration
  havoc for cond-modified locals + decrease-snapshot convention; the
  `cond_setup_user_mutation` gate stays until then
- `collect_choose_rec` skips choose-in-Let-values (proof help lost, documented)
- `HeightCompare` non-strict renders `l = r` vs AIR's `height(l)=height(r)` —
  stronger, sound in obligation position; revisit if `is_smaller_than`-eq ever
  lands in assume position
- `Validated::check` validates with an empty `RenderCtx` but `lower_with_ctx`
  renders with a real one — no ctx-dependent Err today; keep true when adding arms
