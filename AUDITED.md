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
`broadcast_collect.rs`, `call_inlining.rs`, `crate_defs.rs`, `dep_order.rs`,
`driver_client.rs`, `emit_ctx.rs`, `expr_shared.rs`, `generate.rs`,
`impl_subst.rs`, `inline_spec.rs`, `lean_ast.rs`, `lean_name.rs`,
`lean_pp.rs`, `lean_process.rs`, `link_discharge.rs`, `loop_normalize.rs`,
`nonempty.rs`, `prelude.rs`, `project.rs`, `ret_subst.rs`, `sanity.rs`,
`script.rs`, `sourcemap.rs`, `source_util.rs`, `sst_serialize.rs`,
`sst_to_lean.rs`, `tactic_select.rs`, `to_lean_expr.rs`, `to_lean_fn.rs`,
`to_lean_type.rs`, `trait_emit.rs`, `typed_expr.rs`

(Many of these have unit-test coverage, which is why the 2026-07-25 arc
prioritized the four files above — they had none.)

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
