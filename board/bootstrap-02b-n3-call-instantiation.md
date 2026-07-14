---
title: "N3 follow-up — StmData::Call serialization (callee req/ens instantiation)"
status: todo
claimed_by:
created: 2026-07-13T21:20:00Z
updated: 2026-07-13T21:20:00Z
---

## Description

N3a's serializer fails loud on `StmX::Call` (census tag `call`) to keep the
trusted surface pure transcription. This task adds `StmData::Call` capture —
the one place the serializer does non-transcription work.

At the snapshot point `StmX::Call{fun, resolved_method, typ_args, args, dest, …}`
carries only the callee ref + arg exps, NOT the instantiated req/ens. The
production walker (`sst_to_lean::build_wp_call`) resolves the callee via
`fn_map` and substitutes the callee's `decl.reqs`/`enss` at the actual
`args`/`typ_args`. The serializer must render the SAME instantiated exps as
the `Call{reqs, enss}` leaf lists, plus `dest`/`dest_typ` from `dest: Option<Dest>`.

**This instantiation is part of the trusted surface** — it must be spelled out
in the `sst_serialize.rs` faithfulness contract doc-comment (it is currently
listed under "Deliberately NOT read"; move it to "Read" with the instantiation
called out explicitly).

Scope:
- Mirror `build_wp_call`'s callee resolution (`resolve_callee`) and arg
  substitution closely enough that the rendered leaves match the walker's
  (needed for the W2 bridge to `decide`-close on call-bearing fns).
- Handle the zero-arg-dummy quirk (`ast_simplify::injects_zero_arg_dummy`).
- `dest`: `dest.dest` is a Var → binder id; `dest.dest.typ` → dest_typ leaf.
  A `None` dest (unit-returning call) needs a decision — the mirror's `Call`
  always carries a `dest`; likely a synthetic unit binder or a mirror-shape
  question for DESIGN-W2-refwp.

**Done when:** `quad_exec` (the fixture Call fn) serializes; the emitted
`Call{reqs, enss, dest, dest_typ}` literal kernel-computes; census `call`
count drops to the genuinely-unsupported call shapes (trait dispatch etc.).

**Blocked by:** bootstrap-02 (N3a core) — landed. Best done alongside or just
after N3b (goal provenance), since the bridge is what pins the instantiation.

## Progress

- (2026-07-13, opus) **Considered and deliberately DEFERRED this turn** — a
  sequencing call, recorded so it isn't re-litigated blind. The Call arm is
  the one place the serializer does non-transcription work: it must reproduce
  `build_wp_call` + `resolve_callee` + the simple-case subset of
  `build_call_substitutions` (~150 lines of walker internals) *inside the
  TCB*. Facts confirmed from source:
    - Callee specs are VIR-AST `Expr`s (`spec_callee.require` /
      `spec_callee.ensure.0` via `call_inlining::collect_inlined_at_call`),
      NOT SST `Exp`s — so they render through `to_lean_expr::vir_expr_to_ast`
      / `vir_expr_to_ast_for_inlining_with_ctx`, not the serializer's
      `sst_exp_to_ast_checked`.
    - The param→arg instantiation happens at RENDER time via a `RenderCtx`
      `value_subst` map (`build_call_substitutions`, `sst_to_lean.rs:2891`),
      with distinct req/ens/pre maps and a whole mut-ref post-state /
      prophecy sub-machinery. `quad_exec` (the fixture target) is the easy
      subset: two Static, same-crate, no-`&mut`, no-generic, no-zero-arg
      calls.
    - `krate` is already threaded to `emit_cert` (currently `_krate`), so the
      fn_map is reachable at the snapshot point.
  **Why defer:** the task itself says "the bridge (W2) is what pins the
  instantiation," and W2 doesn't exist yet. Writing an unvalidated ~150-line
  substitution mirror into the *trusted* serializer, with no bridge to check
  it against the walker, cuts against the architecture's core discipline
  (TCB stays small + auditable; everything else is kernel-checked). Correct
  order: land N3b (goal side) → W2a/b (the bridge) → then this Call arm, whose
  faithfulness the bridge's `decide` immediately validates. Do it as a
  RESTRICTED arm (Static + same-crate + no-&mut only; keep trait/`&mut`/
  cross-crate fail-loud with sharper census tags) so the TCB addition stays
  small.

- (2026-07-13, opus-n3c) **Deferral re-confirmed while closing N3c** (a second,
  independent read agrees). Settles the one dangling sub-question — *"do we need
  a restricted Call arm landed BEFORE W2a, so the bridge has a real call-bearing
  cert to audit on day one?"* → **No.** W2a bring-up only needs a hand-written,
  manually-verified fixture cert (a known-good Reference/WP pair) to exercise
  the bridge mechanism; you don't need a *generated* Call cert to test a bridge.
  Landing the Call arm pre-bridge would make the TCB the *source* of truth
  rather than the *subject* of the check — exactly backwards. So this stays
  todo behind W2 (see bootstrap-06/07); no change to the sequencing.

- (2026-07-14, opus-b14-cont) **N4 census (`bootstrap-05`) quantified this
  arm's payoff — it is the highest-leverage serializer arm by a wide margin,
  but the sequencing is UNCHANGED (still behind W2b).** Cold census over both
  corpora: `StmData::Call` blocks **5 fixture + 5 tgt = 10 exec fns** (fixture
  {quad_exec, count_down, vec_read, vec_push7, fill_zeros}; tgt
  runtime::{find_cancellation_exec, copy_word, apply_hom_gen, apply_hom_inv,
  apply_hom_symbol_exec}). It is the *entire* fixture gap and 5/8 of the tgt
  exec-fn gap; the only other blocker is `assert-query` (3 tgt fns). See
  DESIGN-W2-refwp.md §1.1. This does NOT reopen the deferral — landing an
  unvalidated substitution mirror in the TCB before the W2b bridge exists is
  still backwards. It just confirms: when W2b lands, THIS is the first
  serializer arm to build (and its faithfulness is exactly what the bridge
  will `decide`-check).

## Writeup
