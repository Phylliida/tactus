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

## Writeup
