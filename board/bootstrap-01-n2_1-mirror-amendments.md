---
title: "N2.1 — tactus-core mirror-type amendments (before N3a freezes literal shape)"
status: done
claimed_by: opus-n2.1
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T20:40:00Z
---

## Description

Amend `tactus-core/lib.rs` (bootstrap branch / tactus-bootstrap worktree) with
the fields the reference WP needs — discovered by writing refWp's equations on
paper. **Must land before N3a**, or the serialized literal shape churns.

Spec: `DESIGN-W2-refwp.md` §0 (amendment table) + §2.1 (shapes).

Amendments:
- `If(cond, neg_cond, then, else)` — add the rendered `¬cond` leaf (else-branch
  hypothesis; refWp can't synthesize leaf ids).
- `Loop{invs, cond, neg_cond, binders, body}` — add loop-state binder list
  (new `BinderList` of `(id, typ_leaf)`) + `neg_cond` leaf.
- `Call{reqs, enss, dest}` — add `dest` binder id + typ leaf.
- `Ret(LeafList)` — instantiated-ensures leaves.
- Params: each carries an optional bound-hyp leaf (`h_x_bound`).
- New `FnCtxData` (params/param_bounds/reqs/enss) and `FnCtxData.typ_params`
  ((binder id, kind leaf); instance binders `[Nonempty A]` as ordinary entries
  with distinguished leaves — **generics are required for any real corpus**).
- **`CtxFrame` = single ordered `FrameList`** (`FNil | FBind | FHyp | FLet`),
  NOT three parallel lists — the production telescope interleaves binders,
  hyps, and lets (P6/P7 evidence). This was a spec defect caught in review.

Rules (same as N2): no mutual recursion (all new lists leaf-only or one-way),
`#[verifier::structural_decreases]` on every recursive spec fn, extend the
in-crate `decide` sanity proofs, update the vir-growth tripwire table note.

**Done when:** tactus-core verifies 0 errors under the package gate (live Lean);
`decide` sanity proofs cover the new shapes; N2 acceptance re-run green.

**Blocked by:** nothing — this is the next actionable brick.

## Progress

- (2026-07-13) Baseline confirmed: `tactus-core/lib.rs` package gate 6/0 pre-change.
  Verified no external references to the mirror types (`grep` over
  `source/lean_verify/src` clean except the tripwire), so field shapes are
  free to change without downstream churn — the serializer (N3a) doesn't
  exist yet.
- (2026-07-13) Implemented all §0 amendments in `tactus-core/lib.rs` (see
  Writeup for the shape table). Package gate now **10/0** (live Lean); new
  `amended_shapes_kernel_compute` `decide` proof exercises every new shape.
- (2026-07-13) Tripwire `bootstrap_coverage.rs` still green
  (`stage_a_coverage_is_pinned` passes) — added a scope note there since it
  tracks StmX *variants*, and N2.1 only enriched *fields* within already-
  covered variants.
- (2026-07-13) Second-opinion pass (local model) on the frozen shape: confirmed
  Loop binders must be `(id,typ)` (already so), Assign needs no type leaf
  (FLet infers), and flagged a possible `FnCtxData.return_var` — deliberately
  NOT added (spec bakes return value into `Ret` leaves; fall-through case is
  OPEN §5.2). Sharpened §5.2 of `DESIGN-W2-refwp.md` with that breadcrumb.

## Writeup

**What changed** — `tactus-core/lib.rs`, per `DESIGN-W2-refwp.md` §0/§2.1:

| Shape | Before | After |
|---|---|---|
| `If` | `If(cond, then, else)` | `If(cond, neg_cond, then, else)` — rendered ¬cond leaf |
| `Loop` | `{invs, cond, body}` | `{invs, cond, neg_cond, binders, body}` — ¬cond leaf + loop-state `BinderList` |
| `Call` | `{reqs, enss}` | `{reqs, enss, dest, dest_typ}` — result binder id + its typ leaf |
| `Ret` | `Ret(u64)` | `Ret(Box<LeafList>)` — one instantiated-ensures leaf per postcond |

**New datatypes:**
- `BinderList = Nil | Cons(id, typ_leaf, tail)` — reused for value-param
  telescopes, typ-param telescopes (kind leaf in slot 2, incl. `[Nonempty A]`
  instance binders as ordinary entries), and Loop binders.
- `ParamBoundList = Nil | NoBound(tail) | Bound(leaf, tail)` — per-param
  optional `h_x_bound` leaf, parallel to `FnCtxData.params`. Distinct
  constructors instead of a sentinel id (0 is a valid interned leaf).
- `FrameList = FNil | FBind(id,typ,tail) | FHyp(leaf,tail) | FLet(id,val,tail)`
  + `type CtxFrame = FrameList`. THE single ordered goal spine — interleaves
  binders/hyps/lets so `∀x, h → let y := e; h2 → …` order is preserved (the
  three-parallel-lists defect the DESIGN §2.1 review caught).
- `FnCtxData { typ_params: BinderList, params: BinderList,
  param_bounds: ParamBoundList, reqs: LeafList, enss: LeafList }` — non-recursive
  struct, the refWp context seed.

**How it verifies:** every new list is self-recursive-via-`Box` only (no mutual
recursion — StmData→BinderList/LeafList and GoalList→GoalData stay one-way),
so `#[verifier::structural_decreases]` applies to each new size fn
(`binder_len`, `param_bound_len`, `frame_len`) and the amended `stm_size`.
`FnCtxData` holds datatypes by value (no `Box`, not recursive). The emitted
Lean defs kernel-compute: `amended_shapes_kernel_compute` closes by `decide`
over Loop/Call/Ret sizes and the new-list lengths, and a `fnctx_arity`
projection over a fully-populated `FnCtxData`.

**Design decisions / assumptions:**
- `Call` carries `dest_typ` even though §2.1's shorthand writes `Call{…dest}`;
  the amendment table (§0) says "dest binder id + typ leaf" and `frameAfter`
  needs the typ to build `FBind(dest, dest_typ, …)`. refWp can't synthesize
  the leaf, same rationale as `If`'s neg_cond.
- `Ret` leaves are pre-instantiated at the return value at render time
  (§0/§2.2), so no return-variable frame binder is modeled. See §5.2 note.
- `CtxFrame` is a `type` alias; it emitted with 0 errors (no separate
  inductive — `FrameList` is the emitted datatype).

**Battery:** tactus-core package gate **10/0** (was 6/0); lean_verify
`bootstrap_coverage::stage_a_coverage_is_pinned` **1 passed**.

**Unblocks:** bootstrap-02 (N3a) — the literal shape is now frozen.
