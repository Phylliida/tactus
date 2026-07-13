---
title: "N2.1 — tactus-core mirror-type amendments (before N3a freezes literal shape)"
status: todo
claimed_by:
created: 2026-07-13T19:38:00Z
updated: 2026-07-13T19:38:00Z
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

## Writeup

_when done: findings, how the code works, assumptions made_
