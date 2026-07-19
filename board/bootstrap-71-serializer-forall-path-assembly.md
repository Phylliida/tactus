---
title: "serializer arm — ∀-path Call assembly (FBind post frame; refWp side already proven)"
status: in_progress
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Close the deliberate bootstrap-02b deferral: the non-ret-eq (`call-forall-path`)
post-call frame. The DTO already carries the path tag; tactus-core's
`ref_wp_call_pass_through` decide proof already covers the ∀-path shape
(`FBind(dest, ret_typ, [FHyp(ret_bound)] FHyp(ens))`); only the
`sst_serialize::call_stm` assembly for it is pending.

- First add a ∀-path **fixture callee** (an ensures with no `r == E` conjunct,
  e.g. `ensures r >= x && r <= x + 1`) + a caller — without one there is
  nothing to bridge-validate (that absence is why 02b deferred it).
- Then assemble the FBind frame in `call_stm` from the DTO ingredients and
  bridge-validate: the new caller's cert must decide-close; a negative-control
  mutation (drop the ret-bound FHyp, or swap ens order) must flip.

**Done when:** the ∀-path fixture caller certifies + bridge-closes with
mutation-kill; census tag `call-forall-path` retired; suite green.

**Blocked by:** nothing.

## Progress

- (2026-07-18, fable-b74) **∀-path arm landed.** `call_stm`'s Forall
  assembly: `FBind(binder, ret_typ)` wrapping `[FHyp(ret_bound)]
  [FHyp(ens)] [FLet(dest, binder) unless use_dest_name]` — the DTO
  already carried every ingredient incl. the `use_dest_name` flag.
  F21 fixture added (clamped_inc: `ensures r >= x, r <= x + 1` — no
  ret-eq conjunct; use_clamped caller). **use_clamped certifies**;
  fixture 28/35 certified. fill_zeros re-tags `call-mut` (its loop
  push; Vec::new's ∀-path no longer the blocker).
- **Validation:** decide-close blocked by bootstrap-74 (as everywhere).
  Reduce-comparison: both sides agree through the ∀-binder with
  IDENTICAL interned props (bound=12, ens=11) and identical final leaf;
  divergence is exactly the two known N1 patterns (hyp Imp→named-All,
  let→witness pair). Frame assembly is correct pending b74 decide +
  mutation-kill.
- **tgt:** b70+b71 moved the census: call-generic 0 (was the gate),
  4× call-forall-path expected to certify with this arm (re-census in
  flight).
