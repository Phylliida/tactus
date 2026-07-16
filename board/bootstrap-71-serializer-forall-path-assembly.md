---
title: "serializer arm — ∀-path Call assembly (FBind post frame; refWp side already proven)"
status: todo
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
