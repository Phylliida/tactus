---
title: "serializer arm — call-generic (vec_read/vec_push7/fill_zeros; the whole remaining fixture gap)"
status: todo
claimed_by:
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T17:15:00Z
---

## Description

Extend the bootstrap-02b Call arm to generic callees. The `call-generic`
census tag covers the 3 remaining uncertified fixture fns (vec_read /
vec_push7 / fill_zeros → fixture would reach 16/16 certified).

- The restricted arm deliberately excluded generics; the work is the
  typ-param instantiation in the post-call frame builder
  (`sst_to_lean::cert_call_leaves` + `sst_serialize::call_stm`), mirroring how
  production instantiates callee typ params at the call site (these are vstd
  Vec-method-shaped callees, so `&mut`/view interactions may surface — if a
  sub-shape is genuinely `call-mut` territory, re-tag it sharply rather than
  forcing it here).
- Same discipline as 02b: serializer builds the FrameList structure
  independently; bridge `decide` validates; mutation-kill (perturb the
  instantiated leaf/frame → bridge must flip).

**Done when:** the 3 fns emit certs and bridge-close (fixture 16/16, probe9
runner extended), or the genuinely-out-of-scope residue is re-tagged with a
written reason; suite green.

**Blocked by:** nothing.
