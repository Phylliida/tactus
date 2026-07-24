---
title: "serializer arm — call-generic (vec_read/vec_push7/fill_zeros; the whole remaining fixture gap)"
status: done
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

## Progress

- (2026-07-18, fable-b74) **Generic gate lifted — vec_read certifies,
  precondition goal decide-closes byte-for-byte, mutation-killed.**
  The plumbing already existed: `build_call_substitutions` takes
  `typ_args` → `typ_subst`; requires substitute it (Phase D), ensures
  get it via `build_ens_post_render_subst`. The one real gap: `ret.typ`
  sites saw a bare `TypParam` — fixed by computing `ret_typ_subst` at
  the VIR level (`vir::sst_util::subst_typ`, mirroring production's
  dest-let binder typ site) and using it for `type_bound_predicate`
  (both paths), `coerce_lexpr` (ret-eq), and `typ_to_expr` (∀-path).
- **Validation** (pre-b74-reconciliation scope): full-goals bridge is
  blocked by the N1-hoist divergence (bootstrap-74, ALL fixtures
  affected) — so validated the head goal alone: `goal_eq` on the Call
  PRECONDITION goal decide-closes against production, and perturbing
  the transcribed req atom (Var 16 → 15) flips it to disproven.
  Goal 2's divergence is exactly the known b74 pattern (dest-lets →
  witness/eq-hyp binder pairs), nothing call-specific.
- **Re-tags:** vec_push7 → `call-mut` (prophecy/rebind machinery,
  genuinely out of restricted scope — the card's sanctioned re-tag);
  fill_zeros → `call-forall-path` — it is bootstrap-71's fixture
  customer for free (Vec::new ensures has no `r == E` conjunct).
  Fixture: 14 certs (+vec_read).
- Remaining for done: full vec_read bridge-close after b74 lands; tgt
  re-census (in flight); suite green (in flight).
- (2026-07-18, fable-b74) **tgt payoff confirmed: exec wp-cert corpus
  1 → 3** — runtime.apply_hom_gen + runtime.apply_hom_inv certify
  (b70 generic gate + b71 ∀-path together took them through); census
  267/1649, call-generic AND call-forall-path both zero, one call-mut
  (copy_word) left in runtime. Full bridge-close of the new certs
  pends bootstrap-74.

- (2026-07-24, fable-endgame-A1) **CLOSED via probe38
  (`probe-w0/probe38_b70_b71_close/`, endgame A1).** Post-b74 evidence,
  live certs: **vec_read goal 0 — the generic-instantiation Call
  PRECONDITION goal — decide-closes per-goal** (`gl_nth_eq … 0 = 1`)
  and the req-atom perturbation kill flips it (the pre-b74 head-goal
  validation, re-established through the reconciled telescope). Goal 1
  (Ret) is the documented stage-B honest-fail (view-call deref +
  Int.ofNat CallN coercion — endgame A7) and is held by an `=0`
  TRIPWIRE in the probe: it fires loud when the A7 vocabulary lands.
  Sanctioned re-tags stand: vec_push7 → `call-mut`, fill_zeros →
  `call-mut`; tgt census call-generic = 0. Suite 551/0, gate 231/0
  (2026-07-24 battery).
