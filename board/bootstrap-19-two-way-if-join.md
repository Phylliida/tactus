---
title: "refWp two-way If-join — both branches fall through to a common Ret (count_down)"
status: todo
claimed_by:
created: 2026-07-14T23:20:00Z
updated: 2026-07-14T23:20:00Z
---

## Description

Stage A does NOT model the general two-way If-join (DESIGN-W2-refwp.md §2.4.1 /
lib.rs `frame_after` If arm). `frame_after(f, If)` returns the pre-If frame `f`
UNCHANGED except for the one special case `diverges(then) && is_skip(else)`
(the early-return fall-through that bootstrap-17 handled). When BOTH branches
fall through to a common continuation (the usual `if C { .. } else { .. } rest`
shape), the continuation is closed under the bare pre-If frame — it never sees
either branch's local bindings — so a common trailing `Ret` yields ONE malformed
postcondition goal where production clones the continuation into both branches
and emits TWO (one per branch frame).

**Concrete failing fixture:** `count_down` —
```rust
fn count_down(n: u64) -> (r: u64) ensures r == 0, decreases n {
    if n == 0 { 0 } else { count_down(n - 1) }
}
```
Both branches assign `tmp__3` then fall through to `return tmp__3`. Diagnosed
in bootstrap-02b (2026-07-14, opus-b02b): refWp emits **3** goals, production
**4**. Pinpoint (proved by `decide`, /tmp/pinpoint_*.lean method):
- rw goal 0 == prod goal 1 (the `n-1` bounds assert). ✓
- rw goal 1 == prod goal 2 (the recursive-call termination/decrease check). ✓
- rw goal 2 == `All n:Int, All h_n_bound, Let decrease_init0:=n, Let r:=tmp__3,
  ⟦r=0⟧` — the BARE pre-If-frame Ret postcondition, matching NEITHER prod goal 0
  (then: needs `Imp(n==0)` + `Let tmp__3:=0`) NOR prod goal 3 (else: needs the
  whole else chain incl. the call's post-frame). **Missing entirely:** prod goal
  0 (the then-branch postcondition — which has nothing to do with the Call).

This is a SOUND honest-fail (strict `goal_eq` refuses to close — no silent-pass),
currently classified in `probe-w0/probe9_bridge/run.sh` honest_fail set. It is
NOT a Call-arm bug (quad_exec, the straight-line-call fixture, closes clean); it
was SURFACED by bootstrap-02b making count_down emittable.

**Why it matters:** the two-way fall-through `if` is one of the most common exec
shapes. Leaving it a permanent honest-fail caps the certificate's reach on real
corpus code significantly (tgt exec fns are full of them). This is the natural
successor to bootstrap-16/17 (the loop / early-return fall-through fixes).

## Design question (for Danielle / whoever picks this up)

Two places the two-way join could be modeled — pick one:

1. **In refWp** (`frame_after`/`wp_stm` If arms): teach `wp_stm(Seq(If, rest))`
   to clone `rest` into BOTH branch frames (production's actual behavior —
   `push_*` clones `after` into each branch). Needs a mirror-shape decision: the
   current `frame_after(If)=f` pass-through can't express "two continuations";
   likely `wp_stm(If, ...)` must take the continuation explicitly (a CPS-ish
   reshape) OR the serializer desugars (option 2). Changes the frozen refWp
   contract — invalidates the tactus-core fn cache once, needs a
   `ref_wp_if_twoway_join` decide proof (a count_down-shaped literal, both
   branches → 2 postconds).

2. **In the serializer** (`sst_serialize`): desugar the fall-through by PUSHING
   the trailing continuation into both If branches at serialize time (emit
   `If(then;rest, else;rest)` instead of `Seq(If(then,else), rest)`), so refWp's
   existing per-branch `wp_stm(If)` produces the two postconds with no refWp
   change. Keeps refWp dumb; adds a non-transcription step to the TCB (the
   continuation clone) whose faithfulness the bridge then validates. Mirrors
   how production itself handles it (clone `after`).

Recommendation deferred — this is a real fork like the bootstrap-02b Call-shape
fork. Option 2 keeps refWp frozen and is smaller, but grows the TCB; option 1
keeps the TCB pure-transcription but reshapes the refWp contract. Whichever
lands, the acceptance is: `count_down` bridge CLOSES by decide+rfl, a
mutation-kill flips it, and `run.sh` reclassifies count_down honest-fail→CLOSE
(the runner already flags a honest-fail that suddenly closes as a
reclassify-required regression).

## Progress

- (2026-07-14, opus-b02b) Created from the bootstrap-02b count_down diagnosis
  (full pinpoint evidence above). count_down classified honest-fail in the
  bridge runner meanwhile so the fixture suite stays green.

## Writeup

(fill in when done)
