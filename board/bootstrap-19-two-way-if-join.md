---
title: "refWp two-way If-join — both branches fall through to a common Ret (count_down)"
status: done
claimed_by: opus-b19
created: 2026-07-14T23:20:00Z
updated: 2026-07-14T01:30:00Z
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

- (2026-07-14, opus-b19) **DONE + VALIDATED END-TO-END.** The fork was
  RESOLVED by a hard technical constraint, then landed as Option 2. count_down
  now CLOSES by decide+rfl; all 13 fixture bridges behave as classified;
  tactus-core 44/0; verdict-neutral. Details in Writeup.

## Writeup

**Two-way If-join — DONE. count_down bridges by `decide`+`rfl`; Option 1 proven
infeasible, Option 2 landed (Danielle-approved).**

### The fork resolution (the key finding)

I implemented **Option 1** first (teach refWp's `wp_stm` Seq arm to clone the
continuation `*b` into both non-diverging branches). Hand-traced against the
real count_down cert it produces production's exact 4 goals in exact walk
order — the *logic* is right. But it does **not verify**: 20 `decide`-stuck
errors. Root cause (confirmed by reading the emitted `.lean`): to bind the
If's `t`/`e` as structural subterms I needed a nested `match a.deref` inside
the Seq arm, which puts the recursive calls at **match-depth 2**. The tactus
Lean backend then compiles `wp_stm` with `termination_by`/`decreasing_by`
(`WellFounded.fix`) instead of structural `brecOn` — and `WellFounded.fix`
does **not reduce under `decide`**, so *every* bridge that walks a `Seq` goes
stuck. I checked the escapes: a mutual-recursion helper needs a `stm_size`
measure; CPS (`wp_stm_k` with a continuation arg) transitions statement→
continuation at leaf arms so it also needs a total measure. **Both are
well-founded → both break `decide` identically.** There is no depth-1
structural formulation of the two-way join inside refWp — it is fundamentally
incompatible with the `decide` bridge. (Reverted refWp to frozen; consulted
Danielle, who approved Option 2 with this reasoning recorded.)

### Option 2 — the serializer desugar (what landed)

refWp stays **100% FROZEN**. The serializer (`sst_serialize::block`) bakes the
continuation clone into the SST **tree**: when a mid-block `if C { t } else
{ e }` is followed by a continuation `rest` and **BOTH branches fall through**,
it emits `If(C, ¬C, Seq(t, rest), Seq(e, rest))` instead of
`Seq(If(t,e), rest)`. refWp's existing **flat** If/Seq arms (depth-1
structural recursion) then reproduce production's goals — and still
kernel-compute. This mirrors production itself (`build_wp` clones `after` into
both branches); it is a NON-transcription TCB step (like the Call
instantiation), and the `decide` bridge validates the clone against
production's independently-computed goals (recompute-not-copy).

Pieces:
- `stm_diverges(&Stm) -> bool` — Rust mirror of refWp's `diverges`
  (Return/DeadEnd/break → true; Block → any; If → both branches).
- `as_if(&Stm)` — peels single-statement `Block` wrappers to find an If head
  (the frontend wraps a bare `if` in `Block([If])`).
- `block` desugar, **gated on both branches falling through**.

### The load-bearing restriction (why ONLY the true two-way join)

A first cut desugared *any* If with a continuation (cloning `rest` only into
non-diverging branches). That **broke find_square** (`CLOSE-BROKE`): its
`if … { return }` sits inside a loop, and moving `rest` INTO the If branch
hides it from `frame_after(If)` (which, for a two-way If, returns the BARE
pre-If frame), so the loop's maintain-reclose got the wrong post-body frame.
find_square's diverging-then case is ALREADY handled by bootstrap-17's
`frame_after` fall-through special case, so the fix is to desugar **only** the
true two-way join (both branches fall through) and leave diverging-branch
cases to the frozen `Seq(If, rest)` + bootstrap-17. The both-fall-through join
only arises at a fn-body **tail** in the corpus (count_down), where
`frame_after` is never queried. **Residual caveat:** a both-fall-through If
*inside a loop* would still need the loop-body post-frame to be the branch
join (unrepresentable by a single linear frame) — no fixture hits it;
documented in `block`'s doc-comment and DESIGN §2.4.1.

### Validation

- **count_down bridge CLOSES** by `decide` AND `rfl` (`goals_eq (ref_wp ctx
  sst) goals = 1`), against the FROZEN refWp emitted defs. Reclassified
  honest-fail→CLOSE in `probe9_bridge/run.sh`.
- **All 13 fixture bridges behave as classified** (`ALL BRIDGES BEHAVE AS
  CLASSIFIED ✓`): count_down + find_square close-ok, max_u64 stays honest-fail
  (unrelated branch-in-leaf), the rest close-ok.
- **tactus-core 44/0** — added `ref_wp_if_twoway_join` (in-crate `decide`
  guard: frozen refWp + the desugared count_down literal → 4 goals; +
  multiplicity + a mutation-kill). Frozen refWp otherwise untouched.
- **Verdict-neutral:** fixture verifies `13 verified, 11 errors` IDENTICALLY
  flag-off and flag-on — the desugar (cert-emit-only path) does not perturb
  verification. (The 11 errors are pre-existing `--lean-all-proofs`
  Lean-elaboration failures in non-cert-eligible fns, unrelated to this task.)

### Assumptions / caveats

- **Both-fall-through If inside a loop:** not covered (residual). Honest-fail
  if it ever arises (no current fixture).
- **`stm_diverges` is conservative** (Return/DeadEnd/break/Block/If only) — a
  branch diverging via another construct reads as fall-through → honest-fail,
  never silent-pass.
- **`as_if` peels only single-statement blocks** — a `Block` ending in an If
  after other statements is not treated as an If head (honest-fail).
- **The count_down cert leaf table renumbered** (the desugar serializes the
  cloned `rest` in then-branch position) — cert regenerated; bridge closes on
  text-equality, so the absolute ids don't matter.
