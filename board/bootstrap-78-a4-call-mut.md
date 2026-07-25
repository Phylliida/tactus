# bootstrap-78 — A4: call-mut arm (prophecy/rebind in the frame mirror)

Status: **card — design frozen from step-0 evidence, implementation not
started.** Endgame §3 A4; the first of the two real machinery arcs left.
Subjects: `vec_push7` + `fill_zeros` (fixture) + `runtime.copy_word` (tgt).
Acceptance: all three bridge-close; `call-mut` census tag → 0 (or splits
into narrower loud tags with population 0 on the corpus); mutation kills
on the new frame channels.

## Step-0 evidence (frozen 2026-07-24, live emission + spine sidecars)

Sources: `bootstrap-fixture/out/lib/pkg/lib__vec_push7.{lean,spine.json}`,
`lib__fill_zeros.{lean,spine.json}` (current b77-era binary), production
walk code (`sst_to_lean.rs`: `push_post_call_frames` diagram ~4180,
`build_call_substitutions`/`add_param_subst_entries` ~3789,
`push_mut_arg_binders` ~4388, `push_mut_rebinds` ~5332,
`MutArgInfo`/`MutTargetRaw` ~3660, `mint_return_prophecy`,
`rewrite_mut_ref_in_stm` ~1135, `next_id` ~2393).

### E1 — vec_push7 (fn-level `&mut` param), both VC spines, exactly:

```
all  v        : Tactus.MutRef (lib.vec.Vec Int lib.alloc.Global)   -- param binder, MutRef WRAPPER typ
all  h_req0   : (let v := v.deref; <req>)                          -- requires binder, deref-shadow prefix INSIDE the leaf
let  v_at_pre_tactus := v.deref                                    -- fn-entry old() snapshot
let  v := v.deref                                                  -- fn-entry deref shadow
all  _tactus_mut_post_1 : lib.vec.Vec Int lib.alloc.Global         -- Phase 1: mut-arg havoc binder, INNER typ
all  _tactus_ret_2      : Unit                                     -- Phase 2: ∀-ret (unit callee, no #128 ret-eq)
imp  view (Ref.mk _tactus_mut_post_1) = push (view (Ref.mk v)) 7   -- Phase 3: instantiated ens (post ↦ mut_post, pre ↦ v)
let  v := _tactus_mut_post_1                                       -- Phase 4: rebind
leaf <postcondition>                                               -- (no Phase 5: no dest)
```

Two theorems (2 ensures), identical telescope. Postconditions reference
`v` (rebound) and `v_at_pre_tactus` (old) — leaf-opaque at stage A.

### E2 — fill_zeros (`let mut` LOCAL, push inside loop)

Call-site frame **identical in shape** (`_tactus_mut_post_5`/`_ret_6`,
ens-imp, `let v := _tactus_mut_post_5`), sitting inside the loop
maintain/exit telescopes. NO fn-entry preamble, NO MutRef binder — the
local enters as `let v := tmp__1` (Vec::new dest). Conclusion: **the
call-site machinery is one shape for params and locals**; only the
fn-ENTRY preamble is mut-param-specific.

### E3 — copy_word (tgt) = the composition subject

Loop + AssertQueryTactus asserts (A3, landed) + `out.push(v[j])` where
the value arg is an earlier call-dest (`vec_index` → tmp): exercises the
A2 let-binder ledger THROUGH a rebind. No new shape beyond E1/E2.

### E4 — production phase order (`push_post_call_frames`)

Phase 1 per-mut-arg: `∀ post_i : typ_subst(param.typ)` + type-bound hyp
(recurses through MutRef to the inner typ; None for Vec/structs — no
bound hyp in any subject). Then returned-mut-ref prophecy ∀-bind (ONLY
when the callee RETURNS `&mut` — `mint_return_prophecy`; **no subject
hits this**). Phase 2 `∀ ret` + bound, or #128 ret-eq replacement. Phase
3 ens hyp via `ens_value_subst` (mut param p ↦ `Var(fresh)`, `p_at_pre`
↦ pre-call arg). Phase 4 rebinds: `Var(x)` target → `let x :=
coerce(fresh)` (wrapper→inner `.deref` when new-mut-ref; no-op for our
Vec case since binder is already inner-typed — verify at impl); `Field`
target → Lean struct-update let. Phase 5 dest let (skipped: unit callee
= no dest; or `use_dest_name`).

### E5 — the counter discipline (THE new faithfulness surface)

`ObligationEmitter::next_id()` is a single chokepoint; consumption
sites: **every emitted theorem** (Assert/AssertQuery/loop-oblig/
postcondition emission sites ~2850/2907/3203/3294/3388/4150) + **every
call's `fresh_ret` gensym** (~4034, consumed at
`build_call_substitutions` time even when the name is unused —
use_dest_name/#128 still burn the id) + **every mut arg's
`_tactus_mut_post_` gensym** (~4025/4348). Evidence that the
serializer's per-call shell counter (always 0) is insufficient:
fill_zeros' names are `_5`/`_6` (ids 1–4 consumed by Vec::new's
fresh_ret + three loop-entry theorems before the call site).
`vec_push7`'s `_1`/`_2` only match by accident of being the first
consumer. ⇒ the serializer must thread a WALK-ORDER COUNTER MIRROR,
incrementing at the same sites production does. Precedent: the
`_h_hoist_i` hyp-naming mirror (b74 slice 2). This becomes a named row
in the faithfulness contract (audit table): the consumption-site list
above IS the contract; drift = leaf-name divergence = bridge flip (the
channel is self-pinning, but the mutation kill makes it explicit).

## Design (frozen)

### D1 — NO call-site vocabulary change

`StmData::Call { reqs, post: Box<FrameList> }` stays. The b02b comment
anticipated exactly this ("generalizes to the coming `&mut` post-state /
prophecy frames"). The serializer assembles the mut frames INTO `post`:

```
post = [FBind mut_post_i typ_i]           (per mut arg, walk order)
       [FHyp bound_i]?                    (type-bound on inner typ, when Some)
       [FBind ret typ | (#128: FHyp E_bound?)]   (existing b70 assembly)
       [FHyp ens]                         (existing)
       [FLet local_i := mut_post_i]       (per mut arg — REBIND, new)
       [FLet dest := …]?                  (existing; absent for unit)
```

refWp consumes `post` generically (frame concat) — **zero tactus-core
edits at the call site, zero W5 model delta there** (`u_esf_call` /
`u_wp_call` already treat `post` as opaque frames; the in-model
tripwire column (D) gains rows asserting the mut-frame CLASSES are
frame-generic, not new arms).

### D2 — FnCtxData preamble: dedicated `MutParamList`, NOT a raw FrameList

New field on `FnCtxData`: `mut_params: MutParamList`, cons-list of
`(param name leaf, at_pre name leaf, inner typ leaf)`. refWp DERIVES
the two entry lets structurally — `FLet at_pre := <p>.deref; FLet p :=
<p>.deref` — rather than trusting serializer-written frames (maximum
reference-side derivation; a raw FrameList would let a buggy serializer
write anything and self-agree). Param binder stays in `params` with its
MutRef WRAPPER typ leaf (E1). `build_req_binders` reuse (A2) already
receives `mut_param_names` — the serializer must pass the real set so
req leaves render the deref-shadow prefix (E1's h_req0).

⚠ churn discipline (b77 lessons, one cache-churning edit): FnCtxData
arity changes → update vendored probe pins (probe14/probe37 use
`FnCtxData.mk` positionally) + watch the wf-sig classifier
(type_bound_predicate fires on new STRUCT fields — Dt-classification
precedence fix from b77 applies; MutParamList is a Dt, so it classifies
like ParamBoundList — verify, don't assume). No Lean-keyword field
names (`then` lesson): `mut_params` is safe.

### D3 — serializer: lift the `call-mut` rejection to the Var-target subset

In `cert_call_leaves` + the Call arm of `sst_serialize.rs`:
- Mirror `build_call_mut_args`: per mut param, resolve the raw arg to a
  `Var`/`VarLoc` target; **Field targets → loud tag `call-mut-field`**
  (struct-update rebind = out of scope, no corpus population).
- **Returned-`&mut` callees → loud tag `call-mut-ret`** (prophecy
  composition machinery; no corpus population; the W5d model story
  exists but the stage-A mirror can wait for a real subject).
- Counter mirror (E5): a `WalkSt.emit_counter` incremented at the
  contract's consumption sites; `fresh_ret`/`mut_post` names minted
  from it (replaces the shell-emitter-counter-0 accident).
- Frame assembly per D1, reusing production's leaf renders
  (`build_call_substitutions` with the mirrored counter, ens/req
  leaves exactly as today).
- LEDGER: after the rebind, re-enter `local → (inner typ, trusted)` in
  `let_binder_typs` — the A2 lesson applies THROUGH rebinds (copy_word
  pushes the same rebound local next iteration; its next arg render
  must see the ledgered typ, not re-wrap `Ref.mk`).
- Raw-SST caveat: the serializer transcribes the RAW body (pre
  `rewrite_mut_ref_in_stm`); the mut-arg exprs arrive in raw
  `MutRefCurrent`/`Loc` shapes — mirror the rewrite's Var extraction,
  fail-loud on anything else (tag `call-mut-arg-shape`).

### D4 — census split (P2: every honest-fail class = fixed arm OR loud tag)

Retire `call-mut` on close; add `call-mut-field`, `call-mut-ret`,
`call-mut-arg-shape` (all expected population 0 on tgt + fixture; if a
future crate hits one, it fails loud with a sharp name). Census table
row in the gate report updates automatically (tags are data-driven).

### D5 — mutation kills (probe13, same session as the close)

- `mut_rebind_drop` (SST-side... **no — these frames live in the CERT's
  Call post FrameList**): drop the rebind `FLet` from a vec_push7 cert →
  ref continuation sees stale `v` → flip.
- `mut_post_binder_drop`: drop the `FBind mut_post` → flip.
- `mut_ens_hyp_drop`: drop the ens `FHyp` → flip (distinct channel from
  b70's frame kills: those covered the ∀-ret path, not mut frames).
- Counter kill: rename `_tactus_mut_post_1` leaf → `_tactus_mut_post_9`
  in ONE of the paired sites (binder vs rebind) → flip. Pins E5 as a
  live channel (both-sites rename would self-agree on the cert side but
  diverge from production `goals` — still flips; single-site is the
  sharper kill; do single-site).

## Slices (each ends green: suite + gates + probes)

1. **S1 counter mirror + census sub-tags — DONE 2026-07-25.**
   `Serializer.emit_ordinal` (consumption table in the field doc +
   serializer header contract row) threaded into `cert_call_leaves`
   (`&mut`, shell emitter starts at the walk value; advance = Phase-C
   gensyms + precondition-theorem id iff `precondition.is_some()`,
   matching production's ~3634 guard). `call-mut-ret` split out (checked
   FIRST — a `&mut` return borrows from a `&mut` param). Validation
   AMENDED from the original card text: existing certs contain NO
   gensym names at all (all certified calls are ret-eq/dest-name paths)
   so S1 is provably byte-neutral — confirmed by cold regen + full-dir
   diff (32 certs identical); the `_1/_2`-`_5/_6` spine byte-match
   moves to S3 acceptance where mut certs first emit. NL arm recurses
   through `stm()` (inner Assert carries the +1); AQT destructures
   inline (own +1); ProofBlock emits nothing (+0). Battery: units
   406+7/0 (golden pin included), probes 9/13/14/37/38 green,
   fixture 24v/9e (the known closer-failure set + a mul_bound
   Mathlib-LEAN_PATH environment artifact under direct invocation).
   S3 note: mut_post mint site inside `build_call_substitutions` is
   ~4025 (Var/Field targets); ~4348 is the returned-mut-ref path
   (tagged out). Prophecy-REUSE consumes 0 ids (skip site) — also
   tagged out with `call-mut-ret`.

   **S1 REVIEW ROUND (2026-07-25, Danielle-prompted "anything you're
   not confident in?"):** two fixes + one big find.
   (F1) header row mislabeled the counter "TRUSTED" — reworded: it is
   CHECKED (gensym drift = loud bridge red; and now the F2 check).
   (F2, the more-right-way find) **emission-time cross-check landed**:
   `predicted_theorem_ids` records every replayed theorem-id
   consumption; after the goal walk they compare element-wise against
   the ids production's theorem names carry (ALL `theorems`, not the
   spine-filtered `goal_names`); mismatch = sharp `emit-counter-drift`
   census reject. Validates the whole table (loop rows, wrap-mode
   walk-order timing) on EVERY cert — not only where gensym names print.
   **THE CHECK IMMEDIATELY FOUND 3 REAL TABLE BUGS** (invisible to the
   byte-diff — none of these fns print gensyms; all three would have
   silently shifted gensym ids in S3+ shapes): the three certs now
   census-reject with `emit-counter-drift` (honest P2 fail-louds, NOT
   regressions — a cert embedding a wrong counter should reject).
   **S1b QUEUE (diagnose fresh, BEFORE the S2 churn):**
   * `count_down` [1,2,3,5]≠[1,2,3]: production emits a
     `_tactus_termination_` theorem at the RECURSIVE call site (id 3,
     before the call's gensym 4) — a consumption row the table lacks
     (decreases-check theorem; find the emit site in walk_call, add
     the row + prediction for self/decreases-carrying callees).
   * `clamped_inc` [1..5]≠[1,2,3]: production emits per-branch × per-
     ensures postcondition theorems (4) for the value-if return; the
     mirror's Ret route predicted ONE Ret of 2 — route mismatch to
     diagnose (which route does the mirror take here, and was this fn
     ever a close subject or an unclassified cert-emitter?).
   * `mul_bound` [1..7]≠[1..6]: one theorem more than predicted around
     the NL query — the AssertQueryNl consumption row is incomplete
     (does the query emit its own theorem BESIDES the body walk's?).
   Post-review state: 29/32 certs emit byte-identical to pre-S1; the 3
   rejects are the drift finds; probes 9/13/14/38 all green; units
   406+7/0. Battery evidence that S1's replay is correct for every
   currently-CLOSING shape (sum_to's loop rows pass) — the 3 finds are
   in never-validated corners, which is exactly what F2 was for.

   **S1b DONE 2026-07-25 — diagnosis CORRECTED both card hypotheses**
   (the queue's guesses above were wrong in instructive ways):
   * `count_down` + `clamped_inc` = ONE bug, and it is NOT a missing
     termination row or a route mismatch: the `block()` two-way-join
     desugar (`Seq(If,rest)` → `If(t;rest, e;rest)`, bootstrap-19)
     serializes the continuation ONCE and reuses the term verbatim in
     the else branch — but production's Wp tree CLONES `after` into
     both branch Wps (`walk_obligations` `Wp::Branch` arm comment
     ~3064) and consumes its theorem ids TWICE. The termination assert
     was already counted correctly (it is an ordinary raw-body
     `StmX::Assert` from the recursion pass — count_down prediction 3)
     and the call's fresh_ret gensym was already consumed (ordinal 4);
     the missing id was the ELSE-branch copy of the continuation
     (count_down id 5 = else-path postcondition; clamped_inc ids 4-5 =
     else-path × 2 ensures). FIX: record the continuation's
     (ordinal, prediction) deltas during its single serialization,
     replay `consume_theorem_ids` after the else-branch walk; a
     gensym-consuming continuation (a Call after the join) rejects
     loud `call-in-branch-join` — its minted names could not match
     both production copies (corpus population 0).
   * `mul_bound` = as hypothesized: the NL query's body Wp is built
     with a `Wp::Done(LitBool(true))` terminator (~6903) and the Done
     arm emits it as the `_tactus_ensures_` theorem — the NL arm now
     consumes +1 after the body walk.
   Header contract table updated with all three rows. Validation:
   fixture emission certified 32/37 (the 3 drift rejects cleared,
   remaining = call-mut ×2 + rawvir classes), all 29 pre-existing
   certs byte-identical, probe9 all-green incl. the 3 restored certs
   (vec_read lone hfail-ok), probes 13/14/37/38 green, units green.
2. **S2 FnCtxData churn — DONE 2026-07-25.** Landed as designed with
   ONE at-impl deviation to D2's entry triple: slot 3 is the **deref
   VALUE leaf** (interned `<p>.deref` text), NOT the inner typ leaf —
   `GoalData::Let`/`FLet` carry value LEAF ids, so the derived frames
   need the interned text (the FLetH typ/eq-leaf precedent: serializer
   renderings of production's exact pp); the inner typ has NO S2
   consumer (call-site typs ride `Call.post` per D1 — add a slot later
   if S3/W5 shows a consumer). Key mechanism finding (evidence:
   vec_push7 emitted theorem + production `hoist_all` ~2094):
   production's preamble lets are TYP-LESS `CtxFrame::Let`s
   (`add_pre_capture`/`add_body_shadow` ~1517) → `hoist_all` bails →
   **every goal of a mut-param fn is WRAP-MODE**, with params/reqs
   staying theorem binders as the emitter's BASE binders — which the
   mirror gets for free: `mut_preamble_frame` derives two PLAIN FLets
   per entry (at_pre first), plainness trips `has_plain_flet`, and
   FBind→All keeps the base binders. Serializer: entries from mut-ref
   pars + `BorrowMut` local_decls in declaration order (production's
   initial-OblCtx loop ~1526) + `mark_flet_forced()` when non-empty
   (freshening only runs inside hoist_all; mut-fn goals never hoist).
   Landed: MutParamList Dt + `FnCtxData.mut_params` (position 5, .mk
   arity 6→7) + `mut_preamble_frame` + seed_frame wiring + wrap-mode
   non-vacuity pin (`ref_wp_mut_preamble_wrap`, decide) + serializer
   population/`mut_param_list` builder + module-doc contract rows.
   Churn fallout handled: 17 vendored pin files arity-bumped
   (probe11 certs+Pinpoint, probe20 certs, probe14, probe10);
   probe37's `hwf_c.2^5` → `.2^6` (FnCtxDataWf gained the
   MutParamListWf conjunct); golden add_capped re-vendored from fresh
   emission; probe20 de-staled with the probe9-style all-preludes glob
   (its pinned prelude dir was the documented milestone-C stale-red
   class — pre-existing, surfaced by running it). Battery: tactus-core
   gate **256/0** + package gate kernel-verified + **Link discharge
   172/0** (wf synthesis absorbed MutParamList automatically), fixture
   emission certified 32/37 (same reject set; all 21 snapshot-compared
   certs ctx-line-only diffs), probe9 all-green (24 certs), probe11
   all-green, probes 13/14/37/38 green, probe20 all-green, units
   406+7/0. NOTE for S3: no new certifying fn this slice (every
   mut-param fixture fn still rejects on its CALL — `call-mut`); the
   preamble derivation gets its first live subject when S3's `fn
   inc(x: &mut u64)` lands with the call arm.
3. **S3 call frame assembly** — D3 rest; vec_push7 + fill_zeros certs
   elaborate + decide-close (extend probe9 subjects).
4. **S4 kills** (D5) + tag retirement + battery.
5. **S5 tgt copy_word** — scoped `--verify-module runtime
   --tactus-emit-cert` cert regen + close (probe38-style runner; NOT
   the full tgt gate — dropped per Danielle, and don't stack heavy
   verus runs). `call-mut` tag → 0 on the tgt census.

## Open items (resolve at impl, not design blockers)

- Phase-4 coercion exactness: whether the Vec-case rebind is bare
  `fresh` or `fresh.deref` (E1 shows bare — wrapper depths already
  match; confirm on a u64 mut-arg fixture fn, add one: `fn inc(x: &mut
  u64)` exercises bound-hyp + coerced rebind in one subject — **add to
  fixture in S3** as the minimal-mut subject).
- Whether `_tactus_ret_N : Unit` binder appears for ALL unit callees or
  only dest-less ones (E1 shows dest-less; a `let _ = f(&mut v)` shape
  would pin the other; not in corpus — leave to the arg-shape tag if
  weird).
- ~~MutParamList wf-classification interaction (D2 ⚠)~~ **RESOLVED
  2026-07-25 (read-only check, S2 opener):** the b77 Dt-precedence fix
  (generate.rs:4779 — Dt-classification wins for datatype-typed params;
  wf hyp subsumes projected bounds) covers the new field: FnCtxData
  stays Dt-classified, MutParamList (u64-carrying cons-list, the
  ParamBoundList shape) gets its own synthesized DtWf like every
  scalar-carrying Dt. S2's churn checklist is therefore just the
  standard set: FnCtxData.mk arity 6→7 in the vendored probe pins
  (probe14/probe37), refWp preamble derivation, W5/FnCtx consumption,
  serializer FnCtx path passes real `mut_param_names` into the
  `build_req_binders` reuse.
