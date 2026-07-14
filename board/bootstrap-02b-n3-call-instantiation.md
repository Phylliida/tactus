---
title: "N3 follow-up — StmData::Call serialization (callee req/ens instantiation)"
status: in_progress
claimed_by: opus-b02b
created: 2026-07-13T21:20:00Z
updated: 2026-07-13T23:10:00Z
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

- (2026-07-13, opus) **Considered and deliberately DEFERRED this turn** — a
  sequencing call, recorded so it isn't re-litigated blind. The Call arm is
  the one place the serializer does non-transcription work: it must reproduce
  `build_wp_call` + `resolve_callee` + the simple-case subset of
  `build_call_substitutions` (~150 lines of walker internals) *inside the
  TCB*. Facts confirmed from source:
    - Callee specs are VIR-AST `Expr`s (`spec_callee.require` /
      `spec_callee.ensure.0` via `call_inlining::collect_inlined_at_call`),
      NOT SST `Exp`s — so they render through `to_lean_expr::vir_expr_to_ast`
      / `vir_expr_to_ast_for_inlining_with_ctx`, not the serializer's
      `sst_exp_to_ast_checked`.
    - The param→arg instantiation happens at RENDER time via a `RenderCtx`
      `value_subst` map (`build_call_substitutions`, `sst_to_lean.rs:2891`),
      with distinct req/ens/pre maps and a whole mut-ref post-state /
      prophecy sub-machinery. `quad_exec` (the fixture target) is the easy
      subset: two Static, same-crate, no-`&mut`, no-generic, no-zero-arg
      calls.
    - `krate` is already threaded to `emit_cert` (currently `_krate`), so the
      fn_map is reachable at the snapshot point.
  **Why defer:** the task itself says "the bridge (W2) is what pins the
  instantiation," and W2 doesn't exist yet. Writing an unvalidated ~150-line
  substitution mirror into the *trusted* serializer, with no bridge to check
  it against the walker, cuts against the architecture's core discipline
  (TCB stays small + auditable; everything else is kernel-checked). Correct
  order: land N3b (goal side) → W2a/b (the bridge) → then this Call arm, whose
  faithfulness the bridge's `decide` immediately validates. Do it as a
  RESTRICTED arm (Static + same-crate + no-&mut only; keep trait/`&mut`/
  cross-crate fail-loud with sharper census tags) so the TCB addition stays
  small.

- (2026-07-13, opus-n3c) **Deferral re-confirmed while closing N3c** (a second,
  independent read agrees). Settles the one dangling sub-question — *"do we need
  a restricted Call arm landed BEFORE W2a, so the bridge has a real call-bearing
  cert to audit on day one?"* → **No.** W2a bring-up only needs a hand-written,
  manually-verified fixture cert (a known-good Reference/WP pair) to exercise
  the bridge mechanism; you don't need a *generated* Call cert to test a bridge.
  Landing the Call arm pre-bridge would make the TCB the *source* of truth
  rather than the *subject* of the check — exactly backwards. So this stays
  todo behind W2 (see bootstrap-06/07); no change to the sequencing.

- (2026-07-14, opus-b14-cont) **N4 census (`bootstrap-05`) quantified this
  arm's payoff — it is the highest-leverage serializer arm by a wide margin,
  but the sequencing is UNCHANGED (still behind W2b).** Cold census over both
  corpora: `StmData::Call` blocks **5 fixture + 5 tgt = 10 exec fns** (fixture
  {quad_exec, count_down, vec_read, vec_push7, fill_zeros}; tgt
  runtime::{find_cancellation_exec, copy_word, apply_hom_gen, apply_hom_inv,
  apply_hom_symbol_exec}). It is the *entire* fixture gap and 5/8 of the tgt
  exec-fn gap; the only other blocker is `assert-query` (3 tgt fns). See
  DESIGN-W2-refwp.md §1.1. This does NOT reopen the deferral — landing an
  unvalidated substitution mirror in the TCB before the W2b bridge exists is
  still backwards. It just confirms: when W2b lands, THIS is the first
  serializer arm to build (and its faithfulness is exactly what the bridge
  will `decide`-check).

- (2026-07-13, opus-b02b) **PICKED UP (W2b gate now cleared) + found a
  genuine mirror-shape fork before writing any TCB code. Surfacing to
  Danielle.** The deferral was correct until W2b landed; it has (bootstrap-07
  done, bootstrap-18 done), so the sequencing gate is clear. On reading the
  production `walk_call` path against the ALREADY-AUTHORED refWp Call
  equations, the current mirror shape does NOT reproduce production's goals
  for the fixture target `quad_exec`. Details, all confirmed from source:

  **The mirror models the naive ∀-path; production takes the #128 ret-eq
  path for the fixture.**
    - `StmData::Call { reqs, enss, dest, dest_typ }` (tactus-core/lib.rs:133)
      with `frame_after(Call) = FBind(dest, dest_typ, hyps_of_leaves(enss))`
      (lib.rs:739) and `wp_stm(Call) = close_each(f, reqs)` (lib.rs:795). I.e.
      refWp models the post-call frame as `∀ (dest:dest_typ), ens0 → ens1 →
      …` — the naive "quantify the result, assume the ensures" shape from
      DESIGN-W2 §2.2. These Call equations have NO in-crate decide proof yet
      (all `ref_wp_*` proofs cover Assert/Seq/Ret/Loop/If — none exercise
      Call), so they were authored to spec, never validated against
      production.
    - Production's `push_post_call_frames` (sst_to_lean.rs:3250) has a
      `#128 ret-eq` optimization (`vir_find_ret_eq` :3695, `push_ret_frames`
      :3802): when a callee's ensures has a conjunct `r == E` with E not
      mentioning r, it DROPS the `∀ ret` entirely and emits
      `[E_bound →] [rest_ensures →] let dest := E`.
    - `double_exec` (the fixture callee) is `ensures r == 2*x` → hits ret-eq.
      For `let a = double_exec(x)` production's post-call frame is:
      `Imp(0 ≤ 2*x ∧ 2*x < 2^64) → Let(a, <bridged 2*x>) → <cont>`
      (E_bound from `type_bound_predicate(2*x, u64)` = unsigned range;
      rest_ensures empty → elided; dest_value = coerce_lexpr(2*x,u64,u64) =
      2*x). The precondition obligation goal is `close(f, [x < 1000 marked
      CallPrecondition])` — a single conjoined obligation
      (`emit_call_precondition_theorem` `and_all`s the requires).
    - So refWp gives `All(a, u64, Imp(ens))` where production gives
      `Imp(E_bound) Let(a, 2*x)`. **Structural mismatch → the decide bridge
      cannot close for quad_exec with the current mirror.**

  **Key facts that shape the fix:**
    - The requires-obligation goal (`close(frame, req_conj)`, one conjoined
      obligation) is IDENTICAL in both the ∀-path and ret-eq path. Only the
      post-call FRAME differs.
    - BOTH production frame shapes are expressible with existing frame
      primitives: ∀-path = `FBind(dest, ret_typ, [FHyp(ret_bound)] FHyp(ens))`;
      ret-eq path = `[FHyp(E_bound)] [FHyp(rest)] FLet(dest, E)`.
    - The raw SST `StmX::Call` does NOT contain the post-call frame — it is
      COMPUTED downstream in `push_post_call_frames`. So ANY option that
      certifies quad_exec must either replicate that computation in the
      serializer (the ~150-line TCB step the card warned about) or capture it
      from production's walk via provenance.

  **Options (full analysis; recommending #1 = "lower the mirror"):**
    1. **`Call { reqs: LeafList, post: FrameList }` — transcribe the post-call
       frame.** refWp becomes `wp_stm(Call)=close_each(f,reqs)`,
       `frame_after(Call)=frame_append(f, post)` (a pass-through appender).
       The serializer INDEPENDENTLY replicates `push_post_call_frames`
       (ret-eq detect + bound synth + coerce) for the simple subset to build
       `post`. Handles ∀-path + ret-eq uniformly and generalizes to future
       `&mut` post-states/prophecies. The `decide` bridge validates the
       serializer's replication against production (non-circular — serializer
       does NOT copy production's frame, it recomputes it). Cost: mirror
       reshape (rewrite the frozen N2.1 Call fields + refWp Call equations +
       the stm_size/decide sanity arms; invalidates the tactus-core fn cache
       once) + ~150 lines of replicated instantiation in the TCB.
    2. **Capture the post-call frame delta via provenance** (like N3b goal
       shapes) instead of replicating. Least TCB, but refWp's Call handling is
       then a pass-through over a COPIED frame → the call's frame contribution
       is tautologically matched (weaker independent check for calls).
    3. **Restrict to the ∀-path; fail-loud on ret-eq.** Tiny, no mirror
       change, but quad_exec still fails and most exec fns have `r == E`
       ensures → certifies ≈nothing. Not worth it.
    4. **Desugar Call into primitive StmData nodes** (DeadEnd/Assert for the
       precondition-only obligation, Assume/Assign for the frame). No mirror
       change, refWp untouched — but "clever" desugaring in the TCB (against
       the module's boring-beats-clever discipline) and still replicates the
       path choice.

  **Recommendation: Option 1.** It matches the architecture's north star
  (serializer = faithful transcription of what production does; refWp = dumb
  structural checker; bridge = the meaningful test). The local model
  (127.0.0.1:8051) independently reached the same conclusion, framing it as
  "lowering the mirror": move the frame from *derived intent* to *explicit
  evidence*, so the bridge actually validates the #128 optimization and the
  fix is permanent across the coming `&mut`/prophecy frame shapes rather than
  perpetually chasing production's frame-synth logic in refWp.

  **Blocked on a Danielle call** (the card invited exactly this fork): does
  she want the mirror reshaped to `post: FrameList` (Option 1), or the
  lighter provenance-capture (Option 2), or keep the contract-view
  `enss/dest/dest_typ` and add a ret-eq VARIANT (a middle path — less general
  than FrameList, but preserves the readable Call node)? Asking now.

  **Concrete next steps once decided (Option 1 path):**
    - tactus-core: change `Call` to `{ reqs: Box<LeafList>, post: Box<FrameList> }`;
      rewrite `frame_after`/`wp_stm`/`stm_size`/`frame_len`(n/a) arms; add a
      `ref_wp_call_*` decide proof for a hand-built double_exec-shaped literal
      (both a ret-eq and a ∀-path case).
    - serializer `sst_serialize.rs`: replace the `Err("call")` arm with a
      restricted builder mirroring `resolve_callee` + the simple subset of
      `build_call_substitutions` + `push_post_call_frames` (Static +
      same-crate + no-`&mut` + no-generic only; keep trait/`&mut`/cross-crate
      fail-loud with sharper tags `call-mut`/`call-trait`/`call-crosscrate`).
      Move the Call bullet from "Deliberately NOT read" to "Read" in the
      module faithfulness doc, spelling out the instantiation as the one
      non-transcription trusted step.
    - Validate via the W2b bridge: quad_exec cert must decide-close; a
      negative-control mutation (swap the E in `let a := E`) must flip.

- (2026-07-13, opus-b02b) **DECISION IN (Danielle: Option 1) → tactus-core
  half LANDED & verified.** Implemented the whole tactus-core side of the
  "Concrete next steps" above (committed; `lean-backend --lean-all-proofs`:
  **43 verified, 0 errors**, `out/lib/` regenerated):
    - `StmData::Call { reqs: Box<LeafList>, post: Box<FrameList> }` (was
      `{ reqs, enss, dest, dest_typ }`). Datatype change → tactus-core fn
      cache invalidated once and the module re-verified, as warned.
    - refWp is now a **pass-through**: `wp_stm(f, Call) = close_each(f, *reqs)`;
      `frame_after(f, Call) = frame_append(f, *post)` (append the transcribed
      post-call frame verbatim); `stm_size = 1 + leaf_len(reqs) +
      frame_len(post)`. `amended_shapes_kernel_compute` Call-size sanity
      updated.
    - **`ref_wp_call_pass_through` decide proof (the double_exec-shaped
      validation §2.6 asked for):** models `let a = double_exec(x); assert Q`
      under a one-hyp ambient frame `[100]`, proving refWp reproduces
      production's goals for BOTH post shapes:
        · ret-eq (#128): `post = FHyp(E_bound) FLet(a, 2*x)` ⇒
          `[100→(x<2^63)]`, `[100→(0≤2x∧2x<2^64)→ let a:=2x; Q]` (no ∀).
        · ∀-path: `post = FBind(a,u64) FHyp(ret_bound) FHyp(ens)` ⇒
          `[100→(x<2^63)]`, `[100→∀a,(0≤a∧a<2^64)→(a>x)→ Q]`.
      Plus a mutation-kill (swap `let a := E` value 10→99 ⇒ `goals_eq = 0`).
    - DESIGN-W2-refwp.md §2.6 marked DECIDED + §0 table Call row superseded.

  **Proves** the reshape is sound and refWp's pass-through reproduces
  production goals for both `push_post_call_frames` paths on hand-built
  literals. **Does NOT yet** serialize `quad_exec` — the card's "done when"
  needs the serializer `post`-builder (the second + third bullets of
  "Concrete next steps" above, unchanged and now UNBLOCKED). Card stays
  `in_progress`; next pickup = that serializer builder, whose faithfulness the
  W2b bridge will `decide`-validate against production (non-circular: the
  serializer recomputes `post`, refWp does not copy it).

## Writeup
