# bootstrap-80 — A7: stage-B callee-signature vocabulary

Status: **DESIGN FROZEN 2026-07-31 — all 6 open questions resolved
(§ "Design freeze" below), under Danielle's standing delegation with
her principles (1 right-way/cleaner, 2 trusted-surface shrink, 3
Lean-idiomatic, 4 transparency, 5 predictability, 6 invest for
clean). Implementation not started.**
Closes the LAST coverage-arm class of milestone A. All six A7-class
honest-fails are the SAME class (vec_read deep-leaf): frame assembly
byte-perfect everywhere; divergence is leaf RENDERING only.
Sequencing per Danielle 2026-07-28: after b79 (DONE), before B
(b67 caching + b68 flip).

Subjects (6): fixture `vec_read`, `vec_push7`, `fill_zeros`,
`count_to_len` (probe9); tgt `runtime.copy_word`,
`runtime.find_cancellation_exec` (probe11).

Scope per the endgame map (DESIGN-bootstrap-endgame.md §3 A7 +
§9 Q3), three parts:
1. **Callee signatures in the mirror vocabulary** — the vec_read
   class: per-arg spec-call rendering decisions (View-deref,
   `Int.ofNat`) need the callee's param types, which the
   fixed-vocabulary mirror does not carry.
2. **Q3 / P1-item-3: derive the poison mark reference-side** —
   recompute "mentions residue" over deep prop content in
   tactus-core; the serializer's `hyp_poison` copy retires. A
   trusted bit should not outlive the first milestone able to check
   it.
3. **Sequenced candidate (b78 card §4, mirrored production quirk):**
   Phase-1 bound predicate runs on the UNSUBSTITUTED param typ — a
   generic `&mut T` callee instantiated at u64 gets no bound hyp on
   the existential (sound, incomplete). RESOLVED at freeze: fix
   production + mirror (see F5).

Constraint (Danielle 2026-07-31): NO full tgt gate runs — too
slow/compute-heavy, not fundamentally needed for bootstrap
correctness. The before/after census table uses probe11's scoped
per-module emits (the b78-S5 recipe: `runtime` +
`todd_coxeter_rt`, `--emit-lean --tactus-emit-cert`, no `-V
cache`), NOT the package gate.

## Step-0 evidence (frozen 2026-07-31)

Source: `bootstrap-fixture/out/lib/cert/vec_read.cert.lean`
(serializer RawExp transcription) vs
`bootstrap-fixture/out/lib/pkg/lib__vec_read.lean` (production
emission). Both post-b79, current on disk.

### E1 — the View-deref divergence, precisely

The return leaf's RawExp (cert line 47):

```
RawExp.CallN 11 TyInt                      -- lib.seq.Seq.index, ret Int
  args: [ RawExp.Call 12 (TyNamed 13)      -- lib.view.View.view, ret Seq Int
            (RawExp.Var 0 (TyRef 14))      -- v : &Vec
            (TyRef 14)                     -- carried argty
        , RawExp.Var 2 TyNat ]             -- i : Nat
```

Production's postcondition leaf (pkg line 38):

```
r = lib.seq.Seq.index Int
      ((lib.view.View.view ((v : Tactus.Ref …)) : lib.seq.Seq Int))
      (Int.ofNat i)
```

Two independent divergences, both per-arg decisions:

- **Deref:** `render_exp`'s single-arg Call arm derives
  `view(v.deref)` — the G2 rule (`needs_ref_deref(type_of(arg))`)
  fires on ANY `TyRef` arg. But `View.view`'s param IS the ref type,
  so production writes bare `v` (the View instance on
  `Tactus.Ref (Vec Int Global)` handles the wrapper). The deref
  decision is (callee param typ, actual arg typ): deref iff arg is
  `TyRef(inner)` AND param is the pointee `inner`. Here param =
  `TyRef` ⟹ no deref.
- **ofNat:** the CallN arm renders args STRAIGHT (lib.rs:1262-1265,
  "per-arg expected-type coercion is deferred to W7c"). `Seq.index`'s
  index param is `Int`; the arg `i` is `Nat`; production materializes
  `Int.ofNat i`. CallN carries NO per-arg param types today — this
  is the vocabulary gap proper.

### E2 — leaf 8 vs leaf 9: the ofNat asymmetry (RESOLVED, F2)

The cert intern table has BOTH `r = Seq.index … (view v) i` (leaf 8,
NO ofNat) and the span-marked `… (Int.ofNat i)` (leaf 9, WITH
ofNat). Resolution: leaf 8 serves the FnCtxData ensures-oblig slot
(the serializer's `oblig_leaf` path via `render_ctx` = production's
WpCtx postcondition ctx); leaf 9 serves the theorem-goal leaf. BOTH
texts are production's own — production has two rendering paths for
the same ensures and they disagree on the per-arg coercion (the
oblig-leaf path predates the `fn_param_typs` coercion).
The bridge compares refWp's Ret-RawExp render against the GOAL leaf
(leaf 9's shape — `GoalData.LeafE (SpanMark 15 (BinOp … AppN …
Cast NatToInt …))` in the cert), so A7 reproduces the ofNat shape
and never touches the no-ofNat oblig slot (stage-A accounting,
opaque id). The oblig/goal path disagreement is a PRODUCTION-
INTERNAL inconsistency — flagged for Danielle (unification is its
own brick, not A7 scope; principle 1 would unify, but it is not on
the bridge's comparison path).

### E3 — the mechanism precedent already exists

`RawExp::Call` (single-arg) already carries `argty` and derives
nat-coercion + ref-deref per-arg (lib.rs:1221-1226); `CallN` is the
un-done sibling. Production's own decision procedure
(`to_lean_sst_expr.rs:941-963`): `ctx.fn_param_typs(fun, typs)` →
per-arg `into_slot(expected)` (with `a.typ` fallback when the
signature is unknown) + `coerce_lexpr` (line 1352-1357: the same
expected-typ bridge inserts `.mk` wraps / derefs). The mirror
follows the same shape: transcribe the per-arg expected types from
the same VIR source, DERIVE the coercions reference-side.

### E4 — subjects' divergence census (from b78 §3/S5 + b79 cards)

- `vec_read`: E1 exactly (precondition + postcondition leaves).
- `vec_push7`: A7 alone closes (b78 §4).
- `fill_zeros`: A7 closes the residue (S3-pre landed 07-26; hfail
  narrowed to A7-only).
- `count_to_len` (b79): goals 2/3/4 close outright; entry /
  exit-reclose / postcondition diverge ONLY on view()-bearing
  invariant/ensures leaves; leaf-normalized spine bridge closes over
  all six goals — frame assembly byte-perfect.
- `copy_word` / `find_cancellation_exec` (b79): spine bridges close;
  non-view goals close outright incl. push mut frames + renamed Ret.

### E5 — poison-mark site (for scope item 2) — AMENDED at freeze

`sst_serialize.rs:1028` `hyp_poison`: text check via
`lexpr_mentions_var(e, residue_name)` — a TRUSTED semantic predicate
(P1: the contract header says so; probe13 `poison_flip` pins the
channel). Domain = `residue_names` (sst_serialize.rs:594, pushed at
1274/1320 — hoisted let names + call dest names).
**Freeze correction to the carded assumption:** the poison check's
domain is NOT deep today. Goal LEAVES are deep `ExprData` (W6d),
but hyp/let-eq PROPS are opaque leaf ids EVERYWHERE — in the cert
frames (`FHyp name prop_id poison`), in hoist-mode goal binders
(`GoalData.All name prop_id`), and in wrap-mode goal bodies
(`GoalData.Imp prop_id …` — add_capped cert evidence). The bridge
never looks inside a hyp prop, and byte-neutrality (F6) requires
that to stay true. So the derivation needs the prop CONTENT
available reference-side WITHOUT changing goal assembly — see F4's
side-table design. And the residue-name set does NOT reach the cert
(FnCtxData fields: typ_params/params/param_bounds/reqs/mut_params/
enss/closer_default — no residue slot); it must be added.

## Design freeze (2026-07-31 — RESOLUTIONS)

**F1 (Q1 — what is Call's `argty` today):** RESOLVED by evidence.
`sst_serialize.rs:1500`: `arg_ty = self.typ_data(&arg.typ)` — the
ARGUMENT node's own typ (actual), not the callee param typ. The
coerce machinery on it is inert (W7 comment: "structural no-op per
element" — Verus materializes most coercions as `Clip` nodes inside
args); the G2 deref fires purely off the actual type, which is
exactly the vec_read bug (E1). Re-source to the callee param typ.

**F2 (Q2 — leaf 8 vs leaf 9):** RESOLVED by evidence (E2 above).
A7 reproduces the goal-path shape (ofNat); the oblig-leaf path's
no-ofNat text is a production-internal inconsistency, flagged, out
of scope.

**F3 (Q3 — where callee param types live):** RESOLVED: **per-site,
carried on the call node** — NOT a signature table on FnCtxData.
- `RawList` (used ONLY by `RawExp::CallN`) gains the expected param
  typ per element: `Cons(Box<RawExp>, TypData, Box<RawList>)`.
  Element-pairs, not a parallel list — no zip, no length-mismatch
  failure mode (principle 3).
- `RawExp::Call`'s `argty` re-sources to the expected param typ
  (same arity).
- render_exp needs NO lookup and NO fallback logic: the serializer
  transcribes production's exact fallback (`a.typ` when the
  signature is unknown — `into_slot(&a.typ)`, E3), so every node is
  self-describing (principles 4/5). A table would add an id-keyed
  lookup + failure mode to the reference and an FnCtxData arity
  bump for zero decision-content gain.
- The expected types are transcribed from the VIR function map the
  serializer already consults (`with_fn_map`, bootstrap-18) — the
  same VIR source production's `fn_param_typs` reads. Same trust
  class as every existing `typ_data` transcription; NOT a new
  trusted decision (the DECISION stays reference-side). For callees
  with defcerts the param types are additionally cross-checked by
  the W7 defs bridge. Impl-time check: confirm the serializer's fn
  map covers prelude callees (`lib.seq.Seq.index`,
  `lib.view.View.view`) — if a callee is absent, the transcription
  falls back to `a.typ` EXACTLY as production does, and the subject
  stays an honest loud fail, never a silent pass.
- The defs-layer transcription (`raw_vir_*`, sst_serialize.rs:1761)
  emits `CallN` too; the same vocab change applies there uniformly
  (no special case — principle 5). Def bodies' args get expected
  types from the same map.

**F4 (Q4 — poison derivation):** RESOLVED: **side table on
FnCtxData; frames and goals untouched; the poison BIT is deleted
from the vocabulary, not relocated.**
- New FnCtxData fields: `residue_names: LeafList` (the interned
  name ids, sst_serialize.rs:1274/1320's pushes) and
  `prop_deeps` — a side table mapping poison-relevant prop leaf ids
  (FHyp props + FLetH eq props) to their `RawExp` transcriptions.
  Total on well-formed certs; a missing entry fails loud.
- refWp derives on the fly, at the assembly sites that read the bit
  today: `raw_exp_mentions(residues, prop_deep)` (simple recursive
  spec fn over RawExp atoms; name ids intern consistently by the
  atom-id invariant). Wrap-forcing = any poisoned hyp in the run;
  FLetH→FLet collapse = that let's own eq prop poisoned. Both are
  pure functions of the transcribed data.
- The carried bit slots are DELETED from FHyp/FLetH (no dead data,
  no second channel). Goal SHAPES are untouched — binders still
  compare by leaf id, wrap bodies still carry opaque prop ids
  (byte-neutrality, F6).
- FrameList is UNTOUCHED ⟹ `wp_stm_sound` and the whole W5
  development see zero semantic churn (the bit was assembly
  metadata, never semantically interpreted). This is why the deep
  content goes in a ctx side table and NOT on the frame: carrying
  it on FHyp/FLetH would thread a semantics-irrelevant field
  through the 285-fn soundness gate and invite id-vs-deep coupling
  questions. Trade-off recorded: a Lean purist might carry the prop
  on the frame; the side table keeps the semantic vocabulary pure
  and the churn surgical (principles 1/3, weighed).
- probe13 `poison_flip` kill RE-POINTED at the derivation input
  (today it zeroes the carried marks — post-A7 that's dead data and
  the kill would silently stop biting): overwrite the cert's
  `residue_names` with names that DO occur in the deep props ⟹ the
  derivation forces wrap ⟹ bridge flips 1→0. Live channel, both
  directions.
- The P1 contract paragraph in sst_serialize.rs's header is updated
  at landing: the poison mark is no longer trusted; `hyp_poison` /
  `lexpr_mentions_var` retire from the cert path.

**F5 (Q5 — the `&mut T` unsubstituted-typ quirk):** RESOLVED: **fix
production + mirror**, as a separate commit inside the A7 arc,
flagged for Danielle's veto. Principles 1+5: "bound hyp iff the
INSTANTIATED param typ is bounded" is both the right semantics and
the more predictable rule; the quirk is a completeness bug
(sound, but weaker caller contexts for every generic-&mut user).
The mirror follows production as always. Fixture subjects:
swap_incr/call_swap_incr. Goal-shape churn = new bound hyps on
generic-&mut callees (strictly more context; no tgt gate per the
constraint — probe11 scoped emits cover the tgt-side subjects).

**F6 (Q6 — byte-neutrality argument, stated as the lemma):**
For every currently-CLOSING bridge, rendered output is unchanged:
- *CallN:* a subject closes today ⟺ the old straight-render arm
  matched production ⟺ production applied no per-arg coercions at
  its CallN sites ⟺ (expected ≡ actual) for the coercion predicates
  at those sites ⟹ the new rule fires nothing. ∎
- *Call:* sites where the old arm closed split: (a) no production
  coercion — old and new both fire nothing; (b) the G2 auto-deref
  case (actual `TyRef(inner)`, expected `inner`) — old derived the
  deref from `actual` alone, new derives it from the pair, SAME
  output. The only behavior change is (actual `TyRef`, expected
  `TyRef`) — the vec_read view case, currently honest-fail, not
  closing. ∎
- *Poison:* the derivation reproduces `lexpr_mentions_var` over the
  same props with the same interned names ⟹ identical wrap/collapse
  decisions wherever the carried bit was correct. Enforced
  empirically: every probe bridge stays green; a wrong derivation
  reds a bridge loud. ∎
- *Cert data shape* changes corpus-wide (RawList element arity,
  FnCtxData arity, bit-slot deletion) — certs re-emit, golden
  re-vendors, probe baselines regenerate; bridge VERDICTS on
  closing subjects unchanged per above.
- ONE tactus-core edit for ALL of the vocab growth (the b77
  lesson): RawList elements, FnCtxData fields, bit deletion, Call
  re-source land together; one cache invalidation, one golden
  re-vendor.

## Acceptance

- probe9: `vec_read`, `vec_push7`, `fill_zeros`, `count_to_len` all
  reclassify hfail → CLOSE; every other subject byte-stable (per
  F6).
- probe11: `copy_word` + `find_cancellation_exec` reclassify →
  CLOSE (scoped per-module regen only — NO tgt gate).
- probe38: the vec_read Ret-goal `=0` stage-B tripwire FIRES (and
  is replaced by the close).
- Atom-fallback census before/after table on the scoped tgt emits
  (endgame acceptance: "shrinks measurably").
- Poison mark derived reference-side; carried bit deleted from the
  vocab; probe13 `poison_flip` re-pointed at the derivation input
  and still flipping; the P1 contract paragraph in sst_serialize.rs
  updated (the bit is no longer trusted).
- F5: production bound predicate on the substituted param typ +
  mirror; swap_incr/call_swap_incr re-close with the new bound
  hyps.
- D discipline: no new StmData arms and FrameList untouched (the
  vocab growth is leaf-rendering + ctx metadata), so
  `wp_stm_sound` is untouched; say so explicitly in the completion
  record.
- Battery: tactus-core gate + package gate + Link discharge 198/0,
  lean_verify units, e2e, probes 9/11/13/14/20/37/38, golden
  re-vendored.
