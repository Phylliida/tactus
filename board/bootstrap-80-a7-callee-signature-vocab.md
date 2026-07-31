# bootstrap-80 — A7: stage-B callee-signature vocabulary

Status: **SCOPE ITEMS 1+3 DONE 2026-07-31 (one session). probe9 ALL
33 bridges CLOSE (zero honest-fails anywhere in the corpus);
probe11 ALL 11 tgt subjects CLOSE; probes 13(21)/14/17/37/38 +
units 428+7/0 green; golden byte-stable. Remaining: scope item 2
(poison derivation, F4 — carded stages below).**
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
**AMENDED by the review addendum (A1 below): the render rule is the
full two-phase `coerce_lexpr` reconciliation, not a two-case
enumeration.**
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

## Freeze review addendum (2026-07-31, second pass — Danielle's
"what would come back to bite us" review)

**A1 — F3's rule was understated; restated as the full two-phase
reconciliation.** Production's decision is `coerce_lexpr`
(`expr_shared.rs:1101`): (phase 1) numeric-sort bridge — peel ALL
wrappers, `Int.toNat`/`Int.ofNat` at the bare value, rewrap;
(phase 2) wrapper-sequence reconciliation — longest common suffix,
peel the non-matching outer wraps, rewrap (`from=[Ref],to=[]` →
`.deref`; `from=[],to=[Ref]` → `Tactus.Ref.mk`; kind mismatch at
equal depth → peel+rewrap). The freeze's "ofNat + deref" enumeration
MISSED the depth-grow case, and it is not hypothetical: vec_push7's
cert carries `Call 11 (TyNamed 10) (Var 0 (TyNamed 12)) (TyNamed 12)`
(the &mut final-value `v` at the POINTEE type) where production
renders `view (Tactus.Ref.mk v)` — the `+1` mk-wrap. The reference
rule, restated over the TypData fragment (depth ≤1, kinds
Ref/Box distinct, pointees opaque):
- both bare: sort bridge iff TyInt↔TyNat (CastKind has both
  directions — the freeze's ofNat-only statement was also
  incomplete; toNat is the symmetric case).
- wrapper → non-wrapper: `.deref` (blind peel, matches production's
  inner-type-agnostic peel).
- non-wrapper → wrapper: `.mk` wrap of the target kind
  (`Tactus.Ref.mk` / `Tactus.Box.mk`).
- equal tags: passthrough (the vec_read view case) — EXCEPT
  TyBox↔TyRef, which is VISIBLE (distinct tags) and reproduces
  production's peel+rewrap.
Named blind spots (all fail LOUD — bridge divergence, never silent;
census-tag per P2 if one ever appears):
- sort-bridge-under-wrapper (e.g. `&int` arg → `nat` param):
  production peels, bridges, rewraps; TypData pointees are opaque
  leaf ids, so the reference cannot see the pointee's sort.
  Corpus population: expected zero.
- MutRef-vs-Ref at equal depth: both erase to `TyRef` — kind-blind
  (Lean erases the distinction; production's wrap sequences keep
  it). Expected zero.
- multi-layer wraps: cannot arise — TypData is depth-bounded 0/1;
  deeper types already fail loud at transcription.
The implementation mirrors coerce_lexpr's TWO-PHASE STRUCTURE
(sort first, then wrappers), not a case list — principle 1.

**A2 — E2/F2 is bigger than stated (both coercions, not just
ofNat).** vec_push7's oblig leaves render `((v : Vec …) : Seq Int)`
— Vec's OWN View instance, NO `Ref.mk` — while the goal path renders
`Tactus.Ref.mk v` + the Ref View instance. Production's oblig-leaf
path diverges from its goal path on the FULL coercion table, not
just ofNat. Deferral from A7 stands (not on the bridge comparison
path; both forms elaborate via defeq/NatCast), but this becomes
load-bearing at E (W8 authority flip) and at any future hyp-prop
deepening. RECOMMEND a separate production-cleanup brick: unify the
oblig-leaf path on `coerce_lexpr` (principle 1; card it at E at the
latest).

**A3 — the N2 IsVariant detector is a SECOND trusted predicate the
freeze was silent about.** The sst_serialize.rs contract names two:
the poison mark (F4 retires it) AND `branch_isvariant_of` (shared
single-source, common-mode). Deriving it reference-side needs a
datatype environment in the mirror vocabulary (dt-in-map,
multi-variant, typ-args) — a W7-adjacent growth, NOT this brick.
Scoped OUT explicitly: it remains trusted post-A7, pinned live by
the four IfCtor mutation kills, and is the natural next trust-shrink
target after B (candidate: reference-side datatype env — fold into
the E-milestone planning). The IfCtor poison BITS, by contrast, are
the poison mark applied to IfCtor frame hyps — F4's `prop_deeps`
table must cover those props too (impl-time check: enumerate every
`hyp_poison` call site — FHyp props, FLetH eq props, the c_lx site
at :1104, IfCtor frames — and transcribe deep for exactly those).

**A4 — F4 landing sequence: the cross-check era comes free, then
delete.** One vocab edit (side table + residue_names land; bit
slots still present), refWp switches to derivation-driven assembly;
if derivation ≠ what the bit would have said anywhere on the
corpus, that subject's bridge reds — the probe battery IS the
equivalence cross-check (the bit was validated by green bridges,
so green-after-switch ⟹ derivation ≡ bit on the corpus). Delete
the bit slots in a follow-up edit within the same arc once probes
are green; re-point `poison_flip` at the derivation input at
deletion time (not before — until then the old kill still bites
the old channel).

**A5 — new probe13 kill class for the expected-typ channel.** The
per-arg expected types are transcribed data the bridge checks, but
liveness wants a kill: perturb one expected typ (Nat↔Int, or add/
remove a TyRef layer) in a pinned cert ⟹ bridge flips 1→0. Cheap;
same harness as the existing expression kills.

**A6 — accepted blast-radius notes (no action, recorded).**
(a) Obligation certs now depend on callee SIGNATURES (per-site
expected types): a vstd/prelude signature change ripples into
obligation certs, not just defcerts — correct (the goals do change)
but a wider invalidation surface for warm-cache/byte-stability.
(b) `prop_deeps` grows every cert and the `decide` workload on
Loop-heavy subjects (count_to_len: 21 goals) — watch probe9
wall-times; report in the completion record.
(c) F5's production fix changes goal shapes for generic-&mut
callees beyond the fixture (tgt modules outside probe11's scoped
pair stay stale-shape until their next regen) — accepted under the
no-tgt-gate constraint.

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
- Poison mark derived reference-side (A4 sequencing); carried bit
  deleted from the vocab by arc end; probe13 `poison_flip`
  re-pointed at the derivation input and still flipping; the P1
  contract paragraph in sst_serialize.rs updated (the bit is no
  longer trusted; the N2 detector paragraph stays, per A3).
- probe13 gains the expected-typ kill class (A5).
- F5: production bound predicate on the substituted param typ +
  mirror + swap_incr/call_swap_incr pins, ONE commit.
- D discipline: no new StmData arms and FrameList untouched (the
  vocab growth is leaf-rendering + ctx metadata), so
  `wp_stm_sound` is untouched; say so explicitly in the completion
  record.
- Battery: tactus-core gate + package gate + Link discharge 198/0,
  lean_verify units, e2e, probes 9/11/13/14/20/37/38, golden
  re-vendored.

## DONE (2026-07-31, one session) — scope items 1 + 3

- **Stage 1: the vocabulary (`1b01cb11`).** RawList elements pair
  each arg with the callee's EXPECTED param typ (serializer:
  `fn_param_typs_of` extracted from production's method as the single
  source, over the same fn_map; fallback = arg.typ, mirroring
  `into_slot(&a.typ)`). `reconcile_arg` derives the per-arg slot
  coercion reference-side as a TAG if-chain (a nested match breaks
  the one-line Lean emission — "redundant alternative", the
  documented lib.rs:3161 idiom): sort bridge both directions +
  wrapper reconciliation (Ref/Box ↔ bare deref/mk-wrap, Ref↔Box
  peel+rewrap, passthrough when the callee param IS ref-typed — the
  vec_read G2 mis-derivation). `ExprData.RefMk/BoxMk` first-class
  wrapper nodes (id-free; the reference cannot mint interned ids —
  production's transcriber maps the same apps). New pin fn
  `a7_reconcile_kernel_computes`. **Gate 286/0 + pkg gate 54 +
  discharge 198/0.**
- **F5 pulled forward (`df5c184b`) — vec_read's residual was NOT the
  leaf class.** After stage 1, vec_read's goal 1 still diverged:
  an EXTRA `_h_hoist` bound hyp in the reference telescope. Root
  cause: production's `type_bound_predicate` ran on the UNINSTANTIATED
  declared typ, so a generic callee (`Seq.index` → `Int`; `swap_incr`
  at `&mut T`) silently elided the numeric bound hyp — the b78
  "mirrored production quirk", bigger than carded (Phase-E ret bound
  + ∀-path + prophecy, not just Phase-1). Fixed per the freeze:
  `instantiate_callee_typ` single-source; production substitutes at
  all four sites; the cert serializer's Phase-1 mirror substitutes
  identically (its ret-bound already did). The serializer's existing
  FHyp then matched production's NEW theorem binder exactly.
- **Assign-rhs `into_slot(dest_typ)` (`f22a50c9`) — find_cancellation's
  residual, masked inside the "A7-class" attribution.** probe11
  per-goal bisection (24 goals, 11–20 diverging): the cond-setup
  hoisted eq prop read `tmp__6 = w` vs production's `tmp__6 = w.deref`
  — production's `walk_let` bridges the rhs into the dest typ
  (`sst_exp_to_typed` + `into_slot`), the serializer rendered raw.
  Mirrored with the binder-aware ctx (byte-neutral switch: the ctx
  only affects class-method coercion, absent from every closing
  Assign rhs).
- **Classification sweep:** probe9 33/33 CLOSE (vec_read, count_to_len,
  fill_zeros, vec_push7 reclassified; every other subject
  byte-stable — F6 held incl. the golden). probe11 11/11 CLOSE
  (copy_word + find_cancellation_exec reclassified; scoped
  per-module regen only — NO tgt gate, per the constraint).
  probe13 → 21 classes: the expected-typ kill (A5) + the b79 Loop
  classes strengthened to the FULL deep bridge (strips retired).
  probe38: the A7 tripwire FIRED as designed → close+kill pair.
  probe17: pre-existing stale-red since the prelude split (pinned
  e81f dir; NOT in the recent battery lines) — fixed to the
  all-preludes glob; defs bridge closes WITH the new CallN pairs.
  probe37: eval/edenote gained RefMk/BoxMk arms (the non-exhaustive
  match produced sorryAx — caught by the probe's own axiom audit,
  exactly the fail-loud design). Units 428+7/0; golden byte-stable.
- **probe20 DEFERRED (documented):** its ~130 vendored tgt defcerts
  carry the OLD RawList shape and will not elaborate against the new
  vocabulary; regeneration needs the tgt-slice emit, deferred under
  the no-tgt-gates constraint. Re-emit with the new binary when tgt
  work resumes.
- **e2e: 829/2** — the 2 = the documented pre-existing examples
  pair (flat_combine, tutorial_fifo), identical to the b79 baseline.
  F5's new bound hyps are purely additive context: zero user proofs
  broke corpus-wide.
- **D discipline:** no new StmData arms; FrameList untouched;
  `wp_stm_sound` untouched (the vocab growth is leaf-rendering +
  Call-arg data). The soundness claim covers exactly what it covered
  before.
- **Before/after census (endgame acceptance):** A7-class honest-fails
  6 → 0 (probe9 ×4 + probe11 ×2, all CLOSE); probe9 honest-fail set
  EMPTY (was: vec_read, count_to_len, fill_zeros, vec_push7);
  probe11 honest-fail set EMPTY (was: copy_word,
  find_cancellation_exec); the vec_read Ret-goal `=0` stage-B
  tripwire FIRED and is replaced.

**Remaining (scope item 2, F4 — poison derivation):** FnCtxData gains
`residue_names` + the `prop_deeps` side table; refWp derives
wrap-forcing + the FLetH→FLet collapse via `raw_exp_mentions`; the
carried bit is deleted after the cross-check era (A4 sequencing:
bridges green with derivation active ⟹ derivation ≡ bit on the
corpus); probe13 `poison_flip` re-points at the derivation input.
Impl-time checklist (from A3): enumerate EVERY `hyp_poison` call
site (FHyp props, FLetH eq props, the c_lx cond site :1104, IfCtor
eq/neg props) and transcribe deep for exactly those.

## Design review 2026-07-31 (pre-impl, second session — ACCEPTED with one refinement)

Reviewed the frozen F4 plan against both codebases (all `hyp_poison`
call sites, the refWp gate/assembly/semantic dispatchers, probe13,
the P1 contract). Verdict: proceed as frozen; findings below.

**Freeze choices validated against the code:**

- **`residue_names` as a GLOBAL ctx field is required, not just
  convenient.** The obvious simplification — derive the residue set
  from the `FLetR` frames in the current prefix — is subtly WRONG:
  production's `residue_names` is monotonic across branch joins (the
  branch state save at sst_serialize.rs:1006 saves
  `(bound_names, rename_env, flet_forced, poison_forced)` and
  deliberately NOT `residue_names`). A frame-prefix derivation
  diverges from production at joins; the global table mirrors
  production's actual implementation state (principle 5). Do not
  "simplify" this later.
- **Full `RawExp` transcription over a var-id projection.** A smaller
  per-prop Var-id table would be a serializer-computed projection —
  another trusted semantic predicate, the same class as the bit
  itself. Full transcription keeps the serializer dumb and is
  forward-compatible with hyp-prop deepening at E.
- **Gate-time derivation (at `has_poisoned_hyp`), not build-time.**
  `StmData::Call.post` is a serializer-emitted `FrameList` appended
  VERBATIM by `frame_after` — refWp never builds those frames, so
  build-time derivation can't reach their FHyp bits without a rewrite
  pass. Deriving at the gate covers StmData-built and Call.post
  frames uniformly, single-sourced. (Coverage census: of the 68
  `FrameList.FHyp` literals in vendored certs, ZERO carry bit 1; the
  only positive poison marks corpus-wide are add_capped's
  Assert/Assume pair. Say so in the completion record.)

**REFINEMENT (adopted): precompute `poisoned_props: LeafList` once at
`ref_wp`, thread ONE param — not the two tables.** One spec fn
`poisoned_props(residues, deeps) -> LeafList` (prop ids whose deep
mentions a residue); the gate and the collapse arms become a
`leaf_mem` membership check (the file's `binder_has_id` nat idiom).
Same information, single derivation site, one threaded param, cheaper
kernel reduction than per-goal-per-frame mention scans (count_to_len:
21 goals — A6(b)). probe13 re-point unaffected: overwrite
`residue_names` → the derived set picks up spurious ids → wrap forces
→ flip. Missing-entry semantics FALL OUT of the precompute: an absent
entry derives 0 (no membership) — loud-by-bridge in the divergence
direction (production wrapped, we hoist → red), correct-by-luck in
the other. Totality loudness therefore rests on the serializer-side
assertion, below.

**Impl-time specifications (settled at review):**

- `raw_exp_mentions` returns `nat` (1/0), NOT bool
  (Classical.propDecidable sticks `decide`); structural_decreases;
  td_tag if-chain idiom (no nested match).
- Totality, two layers: (a) serializer asserts every
  `hyp_poison`-checked prop id gets a `prop_deeps` entry (built at
  the same call site — enforceable at emission, loudest); (b)
  reference-side missing entry derives 0 (see refinement). New
  probe13 kill class: delete the add_capped prop-25 entry → missed
  poison → hoist vs production wrap → bridge flips 1→0.
- Loop cond fan-out: `cond_poison` covers FIVE props (`cond_ann`,
  `neg_cond_ann`, `neg_neg_cond_ann`, `break_guard_ann`,
  `break_use_ann`) — `prop_deeps` needs all five entries per loop;
  derive per-prop, no shortcut (uniform, principle 5).
- The `AssignH`/`RetLetH` collapse move REQUIRES a paired serializer
  change in the same landing: the serializer STOPS collapsing
  poisoned typed lets to `Assign`/`RetLet` (emits the hoist payload
  always; `Assign`/`RetLet` narrow to typ-less/Bool-only) and refWp
  derives the collapse — a poisoned eq prop forces wrap ONLY via the
  collapse to plain FLet (`has_poisoned_hyp`'s FLetH arm reads no
  bit), so the two sides must land together. Goal-shape-neutral
  (FLet/FLetH wrap-render identically; the goal was wrap-forced
  either way).
- Acceptance wording fix: "`wp_stm_sound` untouched" holds for era 1
  only. Era 2 (slot deletion) threads the derived set through
  `wp_stm`/`gate_wrap`/`close_sem_*`, so `wp_stm_sound` gains one
  universally-quantified param — mechanical, content-free (b79 arity
  16→21 precedent). Say exactly that in the completion record.
- probe13 re-point kills BOTH directions: overwrite `residue_names`
  with occurring names (forces wrap) AND delete a needed name (missed
  poison → hoist vs production wrap). Today's `poison_flip` covers
  only the zero-marks direction.
- Era-2 doc sweep: FHyp's doc comment (lib.rs:752-757, "the model's
  leaves are opaque ids, so the serializer computes the mark
  textually") and the StmData Assert/Assume/If/IfCtor/Loop
  poison-field docs.
- A4 masking-gap check PASSES: a bit/derivation divergence inside an
  already-wrap-forced goal (mut-param fns) is irrelevant — production
  doesn't care either — so probes-green ⟹ derivation ≡ bit wherever
  it matters.

**Alternatives considered and rejected:** (a) explicit per-cert
`bit ≡ derivation` decide-pin era — needs throwaway cert-emission
machinery; A4's probes-as-cross-check has the F5/F6 precedent. (b)
In-place hyp-prop deepening (FHyp carries `RawExp`) — right end state
at E, wrong increment now (breaks byte-neutrality on every goal); the
side table migrates cleanly.
