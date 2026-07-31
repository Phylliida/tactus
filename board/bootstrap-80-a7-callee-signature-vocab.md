# bootstrap-80 — A7: stage-B callee-signature vocabulary

Status: **CARDED 2026-07-31 — step-0 evidence frozen (§ below).
Design direction set; open questions listed for design freeze at
impl start (the b79 discipline: freeze before any model edit).
Implementation not started.**
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
   recompute "mentions residue" over the deep `ExprData` leaves in
   tactus-core; the serializer's `hyp_poison` copy becomes a
   cross-check, then retires. A trusted bit should not outlive the
   first milestone able to check it.
3. **Sequenced candidate (b78 card §4, mirrored production quirk):**
   Phase-1 bound predicate runs on the UNSUBSTITUTED param typ — a
   generic `&mut T` callee instantiated at u64 gets no bound hyp on
   the existential (sound, incomplete; both sides agree so the
   bridge closes). Production improvement candidate; decide at
   design freeze whether it rides this churn or stays mirrored.

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
  `TyRef` ⟹ no deref. The carried `argty` (`TyRef 14`) happens to
  equal BOTH the actual and the param typ for this node, so the cert
  alone cannot disambiguate which the serializer transcribes —
  resolve at design freeze (Q1).
- **ofNat:** the CallN arm renders args STRAIGHT (lib.rs:1262-1265,
  "per-arg expected-type coercion is deferred to W7c"). `Seq.index`'s
  index param is `Int`; the arg `i` is `Nat`; production materializes
  `Int.ofNat i`. CallN carries NO per-arg param types today — this
  is the vocabulary gap proper.

### E2 — leaf 8 vs leaf 9: the ofNat asymmetry

The cert intern table has BOTH `r = Seq.index … (view v) i` (leaf 8,
NO ofNat) and the span-marked `… (Int.ofNat i)` (leaf 9, WITH
ofNat). Two leaf shapes of the same prop exist in one cert — which
goal/hyp position each serves (ensures-phase rewrite vs hyp leaf) to
be pinned at design freeze; the per-arg rule must reproduce each in
its position (or the asymmetry is itself a production artifact to
mirror exactly — evidence first, no guessing).

### E3 — the mechanism precedent already exists

`RawExp::Call` (single-arg) already carries `argty` and derives
nat-coercion + ref-deref per-arg (lib.rs:1221-1226); `CallN` is the
un-done sibling. The fix is a VOCABULARY extension (callee param
types available to `render_exp` at multi-arg sites), not another
G-pattern — per the endgame doc. W7's defs layer already transcribes
spec-fn param/ret types (`RawDef` → `DefData`, bridge-checked by
defcert), so a signature table is bridge-cross-checkable against an
already-certified channel.

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

### E5 — poison-mark site (for scope item 2)

`sst_serialize.rs:1028` `hyp_poison`: text check via
`lexpr_mentions_var(e, residue_name)` — a TRUSTED semantic predicate
(P1: the contract header says so; probe13 `poison_flip` pins the
channel). Domain = `residue_names` (in-scope hoist-residue names).
Reference-side derivation needs: the residue-name set available
reference-side (check whether it already enters the cert ctx), and a
`mentions` predicate over deep `ExprData` (leaves are deep since
W6d — the derivation is expressible today). Serializer copy becomes
a cross-check (bridge-level: derived ≠ carried ⟹ loud), then the
carried bit retires.

## Design direction (for freeze at impl)

- Per-arg (callee param typ, actual arg typ) pairs drive BOTH
  decisions uniformly: deref iff arg `TyRef(inner)` ∧ param =
  pointee; ofNat iff arg `TyNat` ∧ param `TyInt`. This SUBSUMES the
  G2 special case — the single-arg Call arm should move to the same
  rule (byte-neutrality on closing subjects is the acceptance gate,
  see below).
- Vocabulary home for the param types: the two candidate shapes are
  (a) per-call-site carried expected types (CallN gains a parallel
  param-typ list; Call's `argty` re-sourced to the callee param),
  (b) a callee-signature table on `FnCtxData` (fn id → params + ret,
  cross-checkable against the W7 defcert channel). Decide at freeze —
  criterion: predictability/transparency of the emitted cert data
  (guideline: favor simple and predictable over special cases) and
  no trusted-surface growth (the types must be transcriptions the
  defs layer can cross-check, not serializer-computed decisions).
- Poison derivation: `mentions` over `ExprData` reference-side;
  derive the bit; cross-check against the carried bit for one
  release (both present, mismatch = loud), then retire the carried
  bit and the `hyp_poison` text check. probe13 gains a kill class on
  the DERIVED bit (zero the derivation input ⟹ bridge flips).

## Open questions (resolve at design freeze, evidence first)

1. Is the single-arg Call's carried `argty` today the ACTUAL arg
   typ or the callee PARAM typ? (E1: indistinguishable on vec_read.)
   Find a G2 subject cert (auto-deref spec call) and read it.
2. Which positions do leaf 8 (no ofNat) vs leaf 9 (ofNat) serve?
   Is the no-ofNat leaf itself correct, or a second coercion gap?
3. Signature-table vs per-site carried types (above) — pick by the
   transparency/predictability criterion + churn radius (FnCtxData
   arity bump is cache-churning; batch ALL vocab growth in ONE
   tactus-core edit per the b77 lesson).
4. Does the residue-name set reach the cert today, or must it be
   added to the ctx (more vocab growth — batch with Q3)?
5. The `&mut T` unsubstituted-typ quirk (scope item 3): fix
   production + mirror the fix, or keep mirroring? Danielle's call
   at freeze.
6. Byte-neutrality strategy: every currently-CLOSING bridge must
   stay byte-identical. The unified per-arg rule must be provably
   identical to the old rules wherever no View/multi-arg-coercion
   fires — state this as a lemma-shaped argument on the card at
   freeze, then let probe9/11/13/14 enforce it.

## Acceptance

- probe9: `vec_read`, `vec_push7`, `fill_zeros`, `count_to_len` all
  reclassify hfail → CLOSE; every other subject byte-stable.
- probe11: `copy_word` + `find_cancellation_exec` reclassify →
  CLOSE (scoped per-module regen only — NO tgt gate).
- probe38: the vec_read Ret-goal `=0` stage-B tripwire FIRES (and is
  replaced by the close).
- Atom-fallback census before/after table on the scoped tgt emits
  (endgame acceptance: "shrinks measurably").
- Poison mark derived reference-side; serializer copy cross-checked
  then retired; probe13 kill class on the derivation; the P1
  contract paragraph in sst_serialize.rs updated (the bit is no
  longer trusted).
- D discipline: no new mirror arm without a model counterpart —
  the render-side vocabulary growth is leaf-rendering only (no new
  StmData arms), so `wp_stm_sound` is untouched; say so explicitly
  in the completion record.
- Battery: tactus-core gate + package gate + Link discharge 198/0,
  lean_verify units, e2e, probes 9/11/13/14/20/37/38, golden
  re-vendored if any byte-stable churn.
