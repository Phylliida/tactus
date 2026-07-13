# N4 → W3: the reference WP and its follow-ups — spec

**Date:** 2026-07-12
**Status:** spec'd, not started. Parent: `DESIGN-bootstrap.md` §12/§5;
sibling: `DESIGN-N3-serializer.md`. Covers N2.1 (mirror-type amendments),
N4 (census), N5 residue (vocabulary olean), W2 (refWp stage A), W3
(differential gate), and pointers into W4/W5.

---

## 0. N2.1 — mirror-type amendments (BEFORE N3a freezes the literal shape)

Writing refWp's equations on paper (§2) shows `StmData` is missing fields the
reference computation needs. These change `tactus-core/lib.rs` and must land
before the serializer exists, or the literal shape churns:

| Variant | Amendment | Why |
|---|---|---|
| `If` | add negated-cond leaf: `If(cond, neg_cond, then, else)` | the else-branch hypothesis is the RENDERED `¬cond` — a distinct leaf text; refWp can't synthesize leaf ids |
| `Loop` | add loop-state binder list: `binders: Box<BinderList>` (new list type: `(binder id, typ leaf)` pairs), plus `neg_cond` leaf | maintain/use telescopes quantify over the modified locals (P7); production computes this set — the literal must carry it |
| `Call` | add `dest: u64` binder id + typ leaf | ensures-hypotheses bind the call result |
| `Ret` | becomes `Ret(Box<LeafList>)` | the obligation is each ensures INSTANTIATED at the returned value — instantiated texts are leaves rendered at the return site |
| params (FnCtx, §2.1) | each param carries an optional bound-hyp leaf | int-typed params get `h_x_bound` hypotheses (P6/P7); they are leaves, not structure refWp invents |
| GoalData spine | interleave-faithful: goals fold a SINGLE ordered frame (see §2.1) | three-parallel-lists loses `∀x, h → let y, h2` ordering |
| typ params | `FnCtxData.typ_params`: (binder id, kind leaf) list; instance binders (`[Nonempty A]`) as ordinary entries with distinguished leaves | polymorphic fns open with `∀ (A : Type) [inst : Nonempty A]` telescopes (P8 island evidence); tgt is generics-heavy — without this the census dies on arrival |

Also new: `FnCtxData` (§2.1), `BinderList`, and `FrameList`. Same rules as N2: no mutual
recursion (all new lists are leaf-only or one-way), `structural_decreases`
everywhere, `decide` sanity proofs extended, tripwire table note updated.
Estimated: small, one sitting, re-run the N2 acceptance (pkg gate 0 errors).

## 1. N4 — the census (small)

Run `--tactus-emit-cert` over tactus-group-theory (~3116 fns) and the fixture
family; the crate-end `certified M/N` summary plus per-construct rejection
counts IS the deliverable:

* a ranked table (construct → fn count) appended to THIS doc — it becomes the
  stage-B coverage roadmap and the first honest measure of the stage-A subset;
* cert-emission overhead measured (wall-clock delta with/without the flag on
  tgt) — budget expectation: rendering leaves twice is the only real cost;
* zero verification-behavior delta (the flag must not perturb verdicts —
  N3 acceptance §7.4 re-checked at scale).

Requires the flag to ride through tgt's crate-local `check.sh` (one-line
plumbing there; the memory note "verify tactus-* with the CRATE-LOCAL
check.sh" applies).

## 2. W2 — refWp stage A (the heart)

Reference WP authored as `tactus-core` spec fns over the (amended) mirror
types. Emitted through crate-defs like everything else; the emitted defs ARE
the checker the certificate runs.

### 2.1 Shape

```
FnCtxData = { params: BinderList, param_bounds: LeafList(optional per param),
              reqs: LeafList, enss: LeafList }

refWp    : FnCtxData → StmData → GoalList     -- the certificate's LHS
wpStm    : CtxFrame → StmData → GoalList      -- worker
CtxFrame  = FrameList                          -- ONE ordered list
FrameList = FNil | FBind(id, typ_leaf, tail) | FHyp(leaf, tail)
          | FLet(id, val_leaf, tail)
```

`CtxFrame` is a SINGLE ordered entry list, not three parallel lists — the
production telescope INTERLEAVES binders, hypotheses, and lets (P7's
loop-maintain and P6's let-in-Prop goals both show `∀ x, h → let y := e;
h2 → …`), and three separate lists cannot reproduce the interleave order.
(Review fix 2026-07-12: the first draft of this spec had `{binders, hyps,
lets}` — a defect caught on inspection, recorded here as a warning to
future spec-writers: the frame IS the goal spine, so its type must be
order-faithful.) Every emitted goal is the frame folded entry-by-entry
around an obligation leaf; one `GoalData` per obligation site, appended in
walk order (production theorem order = O4 pairing). Binder-id discipline
under shadowing: every binding OCCURRENCE gets a fresh id (P7's SSA
shadowing), assigned in walk order by the serializer.

**No higher-order continuations.** spec_fn closures are trigger- and
kernel-hostile (memory: closure-identity arc). The walker is first-order:
`wpStm(frame, stm)` returns the goals of `stm` given what's BEFORE it, and a
`frameAfter(frame, stm)` companion computes the frame extension for what
follows. `Seq(a, b)`: `wpStm(f, a) ++ wpStm(frameAfter(f, a), b)`. Both
functions are single-datatype structural recursion over `StmData` — this is
exactly what N2's Seq/Skip design bought.

### 2.2 The equations (stage A, informal — code is 1:1)

* `Assert(e)`: emit `close(frame, e)`; frameAfter adds hyp `e`.
* `Assume(e)`: no goal; frameAfter adds hyp `e`.
* `Assign(x, rhs)`: no goal; frameAfter adds `Let(x, rhs)`.
* `Call{reqs, enss, dest}`: emit `close(frame, r)` per req; frameAfter adds
  binder `dest` then hyps `enss`.
* `If(c, nc, t, e)`: goals of `t` under hyp `c` ++ goals of `e` under hyp
  `nc`; frameAfter — stage A restriction: join frames are NOT merged (the
  production emits per-branch continuations by duplicating the rest? — OPEN
  QUESTION §5.1: confirm how the production walker handles post-if
  continuation; the mirror follows whatever it does, discovered from the
  cert diffs of a two-branch fixture fn).
* `Loop{invs, cond, nc, binders, body}`:
  - init: `close(frame, inv_i)` for each inv;
  - maintain: under fresh `binders`, hyps `invs ++ [cond]`, goals of `body`
    with post = invs (each inv closed at body end);
  - use: frameAfter = frame extended with `binders`, hyps `invs ++ [nc]`.
* `Ret(ens_leaves)`: emit `close(frame, e)` per instantiated ensures.
* `DeadEnd(s)`: goals of `s`; frameAfter = frame UNCHANGED (facts discarded).
* `Skip`: nothing.
* `refWp` seeds the frame from `FnCtxData`: param binders + bound hyps +
  requires hyps, then `wpStm`, then the implicit `Ret` if the body doesn't
  end in one (OPEN §5.2: where the production puts the postcondition
  obligation for fall-through bodies).

### 2.3 Equality for `decide`

Tactus emission derives `Inhabited` only — no `DecidableEq`. Rather than a
new emission feature, W2 ships `goal_eq : GoalData → GoalData → Bool` and
`goals_eq : GoalList → GoalList → Bool` as structural spec fns in
tactus-core (kernel-compute like everything else). The bridge line is
`example : goals_eq (refWp ctx sst) production = true := by decide`.
(A `deriving DecidableEq` emission knob is the cleaner long-term form —
recorded as a W1.5-style follow-on, not a W2 blocker.)

### 2.4 W2 acceptance

1. Every fixture cert file's bridge line closes by `decide` (and `rfl`).
2. **Mutation kills** (the certificate must be SENSITIVE, not just green):
   hand-perturb copies of one cert file — swap two hypotheses, drop a
   binder, reorder two goals, change one leaf id — each mutation must flip
   the verdict. Checked in as `probe-w0/probe10_mutations/` with a runner.
3. refWp itself verifies lean-only-clean through the package gate, all
   spec fns structural, `decide` unit-examples in-crate.
4. Wall-clock: bridge cost per fixture fn recorded (P2 baseline: 600-stm
   ≈ 2.8s with raised maxRecDepth; expect fixture fns ≪ that).

### 2.5 Honest scope statement (rides in every cert file header)

Stage A certifies statement ASSEMBLY: telescopes, hypothesis order and
content-by-id, let-chains, obligation multiplicity and order. It does NOT
certify: leaf rendering (stage B/W6), the serializer (it's the TCB), the
frontend, or SST semantics adequacy (W5f). A stage-A pass + the four
leaf-renderer bugs of 2026-07-11 coexisting is possible and expected — say
so wherever the certificate is described.

## 3. W3 — the differential gate (the payoff before any proof)

Run serializer + bridge over tgt: every fn where `decide` says NO is a bug in
production, refWp, or the serializer — all three are interesting. This is a
bug-FINDING deliverable, independent of the W5 soundness proof.

* Mechanics: certs emitted during a normal gated run; bridge files batch-
  elaborated like stmt modules (reuse `ensure_stmt_olean`-style plumbing);
  failures reported per-fn with both GoalData terms pretty-printed and
  first-divergence path computed by a small Rust differ (goal index → spine
  position) so triage doesn't read raw terms.
* Triage discipline: every divergence gets classified (production bug /
  refWp bug / serializer bug / stage-A scope gap) in a running table in this
  doc; scope gaps feed stage B, production bugs get pinned e2e tests like
  this week's five.
* Acceptance: tgt divergences = 0 unexplained; certified fraction reported;
  bridge wall-clock budget ≤ the package gate's own cost (else flag for W4).

## 4. W4/W5 pointers (spec'd when adjacent)

* **W4**: `--tactus-emit-cert` + bridge default-on under the package gate;
  needs W3's cost numbers and a cache story (cert files content-keyed like
  islands). Not spec'd further here.
* **W5**: the soundness loop (refWp ⟹ SstSem, authored in tactus) — master
  plan §5 owns the ladder (W5a fuel big-step semantics first). One design
  question this review surfaces that the master plan glosses: **a fuel
  evaluator cannot evaluate opaque leaves**, so W5 over stage-A shapes needs
  either (a) stage B (deep expressions) landed first — serializing W5 behind
  W6 and losing the planned parallelism — or (b) a VALUATION-PARAMETRIC
  semantics: `SstSem` takes a leaf oracle (`LeafId → State → Value`) and
  `refWp_sound` quantifies over all oracles consistent with the leaf table's
  typing. (b) preserves parallelism and is the natural reading of "leaves
  cancel" at the semantic level; it also front-loads the leaf-typing
  discipline stage B needs anyway. Decide at W5a kickoff; recorded as open
  question §5.5.

## 5. Open questions (answer during W2, record here)

1. Post-`If` continuation: does the production walker duplicate the rest
   under each branch, or join? Mirror must match; discover empirically from
   a two-branch fixture cert diff (§2.2).
2. Fall-through postcondition: where the production emits the ens obligation
   when the body doesn't end in explicit `Ret`. Related shape question
   (raised in N2.1 review): the explicit `Ret(LeafList)` bakes the returned
   value into each leaf at render time, so no frame return-binder is needed
   for explicit returns. If the fall-through path instead binds the return
   value as a frame `∀`/`let` (rather than rendering a closed instantiated
   leaf), `FnCtxData` will need a `return_var: (id, typ)` field — deliberately
   NOT added in N2.1 (the amendment table omits it). Confirm empirically
   before adding, so the literal shape doesn't churn.
3. Loop-body post: are body-end invariant obligations distinct Assert nodes
   in the SST at the snapshot point (in which case `Loop` handling shrinks),
   or walker-synthesized (in which case refWp synthesizes identically)?
   P7's fcx evidence suggests walker-synthesized; confirm.
4. Overflow-guard asserts: present as SST `Assert` nodes at the snapshot
   (then free) or walker-injected (then refWp must mirror the injection —
   preferably argue for serializing post-injection instead).
5. W5 leaf semantics: valuation-parametric SstSem vs. deep-exprs-first —
   see §4; decide at W5a kickoff.
6. Mutual/SCC exec fns and non-default loop flavors
   (`invariant_except_break`, `no_unwind` interplay): stage-A exclusions —
   confirm the serializer rejects them loudly rather than mis-capturing.

## 6. Sequencing

N2.1 (amendments) → N3a/b/c (serializer, per its spec) → N4 (census) →
W2 (refWp: worker + equations session, then bridge + mutations session) →
W3 (tgt gate + triage). Each brick ends with the battery green and this doc's
open-question ledger updated.
