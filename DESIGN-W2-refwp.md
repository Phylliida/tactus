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

### 1.1 Census run — mechanism validated + two prerequisites the plan missed (opus-b14-cont, 2026-07-14)

Board `bootstrap-05`. The mechanism works end-to-end; two setup facts the
"one-line plumbing" framing did not anticipate turned up and gate the
tgt-scale table.

**Prerequisite A — the flag is NOT in the tgt-facing binary.** tgt's
`check.sh` invokes `../tactus/source/target-verus/release/verus` (the
`tactus/` checkout, HEAD `f2f80a0`, built Jul 12). That binary predates the
cert work — `--tactus-emit-cert` is unknown to it (`--help` has no such
flag). The flag lives only in the `tactus-bootstrap/` checkout (same fork
`Phylliida/tactus.git`, HEAD ahead by all of bootstrap-01..17). So the census
must run under `tactus-bootstrap/source/target-verus/release/verus` — either
point tgt's `check.sh` at it (a `VERUS=` override, still ~one line) or rebuild
`tactus/` from the bootstrap commits. I used the bootstrap release binary
directly.

**Prerequisite B — the census is cache-confounded; it must run COLD.** Cert
emission (`emit_cert`) is gated behind *actual* verification of a fn — a
cache-hit fn is skipped before the emit path, so it is never censused. A warm
run of tgt (`-V cache`, 12M warm cache) reported `24 verified, 0 errors, 6322
cached` and a census note of only **`certified 1/9 fns`** — i.e. the census
covered just the 9 cert-eligible fns among the 24 that happened to re-verify,
not the ~3116-fn crate. **A tgt-wide census requires running WITHOUT `-V
cache`** (omit it — the raw binary does not cache by default; `--no-cache` is
a `check.sh`-only flag and is rejected by the binary). Cold runs neither read
nor write the cache, so the warm 12M cache is preserved.

**Verdict-neutrality confirmed at both scales (N3 §7.4 re-check):** `0 errors`
with the flag on in every run, including the warm tgt run (`24 verified, 0
errors, 6322 cached`). The flag does not perturb verdicts. ✓

**Fixture-family census (complete, cold, `bootstrap-fixture/lib.rs`, 14 fns):**

| metric | value |
|---|---|
| certified | **9 / 14** (64%) |
| verified / errors (flag ON, cold) | 20 / **0** |
| verified / errors (flag OFF, cold) | 20 / **0** (identical → zero verdict delta) |
| cert files written | 9 `*.cert.lean` |
| wall-clock flag OFF / ON (cold) | 1.073s / 1.047s (**overhead in the noise at this scale**) |

Uncertified constructs (fixture) — ranked:

| construct tag | fn count | fns |
|---|---|---|
| `call` (`StmX::Call`) | **5** | quad_exec, count_down, vec_read, vec_push7, fill_zeros |

At fixture scale the **entire** stage-A gap is `StmData::Call` — exactly
`bootstrap-02b`. (Overhead is unmeasurable here because the fixture verifies
in ~1s; the "rendering leaves twice" budget only shows at tgt scale.)

**tgt-wide census (COMPLETE — cold run, `src/lib.rs`, 3116 fns, 1m40s).**

The single most important finding reframes the whole census: **stage-A cert
emission is EXEC-FN-ONLY.** `emit_cert` is called only from
`emit_package_exec_fn` / its island sibling (`generate.rs:3746`, `:4059`) —
i.e. per verified *exec* fn's WP obligations. tgt is a proof/spec-heavy group
theory crate (3571 `spec`/`proof` fn decls); it has **9 exec fns total**, so
the crate-wide census denominator is 9, not 3116. The plan's "expected big
buckets — trait-method obligations, generics, closures, bv" live in
proof/spec fns and are **out of scope for stage A entirely** — they never
reach the serializer. Consequence: the **`bootstrap-fixture` family is the
real serializer stress corpus**; tgt's value here is (a) verdict-neutrality at
scale and (b) confirming the exec-fn construct gaps on real code.

| metric | value |
|---|---|
| verified / errors (flag ON, cold) | 3116 / **0** |
| verified / errors (flag OFF, cold) | 3116 / **0** (identical → **zero verdict delta at scale**) |
| cert-eligible fns (= exec fns) | **9** |
| certified | **1 / 9** (`runtime::impl_4::clone`) |
| wall-clock flag ON / OFF (cold) | 100s / 99.56s (**overhead ~0.4s, <0.5%** — emission touches 9/3116 fns) |

Ranked per-construct rejection buckets (tgt exec fns) — this IS the stage-B
roadmap for exec-fn certs:

| construct tag | fn count | fns |
|---|---|---|
| `call` (`StmX::Call`) | **5** | runtime::find_cancellation_exec, copy_word, apply_hom_gen, apply_hom_inv, apply_hom_symbol_exec |
| `assert-query` | **3** | todd_coxeter_rt::symbol_to_column_exec, inverse_column_exec; runtime::is_inverse_pair_exec |

**Roadmap read-out.** tgt exec-fn stage-A coverage is gated by exactly two
arms: `bootstrap-02b` (`StmData::Call`) clears the 5 `call` fns, and an
`assert-query` arm clears the remaining 3. Landing both takes tgt from **1/9
→ 9/9** exec-fn certs. No other construct blocks a tgt exec fn. Combined with
the fixture (whose entire gap is also `call`), **`StmData::Call` is the
single highest-leverage next serializer arm** across both corpora
(5 + 5 = 10 fns unlocked), with `assert-query` a distant second (3 fns).

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

**W2a correction (2026-07-14, §5.10):** a `bool`-returning spec fn lowers to
a NONCOMPUTABLE Lean `Prop`, so `decide` gets stuck on `Classical.choice`.
`goal_eq`/`goals_eq` therefore return `nat` (1 = equal, 0 = not) and the
bridge line is `goals_eq (refWp ctx sst) production = 1 := by decide`.

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

### 2.6 Call arm — the #128 ret-eq fork (opus-b02b, 2026-07-13; DECISION PENDING)

Picking up `bootstrap-02b` surfaced a mirror-shape defect: the N2.1-frozen
`StmData::Call { reqs, enss, dest, dest_typ }` + refWp's
`frame_after(Call) = FBind(dest, dest_typ, hyps_of_leaves(enss))` models ONLY
the naive ∀-path (`∀ dest, ens → …`). Production's `push_post_call_frames`
(`sst_to_lean.rs:3250`) has a `#128 ret-eq` optimization: when a callee's
ensures has a conjunct `r == E` (E ∌ r) it DROPS the `∀ ret` and emits
`[E_bound →] [rest →] let dest := E`. The fixture callee `double_exec`
(`ensures r == 2*x`) hits exactly this, so refWp cannot reproduce
`quad_exec`'s goals and the bridge won't close. Full analysis + option table
in board `bootstrap-02b`. Recommended resolution (local model concurs):

**"Lower the mirror" — `Call { reqs: Box<LeafList>, post: Box<FrameList> }`.**
The post-call frame becomes explicit EVIDENCE the serializer transcribes,
not intent refWp re-derives. refWp collapses to a pass-through:

```
wp_stm(f, Call{reqs, post})     = close_each(f, *reqs)          -- obligations
frame_after(f, Call{reqs, post}) = frame_append(f, *post)        -- append verbatim
stm_size(Call{reqs, post})       = 1 + leaf_len(*reqs) + frame_len(*post)
```

The serializer builds `post` by INDEPENDENTLY replicating the simple subset
of `push_post_call_frames` (ret-eq detect via `vir_find_ret_eq`, `E_bound`
via `type_bound_predicate`, the `coerce_lexpr` bridge), so both frame shapes
land in one uniform slot:
- ∀-path → `FBind(dest, ret_typ, [FHyp(ret_bound)] FHyp(ens))`
- ret-eq → `[FHyp(E_bound)] [FHyp(rest)] FLet(dest, E)`

The `decide` bridge then validates the serializer's replication against
production (non-circular — the serializer recomputes, does NOT copy). This
generalizes to the coming `&mut` post-state / prophecy frames instead of
perpetually growing refWp's Call arm.

**Note for the implementer:** this `{reqs, post: FrameList}` reshape is
IDENTICAL for the two leading options — Option 1 (serializer replicates
`post`) and Option 2 (provenance-capture `post` from the walk) differ ONLY in
how `post` is populated, not in the mirror/refWp shape. So the tactus-core
side is safe to build ahead of the Option 1-vs-2 call; only the serializer's
`post`-builder waits on it. (Option 1'—keep `enss/dest/dest_typ` + add a
ret-eq VARIANT—and Option 3—restrict to ∀-path, fail-loud on ret-eq—do NOT
share this reshape.) `frame_len` already exists (lib.rs:288). Add a
`ref_wp_call_*` in-crate `decide` proof over a hand-built `double_exec`-shaped
literal (one ret-eq, one ∀-path) before wiring the serializer.

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

**W3 triage (2026-07-14, from the tgt differential gate — board bootstrap-08,
`probe-w0/probe11_w3_tgt/`).** First bridge run over certs emitted from REAL
corpus code (tactus-group-theory), not the fixtures. Corpus is census-limited:
stage-A emission is exec-fn-only and tgt has 9 exec fns, of which **1** emits a
cert (`runtime::impl__4::clone`, a derived Copy-clone) and 8 are loud scope-
rejections (5 `StmData::Call` = bootstrap-02b; 3 `assert-query`) that emit no
cert and are NOT bridge subjects. So the gate has exactly one bridgeable subject
today. Reconfirmed the census buckets by targeted cold `--verify-module` emits
(runtime: 1 certified / 5 call / 1 assert-query; todd_coxeter_rt: 0 / 2 assert-
query). Verdict-neutral (`24 verified, 0 errors`, flag on cold).

- **runtime::impl__4::clone — RetBind-value ref-param deref (NEW site, class
  known).** `fn clone(self: &RuntimeSymbol)`. Bridge `goals_eq refWp production
  = 1` is FALSE. Pinpoint-proved (`Pinpoint.lean`) the SOLE divergence is the
  RetBind-value leaf: SST `RetLet(4, 0)` binds `_return := leaf 0 ⟦self⟧`;
  production binds `_return := leaf 5 ⟦self.deref⟧`. Patching only that leaf
  (`Let 4 5 → Let 4 0`) closes it. refWp is faithful (`ret_frame` folds the
  SST's `val` verbatim, lib.rs:777); production is correct; the SERIALIZER
  renders the `&`-param return-value binding as bare `self`, not applying the
  `*p → p.deref` subst at the RetBind-value render site (it IS applied at ens
  leaf 2 / oblig leaf 3 in the same fn — so the miss is site-specific). This is
  the reference-param sibling of head_exec/bootstrap-18 (obligation-leaf site);
  a NEW leaf-render site of the SAME class. DESIGN §2.5 leaf rendering not
  certified → sound honest-fail, not a refWp/production bug. **Batched onto
  bootstrap-18** (whose fix must now thread production's deref RenderCtx through
  BOTH the `oblig_leaf`/ens path AND the RetBind-value path). Together the two
  findings show the deref-subst gap is systemic across leaf-render sites.
- **No production bugs found; 0 unexplained divergences.** certified fraction
  1/9 (census-limited). Re-run when the Call + assert-query arms unlock the
  other 8 exec fns.

**W2b triage (2026-07-14, from the fixture-scale bridge run — board
bootstrap-07, `probe-w0/probe9_bridge/`):** running the bridge over ALL 11
fixture certs (not just the four hand-demoed in b15/16/17) found a SECOND
honest-fail beyond the known `max_u64` branch-in-leaf:

- **head_exec — ref-param deref leaf divergence (NEW).** Ensures
  `r == tree_head(*t)` on `t: &Tree`. The serializer's `oblig_leaf` (empty
  RenderCtx) renders `*t` as bare `t` → SST ens leaf `⟦…tree_head t⟧`;
  production's postcondition renders `t.deref` → goal leaf `⟦…tree_head t.deref⟧`.
  Pinpoint-proved the obligation leaf is the SOLE divergence (`goals_eq refWp
  (production with leaf6→leaf3) = 1`). Same source span, different leaf text.
  This is the reference-parameter sibling of finding-4's documented
  "empty-RenderCtx does not replicate a coercion/subst" caveat: a SERIALIZER
  faithfulness gap (not a refWp or production bug), and exactly the kind of
  divergence W3's differential gate is meant to catch — surfaced early here.
  Stage A does not certify leaf rendering (§2.5), so the bridge SOUNDLY does not
  close. Fix (make the serializer render the ensures with production's
  param-deref subst so head_exec bridges) spun out as its own board card. Both
  honest-fails are now permanent classified entries in the probe9 runner: a
  honest-fail that later CLOSES is treated as a regression.

**W2a resolution status (2026-07-14, from the on-disk fixture certs +
authoring refWp — see board bootstrap-06 writeup for full detail):**

1. Post-`If` continuation: **UNRESOLVED — no fixture exercises it.** In the
   fixtures a mid-`Seq` `If` never appears as an SST node: `max_u64`'s `if` is
   ABSORBED by the frontend into the returned-value rendering (leaf 7 =
   `x<y → (let r := let m := y; …)`) before the snapshot. refWp's stage-A
   choice (`frameAfter(If)=frame`, continuation sees the pre-if frame) is
   authored but untested. Needs a fixture with a real post-if continuation
   (feed W3). 
2. Fall-through postcondition: **the serializer emits an explicit `Ret(enss)`
   node** — all three fixtures end in `Ret`, so refWp walks the explicit Ret
   (no synthesis). CONFIRMED the `return_var` question is LIVE: `sum_to`
   production prepends `Let 39 7` (`let r := acc`) before the postcondition
   leaf — production DOES bind the return value as a frame let. So a
   `return_var` field (or serializer-baked let) IS needed for fall-through
   bodies (finding-4). refWp does not add it yet.
3. Loop-body post: **WALKER-SYNTHESISED, confirmed.** Init/maintain/decrease
   invariant obligations are NOT distinct SST Assert nodes; refWp synthesises
   init+maintain from `Loop.invs` identically. (User asserts inside the body
   ARE real SST Assert nodes.)
4. Overflow-guard asserts: **SST `Assert` nodes, serialized post-injection,
   confirmed.** refWp just folds them (add_capped Assert 8/13; sum_to Assert
   13/15). No injection mirror needed.
5. W5 leaf semantics: valuation-parametric SstSem vs. deep-exprs-first —
   see §4; decide at W5a kickoff. (Untouched by W2a.)
6. Mutual/SCC exec fns and non-default loop flavors
   (`invariant_except_break`, `no_unwind` interplay): stage-A exclusions —
   confirm the serializer rejects them loudly rather than mis-capturing.
   (Untouched by W2a.)

**Newly surfaced by W2a (drive bootstrap-15 / W2b):**

7. **Obligation-annotation gap (dominant):** production renders every
   obligation leaf with a `/- @rust:file:line -/` annotation (a distinct
   interned leaf); the SST carries the BARE prop leaf (add_capped `Assert 8` →
   goal `Leaf 15`; sum_to inv `10` → `Leaf 17`). Under strict `goals_eq` NO
   fixture bridge closes today. The serializer must carry the annotated
   obligation leaf (Assert then needs a bare hyp-leaf AND an annotated
   obligation-leaf).
8. **Hyp-name gap:** bound-hyps/requires render as NAMED `∀`-binders
   (`All 19 2` = `∀ (h_x_bound : …)`), not arrows; FnCtxData carries only the
   prop leaf. N2.1-round-2: `ParamBoundList::Bound(name, prop)`, `reqs` as a
   `BinderList`; then refWp's signature hyps switch `FHyp`→`FBind`.
9. **Loop-binder gap:** SST `Loop.binders = Nil` (N3a `modified_vars = None`);
   production quantifies the maintain/use telescope over the loop-modified
   locals + bound hyps + invs-as-hyps + cond + a `_tactus_d_old` let. Serializer
   must populate `Loop.binders` + a decreases leaf.
10. **Backend: `bool` spec fns → noncomputable `Prop`** → `decide` stuck on
    `Classical.choice`. `goal_eq`/`goals_eq` return `nat` (1/0); the bridge
    line is `goals_eq (refWp …) production = 1 := by decide`, superseding
    §2.3's `= true`. Also: nested `match a {…match b…}` emits ambiguously
    ("redundant alternative"); match the first arg alone + read the second via
    projection accessors.

## 6. Sequencing

N2.1 (amendments) → N3a/b/c (serializer, per its spec) → N4 (census) →
W2 (refWp: worker + equations session, then bridge + mutations session) →
W3 (tgt gate + triage). Each brick ends with the battery green and this doc's
open-question ledger updated.
