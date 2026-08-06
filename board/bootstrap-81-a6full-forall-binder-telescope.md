# bootstrap-81 — A6-full: the ∀-binder telescope arm (kills the `assert-forall` tag)

Status: **DESIGN FROZEN 2026-08-06 — step-0 evidence frozen (§
"Step-0 evidence"); all 3 open questions resolved by Danielle's
standing principles (§ "Open questions" below). Era 1 (D1+D2
model-only, byte-stability era) IN PROGRESS.**
Implements endgame table row 11b (DESIGN-bootstrap-endgame.md §8):
retire the `assert-forall` census tag — b68 scaffolding, never
permanent — by modeling `assert forall … by { … }` skolem binders in
the stage-A telescope. Unblocked post-flip per Q4. **This is the LAST
named coverage arm; after it lands, every census tag is an
unmodelable-construct tag (rawvir-*/call-trait/etc.), not a
modeled-but-unmirrored one.**

Subjects: `runtime.lemma_runtime_word_view_subrange` and
`runtime.lemma_runtime_word_view_append` (tactus-group-theory; the
WHOLE `assert-forall` census population, exactly 2). Fixture: **no
assert-forall subject exists today** (`grep -c "assert forall"
bootstrap-fixture/lib.rs` = 0) — the arm adds one (§ "Fixture
subject"), same precedent as b79's break-form subject gap.

## Background (what A6-short did, and what it deferred)

b76 (A6-short, 2026-07-24) made the serializer's `StmX::DeadEnd` arm
run production's OWN skolem detection
(`sst_to_lean::collect_assert_by_vars_in` — shared single-source,
`sst_serialize.rs:3349`) and census-reject `assert-forall`: a DeadEnd
scope referencing any `LocalDeclKind::AssertByVar` local means
production ∀-binds those skolems in the scope's goal telescopes
(`Wp::Scope.scope_vars`), which stage A could not express. The deferral
note is on the `assert_by_var_typs` field doc
(`sst_serialize.rs:680-686`) and in endgame §3/A6: "The real fix (the
`∀ (k : Int)` stage-A telescope binder arm) stays planned post-flip
work — row 11b. **Acceptance (full, 11b):** the tag population drops
to 0 and the binder frame enters the D in-model column."

## Step-0 evidence (frozen 2026-08-06, from the live probe11 out-tree)

Sources:
`probe-w0/probe11_w3_tgt/out/lib/runtime__lemma_runtime_word_view_subrange.lean`
(production emission, 281 lines, 4 goals) and the sibling
`..._append.lean` (386 lines; same shapes plus an if inside the
by-block). tgt src: `tactus-group-theory/src/runtime.rs:506-537`.

### E1 — the SST lowering (vir/ast_to_sst.rs ~2248-2290)

`assert forall|k: int| G implies P by { proof }` lowers to:

```
deadend {
  assume(has_typ(k, int))     // one per binder var — see E3
  <require checks>
  assume(G)                   // the guard, ordinary Assume
  <proof stms>                // the by-block
  assert(P)                   // the real obligation
}
assume(∀ k. G ⟹ P)            // fact re-enters the main flow
```

plus fn-wide `LocalDeclKind::AssertByVar` locals for the binder vars
(the skolems have NO `Wp::Let` — declared fn-wide, scoped
syntactically to the by-block).

### E2 — production ∀-binds the skolems on every in-scope goal

`build_wp`'s DeadEnd arm (`sst_to_lean.rs:6856-6861`) emits
`Wp::Scope { scope_vars, body, after }`; the walker
(`sst_to_lean.rs:3067-3090`) pushes each scope var via
`push_mod_var_frames` — a `CtxFrame::Binder` +, iff
`type_bound_predicate` is `Some`, a bound `CtxFrame::Hyp` — then
walks the body under that obl; `after` walks under the ORIGINAL obl.
So every theorem emitted inside the DeadEnd body carries the binder
in its telescope. Evidence, subrange goal 2 (the by-block's inner
assert, `_534_16_2`):

```
(w) (lo) (hi) (h_req0 : …) :            -- theorem binders (fn preamble)
  let lhs := …; let rhs := …;
  let tmp__1 := (len lhs = len rhs);
  tmp__1 → tmp__1 →                     -- the prior assert, in as hyp
  (∀ (k : Int),                         -- ★ the skolem, ∀-bound
   True →                               -- ★ see E3
   (let tmp__ := 0; … 0 ≤ k ∧ k < len lhs) →   -- the guard G, ordinary Assume
   (let tmp__2 := (index (subrange w lo hi) k = index w (lo+k));
    tmp__2))                            -- the by-block assert leaf
```

Goal 3 (`_533_54_3`, the assert-forall statement's own P) has the
same prefix with the by-block's assert fact additionally in as hyps
(`tmp__2 → tmp__2 → index lhs k = index rhs k`). The postcondition
goal 4 carries the trailing `assume(∀ k. G ⟹ P)` as an ordinary
`Forall` leaf hyp. **The binder appears MID-PROPOSITION** (after
goal-position lets), i.e. past the leading-prefix latch — wrap-mode
rendering, anonymous hyps, `∀ (k : Int), …` inline in the goal body.

### E3 — the `True →` is NOT a binder bound-hyp; it's an ordinary Assume

`type_bound_predicate` returns `None` for `IntRange::Int`
(`to_lean_sst_expr.rs`, the `Nat | Int => None` arm), so
`push_mod_var_frames` pushes NO bound hyp for `k : Int`. The `True →`
in E2 is the `assume(has_typ(k, int))` from the SST lowering
(`has_typ(int) = True`) — an ordinary `StmX::Assume` in the block,
already mirrored by the serializer's existing Assume arm. **The only
unmodeled content is the ∀-binder frame itself** (plus, for
bounded-typ skolems, its type-bound hyp — `ParamBoundList` covers it;
NoBound for the two subjects).

### E4 — the `already_bound` dedup

The Scope walker filters scope vars whose names an ENCLOSING scope
already bound as a `CtxFrame::Binder` (nested assert-forall proof
bodies legally reference outer skolems; rebinding would shadow the
hypothesis-carrying binder — `sst_to_lean.rs:3073-3086`, variant doc
6068-6073). The two subjects have a single flat scope each (never
fires), but the mirror must reproduce it: the filter set is exactly
the names pushed as ∀-binders on the current walk path (enclosing
DeadEnd scopes + loop mod-var binders; closure params are
census-rejected upstream).

### E5 — the mirror vocabulary already has every piece

- `FrameList::FBind(id, typ_leaf, tail)` → `GoalData::All` in `close`
  / `close_e_wrap` / `close_e_wrap_lead` / `close_e_tel` — including
  the mid-proposition wrap rendering E2 needs (A1/b70-71's ∀-path
  closes exercised this).
- `BinderList` + `ParamBoundList` slots + `mod_var_frames(binders,
  bounds)` (FBind + optional named bound FHyp per entry) — the loop
  mod-var telescope's exact shape, reusable unchanged.
- Semantic layer: `holds` reads `GoalData::All(x, _ty, t)` as
  `forall|n: int| holds(t, upd(st, x, n))` (abstract-binder reading,
  S3-pre) — the W5 model already has the binder's denotation.
- Serializer helpers: `binder_id`, `typ_leaf`, `next_hyp_name`,
  `binder_list`, `param_bound_list` — the Loop arm
  (`sst_serialize.rs:4150-4176`) is the line-by-line template.

## Design (proposed; freeze after review)

### D1 — vocabulary: `StmData::DeadEnd` gains binder slots (1 → 3 fields)

```
DeadEnd(scope_binders: BinderList, scope_bounds: ParamBoundList, Box<StmData>)
```

Precedent: b79's Loop 16→21. Non-scope DeadEnds (ordinary
`assert(P) by { … }` proof blocks — the common case) carry
`Nil`/`Nil`: `mod_var_frames(Nil, Nil) = FNil`, so `frame_append(f,
FNil) = f` and **every existing cert/bridge is byte-stable by
construction** (verify: probe9 33/33 + gate 291/0 with zero goal-text
drift before any subject cert emits).

### D2 — refWp: one arm edit, reusing `mod_var_frames`

```
wp_stm(pp, f, DeadEnd(bs, bds, b)) =
    wp_stm(pp, frame_append(f, mod_var_frames(bs, bds)), *b)
```

`frame_after` stays `=> f` (facts discarded — the trailing
`assume(∀…)` lives in the continuation's tree, already handled).
`exec_safe_f`'s DeadEnd arm threads the same extended frame
(`close_sem_e` already interprets FBind→∀; `holds` already reads All
— E5). Expected W5 churn, b74-architecture precedent (S3-pre needed
zero `wp_stm_sound` arm changes when the frame construction changed):
the DeadEnd unfold pins (`lib.rs:5235`, `:6390`) restate, the
soundness arm delegates to the body IH as today. **Impl-time
verification:** if `wp_stm_sound`'s DeadEnd arm does NOT absorb the
change by unfolding alone, stop and re-card the soundness delta
rather than growing a local workaround.

### D3 — serializer DeadEnd arm (replaces the `Err("assert-forall")`)

At `sst_serialize.rs:3342-3357`: keep the existing
`collect_assert_by_vars_in` call (same detection, now constructive),
then mirror `sst_to_lean.rs:3073-3090` exactly:

1. **Dedup filter (E4):** drop vars whose `LeanName` is already in a
   new walk-path set `forall_bound_names` — seeded/extended at the
   Loop arm's mod-var binder push and at this arm's own push,
   saved/restored at branch/scope boundaries (production's
   `obl.clone()` per path; sibling-branch names must not leak into
   the filter). Separate set from `bound_names`: production's
   `already_bound` counts ONLY `CtxFrame::Binder`, not lets/hyps.
2. **Transcribe (Loop-arm template, `:4150-4176`):** per surviving
   var — `binder_id(vid)`, `typ_leaf(&typ)`; bound entry =
   `type_bound_predicate(&LExpr::var(name), &typ)` → `Some((hname,
   prop))` via `next_hyp_name()` + leaf intern, else `None`
   (NoBound). Names claim the SOURCE names (production never freshens
   scope binders); insert into `bound_names` so a LATER shadowing let
   freshens under the existing hoist-mixed-shadow discipline.
3. Emit `DeadEnd(binder_list(entries), param_bound_list(bounds),
   body)`.

No emission-counter changes: Int skolems consume no hyp names
(NoBound); bounded-typ skolems consume one `_h_hoist_i` per bound —
same order as production's telescope (binder-bound pairs precede the
body walk's frames). **Impl-time verification (named, not
speculative):** if a scope-binder FHyp ever lands in a goal's
LEADING prefix (DeadEnd as a fn's first stm), check the assigned
`_h_hoist_k` ordinal against production's per-goal counter on a
fixture variant before accepting; the two subjects never hit this
(mid-proposition, past the latch).

### D4 — census + reporting

- The `Err("assert-forall")` rejection and the tag are DELETED (not
  kept at population 0 — the construct is now modeled; a tag that can
  never fire is scaffolding). Census-report sites, the gate-note tag
  list, and probe11's documented-absences entry updated in the same
  commit.
- The D in-model tripwire column (bootstrap_coverage.rs) gains the
  DeadEnd-binder frame row — endgame acceptance: "the binder frame
  enters the D in-model column."

### D5 — fixture subject (new)

One minimal assert-forall fn in `bootstrap-fixture/lib.rs`, mirroring
the tgt shape: a proof fn over `Seq<u64>` with a plain assert before
an `assert forall|k: int| 0 <= k < s.len() implies P(k) by { … }`
(a second variant with a bounded `k: u64` skolem exercises the
`Bound` entry + leading-prefix check in D3). Golden re-vendor +
probe9 census bump in the same commit.

### D6 — probes + mutation kills

- **probe11:** the 2 subjects' certs RETURN — the subject-population
  pin fires SUBJECT-RETURNED, forcing reclassification (by design;
  the b78 S5 lesson: stale-on-disk certs mask regressions). Expected:
  both CLOSE → probe11 13/13, zero honest-fails maintained.
- **probe13:** new kill classes on the fixture subject (each baseline
  =1, kill =0): `scope_binder_drop` (drop the FBind — unbridgeable),
  `scope_bound_drop` (bounded variant: drop the bound FHyp),
  `scope_binder_typ_flip` (TyInt↔TyNat).
- **probe37:** new DeadEnd arity → the hand-rolled datatype matches
  need arms (sorryAx audit catches misses — by design); probe13
  gen.py cert-literal splitters need the layout update (standing
  gotcha: every vocab change touches both).
- **probe9:** 34/34 with the new fixture subject.

### D7 — battery + acceptance

Done-when (all):
1. `assert-forall` tag population 0 — tag and rejection deleted (D4).
2. probe11 13/13 CLOSE incl. both word_view subjects, fresh regen
   (scoped per-module emits, NO tgt gate — standing constraint).
3. probe9 34/34 (new fixture subject closes); probes
   13(+3 classes)/14/17/37/38 green; units green.
4. tactus-core gate 291/0 + package gate + Link discharge 198/0 with
   zero goal-text drift on all pre-existing subjects (D1 byte-stable
   check), e2e 829/2, golden byte-stable modulo the intended fixture
   addition.
5. `wp_stm_sound`/`ref_wp_sound` still verify with the DeadEnd arm
   threaded (D2) — axiom closures unchanged (⊆ [propext,
   Classical.choice, Quot.sound]).

## Churn checklist (impl-time, in order)

1. tactus-core `lib.rs`: DeadEnd slots + `stm_size`/`diverges`/
   `frame_after`/`wp_stm`/`exec_safe_f` arms + unfold pins
   (`:3008`, `:3077`, `:3166`, `:4461`, `:5235`, `:6390`) + decoder
   census arm (`:6199-6260`) + coverage column. ONE cache-churning
   edit (b79 discipline).
2. Serializer arm (D3) + `forall_bound_names` threading + census/tag
   deletion.
3. Fixture subject + golden re-vendor + probe9.
4. probe11 regen (two scoped emits, ~80s each, no `-V cache`) +
   subject-pin reclassification.
5. probe13 classes + probe37/probe13 layout updates.
6. Full battery (D7) → commit sequence: model / serializer /
   fixture+probes, battery green at each.

## Open questions for Danielle — RESOLVED 2026-08-06 (Danielle: rule by
the standing principles — right-way/cleaner, trusted-surface shrink,
Lean-idiomatic, transparency, predictability-over-special-cases)

1. **Tag deletion vs 0-population tripwire (D4) — RESOLVED: DELETE.**
   A census tag is a silencing channel: it converts an unbridged fn
   from a hard error into an accepted exclusion. A tag that "can't
   fire" only decides what happens if it ever DOES fire (a
   serialization regression on an assert-forall fn) — and kept, the
   answer is "inventoried quietly"; deleted, it's unclassified drift =
   O7 hard error post-flip. Strictly louder (principle 2; the b78 S5
   masking lesson; the endgame text itself calls the tag b68
   scaffolding, never permanent).
2. **Fixture subject shape (D5) — RESOLVED: two proof-fn subjects
   (Int NoBound + u64 Bound), NO exec subject.** The vocabulary delta
   has exactly two shapes. tgt's corpus has only Int skolems and
   exec-vs-proof mode doesn't interact with the DeadEnd arm, so exec
   composition coverage without corpus evidence is speculative
   generality (principle 5) — but the Bound path must be BOTH
   implemented and tested, since an Int-only arm would be exactly the
   special case principle 5 forbids.
3. **Staging (D7) — RESOLVED: b80 two-era pattern.** Era 1 = D1+D2
   model-only (serializer still rejects; Nil/Nil everywhere) with the
   byte-stability pins as the drift proof; era 2 = D3 serializer arm +
   D5/D6 fixture/probes. Cheap, bisectable, and byte-stability is the
   validation the architecture already provides (principle 1).
