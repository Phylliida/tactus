# bootstrap-82 — F1: prelude hygiene (definitionalize `Tactus.index` / `Tactus.hasResolved` / `Tactus.heightLt`)

Status: **IMPLEMENTATION 2026-08-06 — D1–D5a landed (prelude
redeclarations + base-list shrink + sanity extractor `opaque` support),
units 437+7/0 green; battery in progress.** Implements endgame table
row 13,
first of the three milestone-F bricks (DESIGN-bootstrap-endgame.md §7;
spec = closure-doc §4 item 2, DESIGN-axiom-closure-check.md:174-189;
program-table row 8, DESIGN-bootstrap.md:106). Target end state: the
`arch_word_bits` pair is the ONLY tactus prelude axiom. Independent of
the B soak (touches the prelude declaration kinds + the closure-check
base list, NOT the bridge or serializer). Out of scope: closure-doc §4
items 1 (sanity.rs always-on) and 3 (CI grep) — separate small bricks;
vstd-as-package and dual-backend differential are milestone-F siblings,
not this card.

## Step-0 evidence (frozen 2026-08-06)

### E1 — the prelude is exactly 5 axioms, 3 of them hygiene targets

`source/lean_verify/TactusDefs.lean`:

```
60:  axiom arch_word_bits : Nat
61:  axiom arch_word_bits_valid : arch_word_bits = 32 ∨ arch_word_bits = 64
232: axiom Tactus.heightLt {α : Type u} {β : Type v} (a : α) (b : β) : Prop
250: axiom Tactus.index {α : Type u} [Nonempty α] {n : Nat} (a : Vector α n) (i : Int) : α
261: axiom Tactus.hasResolved {α : Type u} (a : α) : Prop
```

The closure-check base list hardcodes all 5 + ofReduceBool/trustCompiler
(TactusDefs.lean:283-287). The prelude is content-addressed
(`prelude.rs:108-115`): editing TactusDefs.lean → fresh `prelude-<hash>`
dir → clean rebuild by construction; no cache management.

### E2 — usage census: who emits each symbol, who consumes it

**`Tactus.heightLt`** — the SST cert path NEVER emits it
(`to_lean_sst_expr.rs:1148-1180`: int operands → direct `<`; same
datatype → `T.height` compare; anything else → hard error). The only
emitter is the VIR-AST cross-crate renderer (`expr_shared.rs:490`),
surfacing in vstd broadcast axioms: `axiom_seq_index_decreases`,
`axiom_seq_subrange_decreases` (vstd/seq.rs),
`axiom_vec_index_decreases`, `axiom_vec_decreases_to_view`
(vstd/std_specs/vec.rs). **Companion audit result: ZERO.** No
`WellFounded Tactus.heightLt` anywhere (grep over source/); nothing
assumes anything *about* the relation — vstd axioms only assert
specific instances *of* it as hypotheses.

**`Tactus.index`** — the SST exec Index arm does NOT use it
(`to_lean_sst_expr.rs:1183-1214` renders `xs[i.toNat]!` via GetElem).
The only emitters are VIR-AST-side (`expr_shared.rs:497`,
`BinaryOp::Index → "Tactus.index"`): spec-mode array indexing in
cross-crate emission, notably vstd's `array_view` body
(`Seq.new (fun i => Tactus.index a i)`, vstd/array.rs). Consumers:
vstd axioms `lemma_array_index`, array_view roundtrips,
`axiom_array_has_resolved`. The `[Nonempty α]` bracket is the N2 fix
(DESIGN-nonempty-axioms.md; `test_soundness_hole_prelude` pin) — must
survive any redeclaration.

**`Tactus.hasResolved`** — one SST emitter: the nested-HasResolved arm
(`to_lean_sst_expr.rs:1121-1126`; top-level synthetic
`Assume(HasResolved(_))` is dropped upstream by
`is_synthetic_assume_to_drop`). Consumers: vstd
`axiom_vec_has_resolved` / `axiom_array_has_resolved`, which carry it
purely as hypothesis. Nothing ever needs to *prove* it.

### E3 — corpus census: the three symbols are absent from the in-gate corpus

`grep -c` over `tactus-core/out/` for all three names: **0** (they
appear only inside the vendored `TactusDefs_lib*.lean` copies, 4
occurrences each = 3 decls + closure-check base list). Fixture out:
same, vendored copies only. So no in-gate bridge subject exercises any
of the three; the live exercisers are vstd boundary axioms (tactus.rs
e2e tests reference `axiom_seq_index_decreases` et al.; probe11's tgt
lane; probe-w0/fcx_island_reference.lean).

### E4 — soundness shape of the change (the "why it's safe" argument)

Each redeclaration is **model-narrowing**: the old axiom's model class
strictly contains the new declaration's single model.

- `Tactus.index` axiom = "some total function Vector α n → Int → α";
  the def picks one member (in-range = the real element, out-of-range =
  `Classical.arbitrary α`). Every fact vstd asserts about it stays
  well-typed and stays true in more models than... no — stays
  *consistent*: the def realizes one model of the axiom, so any
  theory consistent under the axiom with that model is unchanged; the
  def cannot introduce inconsistency (it's a plain definition, kernel-
  checked, no `choice` beyond `Classical.arbitrary` which is already
  in the allowed base via `Classical.choice`).
- `hasResolved` / `heightLt` as `opaque`: an opaque constant is a
  definition whose (fixed, inhabited) witness the elaborator cannot
  unfold; it introduces NO axiom. The everywhere-True interpretation
  validates every vstd instance assertion, so the axiom's model class
  is non-empty and the opaque witness picks one member. Nothing
  assumes falsity of any instance, so no previously-consistent theory
  becomes inconsistent.

Net effect on `#print axioms` closures: the three names simply stop
appearing (defs/opaques aren't axioms). The closure-check base list
loses them — the machine-checked shrink IS the deliverable.

## Subject matrix (behavior dimensions, per retrospective change 1)

Dimensions: {declaration} × {emission path} × {consumer class}.

| # | Declaration | Emission path | Consumer | Risk to check |
|---|---|---|---|---|
| S1 | index→def | VIR-AST spec array index (`array_view`) | vstd array axioms | def vs axiom typing; `[Nonempty α]` retained |
| S2 | index→def | (none on SST cert path) | tactus-core/fixture corpora | zero occurrences (E3) — nothing to drift |
| S3 | hasResolved→opaque | SST nested arm (`to_lean_sst_expr.rs:1121`) | goals mentioning vstd ensures w/ has_resolved | opaque elaboration: `Nonempty Prop` instance resolution under universe binders |
| S4 | hasResolved→opaque | VIR-AST | vstd vec/array has_resolved axioms | hypothesis-position only — nothing proves it |
| S5 | heightLt→opaque | VIR-AST only | vstd seq/vec decreases axioms | two type params, two universes — opaque binder handling |
| S6 | all three | closure-check base list | `#tactus_check_axioms` users | base list edit = the shrink; any stale `expected` entry naming them would now be inert (subset check, not equality — safe) |

Population note: S2/S6 are verifiable TODAY (grep = 0; subset-check
semantics documented at TactusDefs.lean:276-277). S1/S4/S5's live
exercisers are the e2e tactus.rs tests + probe11's tgt lane.

## Design (D1–D5)

- **D1 — `Tactus.index` → def.** Replace the axiom with:

  ```lean
  noncomputable def Tactus.index {α : Type u} [Nonempty α] {n : Nat} (a : Vector α n) (i : Int) : α :=
    if h : 0 ≤ i ∧ i.toNat < n then a[i.toNat]'h.2 else Classical.choice inferInstance
  ```

  (`noncomputable` required: `Classical.choice` isn't code-generable;
  the fallback primitive is `Classical.choice inferInstance` — core
  v4.25.0 has no `Classical.arbitrary`, that's Mathlib.)
  Keeps the N2 bracket (the soundness-hole pin stays green), keeps the
  exact signature (S1 consumers unchanged). Faithful in-range
  condition (`0 ≤ i ∧ …`) per predictability: negative `i` is
  out-of-range, not silently element 0. Out-of-range = choice over the
  `Nonempty` instance: still unspecified, matching Verus's
  total-but-unconstrained spec indexing.
- **D2 — `Tactus.hasResolved` → opaque.** `opaque Tactus.hasResolved
  {α : Type u} (a : α) : Prop`. No explicit witness (most
  conservative: unspecified-but-fixed). If `Nonempty Prop` resolution
  fails under the universe-binder form, fallback = keep the axiom for
  this symbol only and say why (NOT `:= True` — that commits to an
  interpretation the comments explicitly reject; see Q2).
- **D3 — `Tactus.heightLt` → opaque.** `opaque Tactus.heightLt
  {α : Type u} {β : Type v} (a : α) (b : β) : Prop`. The companion
  audit (E2) found nothing to preserve — no WF assumption, no
  companion facts; the relation's whole content is vstd's per-instance
  assertions, which an opaque witness accommodates.
- **D4 — closure-check base list shrinks** (TactusDefs.lean:283-287):
  drop `` `Tactus.heightLt, `Tactus.index, `Tactus.hasResolved ``. Base
  becomes classical core + `arch_word_bits` pair + ofReduceBool/
  trustCompiler — the endgame's target end state. Update the comment
  block above the command (263-277) to match.
- **D5 — pin audit + battery.** Check `tests/sanity.rs:217`'s
  prelude-name extractor against the new declaration kinds (it parses
  TactusDefs.lean; confirm it's name-based, not kind-based — if
  kind-based, extend). Then: units, fixture certs + golden,
  tactus-core gate + pkg + discharge + bridge, probes
  9/11/13/14/17/37/38 (probe11 regen = the two scoped cold emits —
  prelude hash changed; probe37's axiom audit is the shrink's
  machine-checked witness — its expected lists must now show the
  reduced closure), e2e (tactus.rs vstd-axiom consumers).

## Risks

- **R0 (SURFACED, fixed same-day): cold-prelude rebuild races across
  verifier threads.** First gate run after the prelude-text bump went
  230-fns red with "failed to create file 'TactusDefs.olean'". Root
  cause: `build_module`'s build dir is pid-unique but the gate's ~64
  verifier threads share ONE pid; with the new `prelude-<hash>` dir
  absent, the whole first wave saw not-fresh and entered
  `build_module` concurrently in the SAME `build-<pid>-TactusDefs`
  dir, and the first finisher's `remove_dir_all(build)` deleted the
  cwd of the others' still-running `lean`. Latent since the pid-unique
  build dir; never bitten because prelude-text bumps are rare (last
  was N2, 2026-07-03) and every other rebuild trigger leaves the
  prelude hash alone. Fix: process-wide `REBUILD_LOCK` Mutex in
  `ensure_prelude_olean` + freshness re-check under the lock
  (cross-process builders need no lock — distinct pids, identical
  content). Validated by the cold-prelude gate rerun below.

- **R1 (S3/S5): `opaque` elaboration — DE-RISKED pre-card (2026-08-06,
  scratch probe on the pinned v4.25.0 toolchain).** All three
  redeclarations elaborate: both `opaque` forms (incl. the two-type-
  param/two-universe heightLt) resolve `Nonempty Prop` fine and carry
  ZERO axioms (`#print axioms`: "does not depend on any axioms"); the
  index def needs `noncomputable` (Classical.choice isn't code-
  generable) and a theorem through it rests on `[propext,
  Classical.choice]` only — the allowed classical core. Vstd-style
  consumer axioms over all three re-elaborate unchanged.
- **R2 (S1): kernel-visible reduction changes automation.** As a def,
  `Tactus.index` can now unfold under kernel reduction (`decide`,
  `whnf`). Direction is strictly more-provability; the bridge compares
  goal TEXT (the head symbol is unchanged — `Tactus.index a i` renders
  identically), so no goal drift. tactus-core corpus has zero
  occurrences (E3), so no in-gate closure changes. e2e tactus.rs
  exercises the vstd consumers.
- **R3: probe staleness.** Prelude hash change invalidates probe11's
  vendored tgt out-tree → regen (two scoped cold emits, ~80s each —
  the accepted lighter path, not a tgt gate). Probe runners glob the
  prelude dir by design.
- **R4: golden/vendor churn** — fixture certs re-emit (TactusDefs
  vendored copies change) → re-vendor golden. Byte-drift expected and
  explainable (declaration kinds + base list).

## Done-when

1. D1–D4 landed; `grep -c "^axiom" TactusDefs.lean` = 2
   (`arch_word_bits` pair only).
2. `test_soundness_hole_prelude` (N2 pin) still green.
3. Full battery green: units, gate 298/0 + pkg 54 + discharge 205/0 +
   bridge 172/172, probes 9/11(regen)/13/14/17/37/38, golden
   re-vendored, e2e 829/2.
4. probe37's axiom audit shows the reduced closure (the shrink is
   machine-checked, not just asserted).
5. **Skeptic review round after landing** (retrospective change 4 —
   in Done-when): specifically hunting (a) any consumer that silently
   relied on axiom opacity/unknowability in a direction the
   model-narrowing argument missed, (b) opaque-vs-axiom elaboration
   differences in the vstd boundary files, (c) `expected`-list entries
   anywhere naming the three symbols (now inert — confirm harmless).

## Open questions for Danielle

- **Q1 — scope: all three in one brick, or index first?** The endgame
  wording is "definitionalize index/hasResolved, AUDIT heightLt
  companions". The audit (E2) found zero companions, so D3 reaches the
  stated end state (arch pair only) in this brick. Recommend: all
  three; the audit IS the heightLt deliverable and it came back empty.
- **Q2 — the `:= True` fallback ban.** If opaque elaboration fails
  (R1), the fallback is keeping that symbol an axiom, not giving the
  opaque an explicit `True` witness: an explicit witness commits to
  the everywhere-True interpretation, which is *a* model of the axiom
  but contradicts the documented intent ("no assumption that it holds
  or fails"). Confirm the conservative ordering.
- **Q3 — `arch_word_bits` itself.** Out of scope here (honest platform
  assumption, closure-doc §4: "the one pair that's honestly an
  axiom"), but noting for the record: nothing in this brick makes it
  definitionalizable. Agreed to leave as the standing single axiom
  pair?
