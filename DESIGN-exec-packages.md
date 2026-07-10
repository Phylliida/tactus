# DESIGN: M6 — Exec Packages

*Drafted 2026-07-10, evening of the island-cache + symbol-investigation
arcs. Status: SPEC, unimplemented. Co-design gates marked ⚑.*

## Why M6 (three problems, one structure)

1. **Helper-tactic shape coupling (dragon B, `63005a2`).** Islands
   inline helper proof-fn theorems, re-elaborating their user tactics
   against whatever spec-fn render is in scope. Renders differ by
   world (vir `match` vs simplified `if .isVariant`), so tactics are
   not portable, and both authoring worlds are pinned in the wild
   (test_crate_defs_proof_exec_mix vs tgt's migrated exec tactics).
   Statements don't carry tactics — stmt-style helper imports
   dissolve the coupling *by construction*.
2. **Island fatness.** Every exec island inlines its whole dep world
   (~19s elaboration each on tgt). The `.verified` cache (island-cache
   arc) hides this on warm runs; cold runs and every text-touching
   edit still pay it. Packages amortize the world into defs oleans.
3. **Exec fns are outside the Link gate.** Proof fns' closed forms are
   composed and axiom-closure-checked every run; exec obligations are
   not. M6 puts exec obligations into the Link closure — a soundness
   upgrade, not just a speed one. (The island sorry-gate from
   `19cb850` covers the worst gap today, but Link-level composition is
   the real story.)

Also retired by M6: the dead-weight duplicate defs family (the exec
scope's narrow-rung builds are consumer-filtered at generate.rs's
`covers_exec` gate — pure waste, measured as the "double defs family"
finding).

## The trust seam (the load-bearing design issue)

Today, inlining = re-proving: an island that contains
`lemma_rate_pos` re-elaborates its proof against the render in scope.
No cross-render trust is ever needed.

Under M6, an exec pkg module would import the helper as a STATEMENT
(hypothesis binder typed by a stmt def), whose proof happened in the
PROOF world against vir-rendered spec fns. The exec obligation world
renders the same spec fns from the SIMPLIFIED krate. Same Verus
definitions, two Lean renders — **semantically equal, but Lean does
not know it.** Binding the vir-proven fact against the
simplified-rendered name is a new trust seam that re-proving never
had.

Options:

- **(i) Accept the seam as an axiom-class bridge.** Rejected:
  fails the transparency bar; grows the TCB for convenience.
- **(ii) Unify the renders.** Make the defs module render spec-fn
  bodies ONE way for both worlds (vir-style `match` is the natural
  candidate — it's what tactics like `cases s <;> simp only [rate]`
  want, and accessors remain available for exec OBLIGATION bodies,
  which are emitter-generated and shape-flexible). Existing
  simplified-authored tactics (tgt's migrated exec fns) would need
  re-touching. ⚑ Gate: Danielle's appetite for a one-time tactic
  migration pass (the 10s scratch loop makes this tractable; the
  population is currently ~9 fns).
- **(iii) Generated bridge lemmas.** For each spec fn with two
  renders, emit `theorem rate_bridge : vir_rate = simpl_rate := by
  cases ... <;> rfl` (mechanically generatable, kernel-checked).
  Closes the seam soundly without touching user tactics, at the cost
  of a generated-lemma population and name-doubling in the defs.
  Viable as a TRANSITION device under (ii), or a fallback if (ii)'s
  migration is unwanted.

**Recommendation: (ii) as the destination, (iii) only if migration
friction demands it.** Render unification also collapses the two defs
families into one (proof and exec worlds import the same spec-world
module; only accessors/obligation machinery differ), which is the
full resolution of the double-defs cost.

## Prerequisites (must land first)

- **M6.0 — Nonempty/Inhabited currency unification (dragon A).**
  Accessors take `[Nonempty V]` + `Classical.ofNonempty` (already
  noncomputable); `compute_nonempty_needs` gains a seed: body uses a
  field projection whose type involves a type param ⇒ Nonempty need
  (flows to instance `ne_bounds` via existing machinery). Without
  this, full-roots defs elaboration dies on vstd's Option DeepView
  instance (base:168) and exec packages have no defs to import.
  Blast radius: every island text changes (one-time global
  re-elaboration; the `.verified` cache absorbs it after one run).
  The design comment at PreambleConfig ("accessors for types with
  non-Inhabited fields break elaboration even when unused") is
  precisely what this lifts.
- **M6.0b — remaining full-roots breakage census.** Behind Inhabited
  sits at least the Tactus.Ref closure-ABI corner (bare-arrow Fn
  instances, builtinSpecFun — seen in the M5e cold logs). Run the
  ladder's attempt-0 on tgt after M6.0 and taxonomize what still
  fails. If closures remain broken: iterative-repair build (drop only
  the erroring item by line attribution — the CRATEDEFS follow-up)
  keeps defs coverage maximal without blocking on a full ABI fix.

## Architecture (mirrors M5, per-obligation)

- **Exec stmt modules**: one per exec fn — its obligations' statements
  as defs (statements only; span-mark landmarks preserved for
  attribution). Helper proof fns' stmt modules ALREADY exist (M5d-2);
  exec pkg modules import them for helper facts.
- **Exec pkg modules**: per exec fn, importing defs + own stmt module
  + helper stmt modules; obligations as theorems with the fn's tactic
  text; helper facts as hypothesis binders typed by stmt defs
  (identical to the proof-fn package pattern, M5a).
- **Link**: exec closed forms join the composition + sorryAx/axiom
  closure. Attribution stays per-obligation via span marks (M5b
  machinery).
- **Cache**: pkg-module cross-run cache (M5e) covers exec pkg modules
  with zero new code — the whole island-cache arc remains as the
  fallback path's cache.
- **Fallback**: UnsupportedScc-style graceful degradation to islands
  (which keep their `.verified` cache and sorry gate). Islands never
  disappear; they stop being the default.

## Sequencing

| Step | Content | Gate |
|---|---|---|
| M6.0 | Nonempty unification | suite + tgt green |
| M6.0b | full-roots census on tgt | taxonomy in doc |
| M6.1 | render unification decision | ⚑ co-design |
| M6.2 | exec stmt + pkg emission, flag-gated | suite parity |
| M6.3 | Link integration (exec closed forms) | gate green on tgt |
| M6.4 | tgt migration validation (the ~9 fns; retouch tactics per M6.1) | 3116/0 |
| M6.5 | exec packages become default; islands = fallback | measure |

## Open questions ⚑

1. Render unification appetite (option ii) vs bridge lemmas (iii) —
   who pays: a one-time tactic retouch, or permanent generated-lemma
   population?
2. Should M6.0's accessor change land alone first (it independently
   unblocks exec defs coverage and is the only piece with global
   island churn)?
3. Exec obligations with loops produce multiple theorems per fn —
   one pkg module per fn (all obligations together, one olean) or
   per obligation (finer cache, more modules)? Default proposal:
   per fn, matching islands.

## Expected end state

Exec fns verify like proof fns: shared defs, statement-typed helper
facts, Link-gated composition, cross-run cached. The 19s-per-island
cost, the double defs family, the shape-coupling fragility, and the
exec-outside-Link gap all close with the same structure. tgt cold
should drop well under 200s and warm stays at the verus-side floor.
