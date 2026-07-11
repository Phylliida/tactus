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

## Decisions (2026-07-10, Danielle)

- **Render unification: YES** (option ii below). Bridge lemmas only if
  migration friction demands.
- **Granularity: per-fn** pkg modules (all of a fn's obligations in
  one module/olean, matching islands).
- **Flow: staged** — each step below lands green and is valuable
  alone; implementation begins in a fresh session.

## The trust seam (the load-bearing design issue)

Today, inlining = re-proving: an island that contains
`lemma_rate_pos` re-elaborates its proof against the render in scope.
No cross-render trust is ever needed.

Under M6, an exec pkg module imports the helper as a STATEMENT
(hypothesis binder typed by a stmt def), whose proof happened in the
PROOF world. If the two worlds render spec fns differently
(vir `match` vs simplified `if .isVariant`), the imported fact is
typed against a render Lean cannot connect to the local one —
**semantically equal, but not Lean-known-equal.** Axiom-bridging that
seam (option i) fails the transparency bar. Render unification
(option ii, DECIDED) removes the seam by construction; generated
`vir_x = simpl_x` bridge lemmas (option iii, kernel-checked) remain
the fallback device only.

## M6.1 — render unification via DUAL-KRATE (resolved mechanism)

The accessor-shaped render is NOT a lean_verify rendering knob: 
`check_exec_fn` receives Verus's post-`ast_simplify` krate, where
matches are already lowered to `isVariant`/field chains CRATE-WIDE —
spec fns and vstd instances included. The fn's own obligations come
from separate SST params (`fn_sst`, `check`).

Mechanism: the exec path's spec-world/defs renders from the
**unsimplified vir krate** (same as the proof world — match-style),
while obligations keep their SSTs (accessor-style, as WP output
genuinely is). Plumbing: a second krate param through
`check_exec_fn`/`emit_exec_fn` feeding `for_crate` and
`krate_preamble`; the verifier holds both krates.

Consequences, all good:
- The vstd `DeepView (Option T)` instance renders `match`-style — the
  `Inhabited T` synthesis failure at exec base:168 VANISHES, shrinking
  M6.0 (below) to a residue.
- Spec-fn renders are identical across worlds → the trust seam never
  exists; helper statements are shape-neutral by construction.
- The shape-coupling hazard (dragon B) dissolves: there is ONE
  authoring world. tgt's ~9 migrated exec tactics (authored against
  accessor-shaped spec fns) get a one-time retouch — the 10s scratch
  loop makes this tractable, and it is the LAST such migration.
- **Unlocks re-landing the kind-specific ladders + kind-suffixed
  scope keys** (built and reverted in `63005a2` — the revert reason
  was exactly the shape coupling). With one render world, the exec
  scope becomes "full roots or nothing," the dead-weight duplicate
  defs family dies, and the scope-key collision hazard closes.
- Accessor DEFS stay emitted for the exec scope (obligation bodies
  need them); only spec-fn/instance BODY renders change.

Named risk (checked empirically at this step): obligations may
reference simplified-only synthetic fns (tuple ctors etc.) that the
vir spec-world doesn't emit — the suite + a tgt run flush these out;
any stragglers get vir-side emission or a targeted synthetic-fn
whitelist.

## M6.0 — Nonempty/Inhabited currency unification (now a residue)

After M6.1, accessor applications survive only in OBLIGATION bodies.
Generated accessors demand `[Inhabited V]`; a generic exec fn whose
obligation projects a type-param-typed field needs that premise on
the obligation theorem. Islands already handle this today (generic
exec fns verify on tgt), and packages REUSE the island theorem
builder, so existing behavior carries over unchanged. The residue:
swap the accessor signature to `[Nonempty V]` + `Classical.ofNonempty`
(accessors are already noncomputable) so the whole "type has a value"
economy is single-currency with the nonempty arc — smaller premises,
uniform machinery, and the PreambleConfig caveat ("accessors for
types with non-Inhabited fields break elaboration even when unused")
lifts. Blast radius after M6.1 is small: accessor defs + obligation
binder sites; island texts change once (the `.verified` cache absorbs
it in one run).

## M6.2 — exec stmt + pkg emission (per-fn)

- Exec stmt module per fn: its obligations' statements as defs
  (span-mark landmarks preserved for attribution).
- Exec pkg module per fn: imports defs + own stmt module + helper
  stmt modules (helper stmt defs ALREADY exist, M5d-2); obligations
  as theorems with the fn's tactic text; helper facts as hypothesis
  binders typed by stmt defs — identical to the proof-fn pattern.
- Flag-gated; islands remain the graceful-degradation fallback (with
  their `.verified` cache and fatal-sorry gate) — they stop being the
  default, they never disappear.
- Cache: the M5e pkg cross-run cache covers exec pkg modules with
  zero new code.
- Fold-ins while touching this code (right-way housekeeping):
  tracked-write for the Link module (stop rewriting identical bytes),
  numeric island/pkg cache-hit counts in the gate note, and a `v1 `
  version prefix on the `.ladder` sidecar format while it is young.

## M6.3 — Link integration

Exec closed forms join the composition + sorryAx/axiom closure — the
soundness headline: exec obligations become Link-gated for the first
time. Attribution stays per-obligation via span marks (M5b).

## M6.4 / M6.5 — tgt validation, then default

Retouch the ~9 tgt tactics (M6.1), validate 3116/0 cold + warm at the
floor, flip exec packages to default with islands as fallback,
measure and record.

## M6.1 + M6.1b STATUS: DONE (2026-07-11)

Landed: `5c4e3c9` (dual-krate), `fcddbea` (kind ladders + scope
suffix re-land), tgt retouch `05e0bc7`. Suite 533/0; tgt errors =
exactly the pre-existing apply_hom_symbol_exec baseline.

What the day proved:
- Dummy-param seam closed the right way: `injects_zero_arg_dummy`
  exported from vir (injector's own predicate, used by the injector),
  drop-dummy applied at both SST render boundaries.
- A real vir-render gap surfaced and fixed: tuple patterns emitted
  `tuple%N` ctor names; `Pattern::Tuple` now renders `(p, q)`.
- The retouch surface on tgt was ONE fn (find_cancellation_exec,
  4 occurrences of one cast-discharge pattern — the new match-world
  axioms are CLEANER, without simplify's let-tmp chains).
- The Inhabited dragon (old base:168) died as predicted: vstd
  instances render match-style. Census: the next full-roots blocker
  is a `Tactus.Ref (option.Option T)` type mismatch at base:167 —
  the Ref-ABI corner (M6.0b item).
- Timing note: a large apparent floor regression (~89s → ~300s
  emit-only) was investigated with perf + a pre-M6.1 worktree A/B and
  attributed to HOST LOAD (load average ~208 on 64 cores during all
  measurements; baseline binary measured 250s under the same load =
  yesterday's 85s × oversubscription). Relative A/B: M6.1 floor delta
  ≤ ~20%, possibly noise. The churn diagnostic (touch/find-newer)
  confirmed steady-state runs re-elaborate NOTHING (only the proof
  `.ladder` sidecar rewrites — an untracked write, mtime-only;
  housekeeping item: tracked-write it). Clean re-measure deferred to
  an idle host.

## Sequencing (each step lands green alone)

| Step | Content | Session-sized? |
|---|---|---|
| M6.1 | dual-krate render unification + tgt tactic retouch | yes |
| M6.1b | re-land kind ladders + scope suffix (dead-weight removal) | small, same session |
| M6.0 | accessor Nonempty residue + full-roots census on tgt | yes |
| M6.2 | exec stmt/pkg emission, flag-gated + housekeeping fold-ins | yes |
| M6.3 | Link integration | small |
| M6.4/5 | tgt validation → default | yes |

## Artifact ledger (transparency — every sidecar and its key)

| Artifact | Meaning | Invalidated by |
|---|---|---|
| `<part>.lean`/`.olean` | defs part + build | content compare vs disk |
| `<part>.manifest` | per-command hashes | superset check (append = non-breaking) |
| `<scope>.ladder` | winning attempt (or FAILED + per-attempt hashes) + toolchain fp | winner render hash change; fp change |
| `<island>.verified` | last completed run on this text succeeded | text change; defs breaking; fp change; removed before every live run |
| `TactusPrelude.lean` marker | prelude source + toolchain fp | either changes |

## Expected end state

Exec fns verify like proof fns: one render world, shared defs,
statement-typed helper facts, Link-gated composition, cross-run
cached. The 19s islands, the double defs family, the shape-coupling
fragility, and the exec-outside-Link gap close together. tgt cold
drops well under 200s; warm stays at the verus-side floor.
