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

## M6.0b + Option B STATUS: CENSUS COMPLETE, MERGED, GREEN (2026-07-11)

Exec full-roots defs PASSES on tgt; islands import the shared exec
defs module. Census fixes: Match-scrutinee Ref bridge, builtin
signature axioms (Prop-returning), Nat-sorted integer bounds, 3
lean_axiom_eq attributes in tgt. Option B (fully-qualified names)
merged; pkg/stmt/link machinery adapted (no namespace wrappers).
Structural fixes from the integration: consumer-routed bc-axiom
placement (umbrella; subrange axiom at the companion site in-part),
partition-aware ladder content hashes, binary-aware ladder record
fingerprints. Fast iteration: /tmp/defs_repro.rs shape (Vec exec fn +
drop_first spec fn) exercises the full defs ladder in ~20s on the
debug binary.

Remaining M6 sequence: M6.3 Link integration → M6.0 accessor residue
→ M6.2 fold-ins → M6.4/5 tgt validation + default flip. Detailed
specs below (written 2026-07-11 while M6.2 validated).

## M6.2 STATUS: LANDED (2026-07-11)

Exec fns verify via package modules under --tactus-package-check:
`emit_package_exec_fn` (own stmt module with per-obligation statement
defs, PRECISE per-obligation helper scan over the SST-derived tactic
texts — the ExecFn every-proof-fn over-approximation is dead on this
path), `check_exec_fn_via_package` (M5e cacheable rule, fatal sorry,
island fallback on any inexpressibility). One integration finding:
Option B island texts cite helpers by GLOBAL dotted name, but package
binders can only carry short names — `bridge_qualified_helper_refs`
rewrites qualified helper references inside machine-generated pkg
modules only (islands keep the verbatim text; one source serves both
routes), with a short-name-collision guard that bails to islands.
Suite pins: smoke (short + qualified citations), sorry-fatal.

## M6.3 spec — Link integration for exec (the soundness headline)

Exec obligations become Link-gated: closed forms join the composition
+ sorryAx/axiom closure. Post-M6.2 state: exec pkg oleans verify
per-fn but are NOT registered (`record_pkg_olean_built` deliberately
skipped) because two things are missing.

**(1) Obligation registry.** `build_link_module` runs from the
AST-level package graph; exec obligations only exist in the SST,
available per-fn at check time. So: each `check_exec_fn_via_package`
success records `(fn, obligation thm names, per-obligation dep lists,
stmt module, pkg olean path)` into a registry (same pattern as
`record_pkg_olean_built`); the Link/gate pass — which already runs
after all per-fn checks — reads it. Exec obligations are LEAVES in
the dependency graph (nothing references them), so they append after
the proof-fn ordered loop; per obligation:
`noncomputable def <thm>_closed : <thm>_stmt := <thm> <dep>_closed …`
followed by `#tactus_check_axioms <thm>_closed [<Boundary>]` with the
EXEC defs family's declared axiom set as Boundary.

**(2) The two-family problem — DECISION NEEDED.** Exec pkg modules
import EXEC-family stmt modules; helper proof fns' closed forms live
in the PROOF-family Link. One Lean module cannot import both families
(two copies of the spec world = duplicate decls). Options:

- **A. Cross-family import** — collides; not viable.
- **B. Exec-family pkg copies of cited helpers.** Helpers cited by
  exec tactic texts get a second pkg module built against the exec
  family; the exec Link is then self-contained. Incremental, small
  (tgt cites ~5 helpers from exec texts), double-elaborates only
  those helpers. Ships the soundness headline in one session.
- **C. Family unification.** When full-roots defs pass
  (`covers_exec`), verify PROOF fns against the exec defs module too:
  one family, one stmt partition, one Link holding both proof closed
  forms and exec obligations. Halves ladder cost, kills the dual-
  family maintenance surface. Proof-only family survives solely as
  degradation for `covers_exec == false` crates. Bigger churn: proof
  islands/pkg re-key to the exec defs name (one-time marker/olean
  invalidation), and the fallback matrix needs care (a crate whose
  full-roots ladder REGRESSES must degrade proof fns gracefully back
  to the proof family).

LANDED 2026-07-11 same session (C-1 + C-2 both green: suite 543/0,
tgt 82s at baseline, exec closed forms kernel-checked in the Link).

DECIDED 2026-07-11 (Danielle): **C — the right way first.** Key
implementation observation shrinking C: the proof pkg/stmt/Link
machinery is already family-parametric (everything takes `defs`), so
C is a defs-SELECTION change at the check chokepoints, not new
machinery. Sequenced as:

- **C-1 (unification):** in package-check mode, both proof and exec
  checks first try the full-roots family
  (`for_crate(Exec).filter(covers_exec)`); proof fns fall back to the
  proof family when unavailable (today's path — the degradation
  matrix), exec fns fall back to islands. On success the proof ladder
  is never even attempted (the halving). Family choice is memoized
  per scope → deterministic within a run, no mid-run flips. One-time
  cache re-key (stmt/pkg modules rename to the exec-family scope).
  Non-package modes untouched (islands are standalone).
- **C-2 (= M6.3 core):** obligation registry recorded by
  `check_exec_fn_via_package` successes; Link appends exec closed
  forms after the proof-fn ordered loop (obligations are leaves);
  `#tactus_check_axioms` per closed form against the exec-family
  Boundary; exec pkg oleans registered; sorry relaxes to Link-backstop
  parity (flip the sorry-fatal pin to expect the GATE catch).

**(3) Sorry relaxation.** Once exec closed forms are Link-gated,
exec pkg sorry drops from fatal-at-fn to warning + fatal Link sorryAx
backstop (proof-fn parity; flip `island_sorry_failure` off the pkg
path and pin with a test that a sorry FAILS via the gate instead).

**Attribution:** per-obligation span marks already ride the pkg
source map; `#tactus_check_axioms` failures name the closed form,
which embeds the obligation theorem name → same Rust span.

## M6.0 spec — accessor [Nonempty] residue — DONE 2026-07-11 (was
already substantively landed: accessors take [Nonempty] +
Classical.ofNonempty; datatypes stay Inhabited PROVIDERS for getElem!;
instNonemptyOfInhabited bridges. Remaining work was the stale ProofFn
caveat comment, now lifted.)

Swap generated accessor signatures from `[Inhabited V]` +
`default` to `[Nonempty V]` + `Classical.ofNonempty` (accessors are
already noncomputable). Blast radius: accessor defs (crate_defs
emission) + obligation binder sites that thread the instance. Island
texts change once; `.verified` + ladder caches absorb it in one run.
Payoff: single type-has-a-value currency with the nonempty axiom arc,
smaller premises, and the ProofFn-config caveat ("accessors for types
with non-Inhabited fields break elaboration even when unused") lifts
— which may let the config distinction itself collapse post-C.

## M6.2 fold-ins — DONE 2026-07-11 (all three below)

- Tracked-write for the Link module (stop rewriting identical bytes —
  today it invalidates downstream mtimes every run).
- Numeric island/pkg cache-hit counts in the package gate note
  (observability: "N pkg cached, M islands cached, K elaborated").
- `v1 ` version prefix on the `.ladder` sidecar while the format is
  young (forward-compat for record-shape changes like the fp fix).

## M6.4/M6.5 spec — validation, then default

- **M6.4 validation — DONE 2026-07-11** (loadavg ~10-14 during the
  measurement, so these are conservative): COLD 186s (every Lean
  artifact wiped: defs ladder + stmts + pkg + Link rebuilt from
  nothing), WARM 80s/82s — matching the island-era best (82s) with
  the composition gate in the loop. Errors = apply_hom baseline (2)
  on all three runs; exec ladder `v1 0`; 27 pkg modules (Link builds
  on gate runs — skipped here because the baseline failure skips the
  gate, pre-existing behavior).
- Original protocol: tgt cold run (wiped TACTUS_LEAN_OUT) + two
  warm runs under package-check; record cold/warm wall-clock and the
  gate note counts vs the pre-M6.2 island baseline (82s steady).
  Cross-check: zero islands emitted for pkg-covered fns, exec ladder
  `0`, errors = apply_hom baseline, `#tactus_check_axioms` closure
  green over the full crate. (tactus-computability-theory dropped
  from the protocol — Danielle 2026-07-11: tgt is the validation
  crate.)
- **M6.5 default flip — DONE 2026-07-11.** Package-check is the
  --lean-backend default; --tactus-islands opts out; old flag forces
  on. tgt default run 82s at baseline; opt-out verifies identically;
  tgt check.sh inherits the default unchanged. The flip surfaced and
  fixed two latent issues: per-fn fallback noise (now silent — the
  gate note summarizes) and ProofClasses umbrella-routing (now Base
  with prereq hoist, consumer-routing principle). **M6 COMPLETE.**
- Original spec: package-check becomes the --lean-backend
  default (islands remain automatic fallback per-fn); flag inverts to
  an opt-out (--tactus-islands). Update tgt/ct check.sh, tutorial
  docs, and the artifact ledger. Only after M6.3 (exec fns must not
  LOSE their soundness gate by moving off islands) and one clean
  M6.4.

## Post-M6 horizon (recorded, not scheduled)

- **C follow-through:** delete the proof-family ladder when unified
  (keep degradation path); measure the ladder-cost halving.
- **tgt check.sh flip** to package-check default once M6.5 lands.
- **Mutual exec SCCs:** not applicable (obligation theorems never
  mutually reference); documented here so nobody goes looking.
- **apply_hom_symbol_exec:** still blocked on
  tactus BUG-call-arg-temp-claimed-typ.md — unrelated to packages,
  the 2-error tgt baseline until fixed.

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
