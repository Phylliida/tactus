# probe33 — W5 authoring shape de-risk (bootstrap-60)

**Verdict: PASS — `32 verified, 0 errors`** through the real bootstrap binary
(`--lean-backend --lean-all-proofs`), ~65s. Axiom closure of every VC of the
four key lemmas (`close_leaf_sem`, `holds_all_append`, `wp_stm_sound`,
`wp_sound_bites`): subsets of `[propext, Classical.choice, Quot.sound]` —
Lean-core only, no `sorryAx`. (`Quot.sound` enters via funext on the
function-typed state; `Classical.choice` via `simp_all`'s classical steps.
`wp_sound_bites` is `[propext]` alone.)

## What was tested (the four shapes probe32 didn't cover)

Reading probe24 (W5c frame-carrying formulation) against probe32: the Seq arm
no longer recurses under a lambda (frame-carrying `execSafeF` made Seq a plain
conjunction and the theorem a direct implication). The REAL untested shapes:

- **M1 — spec-closure literals**: `upd(st, x, n) = |k| if k == x { n } else
  { st(k) }` returning `spec_fn(u64) -> int`. **Works.** Emits as clean
  `Int → Int` Lean functions.
- **M2 — nested spec_fn types**: oracle `hp : spec_fn(u64, spec_fn(u64) ->
  int) -> bool` (state-consuming). **Works** — emits `Int → (Int → Int) →
  Prop`.
- **M3 — recursion under a `forall` binder**: the `FBind`/`All` arms
  `forall|n| #[trigger] holds(hp, *t, upd(st, x, n))`. **Works** (authoring,
  verification, emission; `structural_decreases` accepted).
- **M4 — induction THROUGH the ∀ arm** (`close_leaf_sem`: goal-side `close`
  agrees with semantic telescope): works **only in the state-generic shape**
  (below).

## The two backend facts that force the shape (both discovered here)

- **F1 — proof-fn calls inside `assert forall ... by` are DROPPED.** Every
  call in the by-block renders as a bare `True →` in the emitted VC (and a
  recursive self-call additionally emits NO termination VC — it vanishes
  entirely). So NO fact — unfold lemma or IH — can be injected under a binder.
  First failing attempt: per-n IH call inside `assert forall|n| ... by { ih(n) }`
  → VC goal was exactly the IH conclusion with `True → True →` where the facts
  should be.
- **F2 — ∀st-quantified equation hyps rewrite under inner binders.** Facts
  established in the ARM BODY (outside binders) do enter the VC, and
  `simp_all` uses a hypothesis `∀ st, lhs st = rhs st` as a rewrite rule
  under a nested `∀ n` in the goal. Hand-validated against the emitted
  defs olean first, then confirmed through the full pipeline.

## THE FROZEN IDIOM (binding for bootstrap-61..64)

1. **State-generic ensures**: every state-dependent lemma quantifies st in the
   ENSURES — `ensures forall|st| #[trigger] lhs(.., st) == rhs(.., st)` —
   mirroring hand-Lean theorems (which auto-generalize). IHs and unfold lemmas
   become plain arm-body calls; their ∀st-equations rewrite pointwise under
   binders. **Never use `assert forall ... by` with calls inside** (F1).
2. **st-as-param is fine when no binder is crossed** — `holds_all_append` and
   `wp_stm_sound` keep st as a signature param (their inductions never need a
   fact at a modified state under a binder) and verify unchanged. Mixed usage
   composes: st-generic callee facts instantiate at the caller's specific st.
3. **u_* one-step unfolds, st-generic**: closer
   `#[verifier::tactus_tactic("first | tactus_auto | (intros <;> rfl)")]` —
   the pointwise unfold is definitional on a constructor literal, so
   `intros <;> rfl` closes the ∀st wrap. Data-only unfolds (no st) keep the
   probe32 empty shape with the default closer.
4. **Induction discharge closer unchanged** (probe32):
   `first | tactus_auto | (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))`.

## Frozen model interface (for the bootstrap-61 batched edit)

Names mirror the hand-Lean (probe24/probe27) with Rust casing:

| authored (tactus-core)        | hand-Lean (probe24)  | type |
|---|---|---|
| `St` (spelled inline)         | `St := Int → Int`    | `spec_fn(u64) -> int` |
| `upd(st, x, n)`               | `upd`                | closure literal, as here |
| `hp` oracle param             | `hp`                 | `spec_fn(u64, St) -> bool` |
| `he` oracle param             | `he`                 | `spec_fn(ExprData, St) -> bool` |
| `lv` oracle param             | `lv`                 | `spec_fn(u64, St) -> int` |
| `holds(hp, he, lv, g, st)`    | `holds`              | over the real `GoalData` (Leaf/LeafE/Imp/All/Let) |
| `holds_all(...)`              | `holdsAll`           | over `GoalList` |
| `close_sem_e(..., f, st, e)`  | `closeSem _ (fun st' => he e st')` | continuation DEFUNCTIONALIZED |
| `close_sem_obligs(..., f, st, ls)` | `closeSem _ (fun st' => obligsSafe he ls st')` | second continuation shape |
| `obligs_safe(he, ls, st)`     | `obligsSafe`         | leaf-list safety |
| `exec_safe_f(..., f, s, st)`  | `execSafeF`          | frame-carrying, total on `StmData` |

Continuations: the real `execSafeF` needs exactly TWO continuation shapes
(single deep leaf / obligation list), so tactus-core gets two first-order
`close_sem_*` spec fns — no `ContK` datatype, no higher-order continuation
param. (This probe's `close_sem_leaf` is the one-shape miniature.)

## Files

- `lib.rs` — the mini-W5c (frame telescope FNil/FHyp/FBind, goals
  Leaf/Imp/All, function St + upd, goal-side `close_leaf`, semantic
  `close_sem_leaf`, frame-carrying `exec_safe_f`, `wp_stm`; u_* unfolds;
  `close_leaf_sem` M4 crux; `wp_stm_sound`; `wp_sound_bites` non-vacuity
  through a real FBind telescope).
- `run.sh` — canonical check + PASS/FAIL gate.
- Axiom-closure check (regenerate ad hoc): import the `out/lib/pkg` oleans and
  `#print axioms` each VC theorem; LEAN_PATH = `out/lib:out/lib/pkg:
  ~/.cache/tactus/prelude-<hash>` (Nix `lean` on PATH).
