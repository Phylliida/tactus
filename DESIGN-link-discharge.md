# DESIGN — Link discharge: premise-free closed theorems per proof fn

Status: DESIGN (bootstrap-73). Author: fable, 2026-07-16, with Danielle's
"no temporary hacks — do it the right way" steer as the brief.
Companion to `DESIGN-emit-module.md` (§4.4 Link layer) and
`DESIGN-W5-soundness.md`; first consumer is bootstrap-66 (the W5
adequacy-spine composition), but the feature is a general Link-layer
completion, not a W5 special.

## 0. What this adds, in one breath

The linker — which already walks proof fns in topo order and already owns
every statement's structure — additionally emits, for each eligible proof
fn, a **premise-free closed theorem under the fn's stable name**: the
fn's ensures with every callee-fact premise *discharged* by the callee's
own closed theorem (and, for recursive fns, the induction knot tied by a
synthesized structural fix whose decrease facts are the already-emitted
termination VC theorems). This turns the package's assume-guarantee
composition from a meta-argument *about* the artifact into an object *in*
the artifact, checked by the kernel like everything else.

## 1. Where the gap is today (two premise channels)

A pkg VC theorem's statement (`TactusStmts_…_stmt`) receives callee facts
through two distinct channels:

1. **Binder channel** (already discharged). Helper theorems referenced in
   a `tactus_tactic` TEXT become leading hypothesis binders on the stmt
   (the M2 short-name-shadowing mechanism). `build_link_module`
   (`source/lean_verify/src/generate.rs:3984`) applies these away:
   `def <name>_closed : <name>_stmt := <name> <dep>_closed …`, arg order
   = binder order via `direct_helper_deps` (:3865). For fns with no such
   deps the application list is empty and `_closed` is the definitional
   eta re-typing (emit-module F3).

2. **Weave channel** (never discharged — the gap). Facts from lemma
   CALLS in the Verus proof body are woven by the WP transform into the
   VC as *internal* premises — `∀ (_tactus_ret_N : Unit), <fact> → …` —
   interleaved with the fn's own lets and context at the exact call
   position. All of tactus-core's W5 soundness proofs use this channel
   exclusively (`ref_wp_sound`'s stmt carries `u_ref_wp`'s equation and
   `wp_stm_sound`'s equation as `→`-premises). Nothing instantiates
   them: today's `_closed` for these fns is a bare re-typing, so **no
   premise-free `∀ …, holds_all (ref_wp c s) st = exec_safe_f …` object
   exists anywhere in the emission.**

Consequently the gate note "composition + axiom closures kernel-verified"
means, precisely: all modules elaborate together, `#tactus_check_axioms`
passes per theorem, and the call graph is cycle-free (tri-state DFS). The
step from per-obligation, premise-laden theorems to the clean per-fn fact
is the standard modular-verification assume-guarantee argument — sound,
structurally checked (topo order), but living OUTSIDE the kernel. This
design moves it inside.

Note on why we do NOT lift weave-channel premises to leading binders and
reuse channel 1 wholesale: the interleaving is semantically load-bearing —
a woven fact may mention let-bound locals (`tmp__k`) introduced earlier in
the statement, so it cannot float above their binders. The discharge term
must navigate the weave in place (which is fine — see §3).

## 2. The artifact

For each eligible proof fn `f` in a package scope:

- **`<stable>.closed`** — one Lean `noncomputable def` (or `theorem`)
  whose type is the CLEAN STATEMENT: the fn's ∀-params + honest
  non-callee premises (param type-bound hyps like `h_o_bound`, which
  belong to the meaning of the statement) + the ensures — with all
  weave-channel callee-fact premises and their `_tactus_ret_N : Unit`
  companions gone, and binder-channel hypotheses applied away as today.
- **Stable naming**: the clean object is per-FN (not per-obligation), so
  it uses the fn's stable package name (package-check proof fns already
  have hash-free stable names, M5d-3) — e.g. `lib.wp_stm_sound_closed`.
  Consumers must never touch the line-numbered per-VC names
  (`_at_lib_3650_13_6…`), which shift under unrelated edits.
- **Multiplicity**: a fn has several postcondition VCs (one per arm
  path). The clean object is ONE theorem; the per-arm VCs are its
  ingredients (§3.3). For non-recursive fns with a single postcondition
  VC the correspondence is 1:1.
- **Axiom check**: `#tactus_check_axioms <stable>.closed [<Boundary>]`
  exactly as the existing closed defs.

**The clean statement is derived at emission time from the same source as
the premise-laden one** — the stmt renderer chokepoint — never parsed
back out of Lean text. Statement identity by construction, as everywhere
else in the emit-module design.

## 3. Discharge synthesis

### 3.1 The discharge spine (recorded at weave time)

The code that weaves a call's fact into the VC (the WP transform path
that emits `∀ (_tactus_ret_N : Unit), <fact> → …`) is extended to record,
per woven premise, a **spine entry**:

    { callee: stable name | SELF, inst_args: rendered arg terms,
      position: weave index }

The renderer already possesses the callee resolution and the rendered
instantiation (it renders `<fact>` from the call site via the same
RenderCtx); the spine is the same information kept as data instead of
discarded. Spine entries ride the fn's emission outcome to the Link
builder. `SELF` marks recursive calls (the IH premises) for §3.3.

### 3.2 Non-recursive fns: positional application

In topo order (already computed), the Link emits:

    noncomputable def f_closed_clean : <clean stmt> :=
      fun <params> <honest hyps> =>
        f_thm <params> <honest hyps>
          () (callee₁_closed_clean <inst_args₁>)
          () (callee₂_closed_clean <inst_args₂>) …

applying positionally through the weave: `()` for each Unit binder, the
callee's clean closed theorem instantiated at the recorded args for each
fact premise. Lets in the statement zeta-reduce under application — no
special handling. Topo order guarantees every `calleeᵢ_closed_clean`
already exists (cycles are already fatal upstream).

Leaf case: a fn with an empty spine gets `f_closed_clean := f_thm` with
only the Unit/binder cleanup — the base of the induction over the call
graph.

### 3.3 Recursive fns: the synthesized structural fix

For a recursive proof fn with `#[verifier::structural_decreases]` on a
single datatype parameter `d` (the only recursion shape tactus-core uses,
by the crate's own design discipline):

    noncomputable def f_closed_clean : <clean stmt> :=
      fun <params before d> d <params after d> =>
        match d with
        | Ctor₁ … => f_thm_arm₁ <params> <discriminator facts by rfl/simp>
                       <spine discharge, with SELF entries ↦
                        f_closed_clean at the recorded (smaller) args>
        | Ctor₂ … => …
    termination_by <D>.height d
    decreasing_by exact <the emitted termination VC theorem, applied>

Three facts make this synthesis principled rather than clever:

1. **The per-arm postcondition VCs are keyed by discriminator chains**
   (`¬d.isCtor₁ → … → d.isCtorₖ → …`); on a `match` arm the
   discriminators are definitional on the constructor (`rfl`-class), so
   the generated term supplies them mechanically.
2. **The IH premises are ordinary spine entries tagged SELF** — the fix's
   recursive call at the recorded args IS the discharge term.
3. **The decrease side-conditions are the already-emitted termination VC
   theorems** (`height <arg> < height d ∨ …`). Verus's recursion
   checking proved exactly the facts `decreasing_by` needs; the fix
   consumes them instead of re-deriving anything.

This mirrors, in generated Lean, precisely the induction the Verus-level
proof performed — no new mathematics enters the TCB; the generator is
untrusted (its output is kernel-checked like all emission).

### 3.4 Exclusions (fail-loud, census-tagged)

Per the house discipline, anything outside the supported shape emits NO
closed_clean and a sharp census tag (gate note counts them; no silent
caps):

- `discharge-mutual` — mutual SCCs (the M3.5 mutual blocks; the fix
  synthesis for an SCC is a joint fix — future arm).
- `discharge-wf` — recursive fns with non-structural / multi-param /
  WF measures.
- `discharge-blocked-dep` — fns whose (transitive) callees are excluded;
  propagates, so the counts stay honest.
- Exec fns are skipped by design — nobody cites an exec fn's theorem
  (emit-module §4.4); callers consume the contract defs.

## 4. Placement, cache, cost

Default: the closed_clean defs live in the existing `TactusLink_<scope>`
module (it is the topo-order place and already always re-checks — a
`sorry` can't ride the cache, and neither can a bad discharge). Risk: the
Link is on the every-run path and the new terms grow it; **measure the
cold/warm delta on tactus-core and on tgt** as part of acceptance. If the
growth is material, split a `TactusClosed_<scope>` module downstream of
Link with content-keyed caching (same machinery as pkg modules) — an L4
follow-up, not a day-one requirement.

## 5. What this upgrades (claims and consumers)

- **Gate note** gains: `N closed theorems formed (M discharged, K tagged:
  <tag histogram>)`.
- **VERIFICATION-PATH.md**: the assume-guarantee composition step moves
  from implicit meta-argument into the kernel-checked artifact; the
  residue list is unchanged (kernel / serializer / frontend / adequacy /
  platform pair) but the "composition kernel-verified" claim becomes true
  in its strongest reading. Update §4/§5 wording when this lands.
- **bootstrap-66** (first consumer): the adequacy spine consumes
  `lib.ref_wp_sound_closed` by plain `exact` — no hand chain-discharge,
  no drift gate, no line-numbered names.
- **W8** (authority flip): needs clean theorem objects; this is its
  prerequisite landing early.
- **Every tactus-verified crate** (tgt included): the package artifact
  gains end-to-end per-fn theorems, not only per-obligation VCs — a
  strictly stronger deliverable for any external auditor.

## 6. Acceptance

1. tactus-core: every W5 proof fn (and every other eligible proof fn)
   gets a closed_clean; Link elaborates; `#tactus_check_axioms` clean;
   suite + package gate green; counts reported.
2. **Mutation-kill**: (a) perturb one spine instantiation arg in the
   generator → Link elaboration must FAIL (the kernel rejects the
   discharge); (b) perturb a decreasing_by consumption → fail. Pinned as
   e2e tests, in-harness.
3. `lib.ref_wp_sound_closed` and `lib.wp_stm_sound_closed` exist with
   the exact clean statements (golden-pinned), and a probe consumes
   ref_wp_sound_closed by `exact` (folds into bootstrap-66).
4. Cost: cold/warm wall-clock delta on tactus-core + tgt recorded here.
5. Census tags on tgt recorded here (expected: some `discharge-mutual`
   from the M3.5 mutual fns; histogram is the next-arm worklist).

## 7. Ladder

- **L0 (probe34, no production code) — DONE 2026-07-16**: validated the
  fix shape / discriminator discharge / positional weave application /
  termination-VC consumption on `holds_all_append_closed` (recursive,
  bound-free chain) + the holds_close_e FNil arm; `theorem` keyword works
  incl. recursion (Q3). Targets shifted from wp_stm_sound/ref_wp_sound
  because L0 FOUND the bound gap (Q4/F1) that blocks their u_* callees —
  the wp chain discharges only after Q4 is resolved (R-a recommended).
  Shapes frozen in `probe-w0/probe34_link_discharge/REPORT.md`.
- **L1**: spine recording at the weave chokepoint + clean-statement
  rendering + non-recursive discharge codegen; fixture green.
- **L2**: structural-fix synthesis for single-datatype-param recursion;
  tactus-core green end-to-end (this is the W5 unblock).
- **L3**: gate-note counts, census tags, mutation-kill pins, cost
  measurement on tgt; acceptance ledger filled in above.
- **L4 (optional, data-driven)**: TactusClosed module split + caching;
  mutual-SCC arm.

## 8. Open questions (Danielle knobs)

- **Q1 — naming**: `<fn>_closed_clean` vs `<fn>_closed` (renaming
  today's eta re-typings to something like `_closed_hyp`)? The doc uses
  `_closed_clean` to avoid touching existing names; a one-time rename to
  make `_closed` mean the clean thing is prettier and cheap NOW (few
  consumers) but churns the Link golden tests.
- **Q2 — default-on**: emit closed_clean for all eligible fns always, or
  behind a flag first? Recommend always-on once L2 lands (it is additive
  and kernel-checked; a flag would just hide regressions).
- **Q3 — theorem vs def**: `theorem` is the honest keyword for a Prop;
  the existing Link uses `noncomputable def` (needed where stmts are
  `@[reducible] def : Prop`). Follow the existing convention unless it
  fights the elaborator.

## 9. Final status — COMPLETE for tactus-core (2026-07-18), lessons ledger

67/67 per-fn closed theorems, 0 pending (6 fix + 9 straight-line + 52
zero-spine), surviving the N1/N2 statement reshape. What the build taught,
beyond §3's design (each found by a gate error, none by foresight):

- **R-b (wf defs)**: extrinsically-typed obligations demand `{Dt}Wf`
  predicates. Mutual inductive families need `mutual … end` wf blocks
  with per-def `termination_by structural x` INSIDE the block; SCC
  extraction must skip non-cycle waiters when seeding. Struct-emitted
  dts (single variant named after the type) have no matchable ctor —
  projection-form wf defs. Single-conjunct wf clauses are bare Props:
  no `⟨…⟩` patterns, bind bare.
- **R-c (preservation synthesis, `wf_synth.rs`)**: for spec fns feeding
  wf-demanding positions, synthesize `g_wf` lemmas whose proof terms are
  ISOMORPHIC to g's body (ctor ↦ ⟨comps⟩, rec ↦ rec, call ↦ callee _wf,
  match ↦ match-mirror destructure, if-in-arm ↦
  `(congrArg DWf (if_pos h)).mpr` defeq transport, top-level if ↦
  `unfold`+`by_cases` — non-recursive defs keep equations). Everything
  rides defeq iota; the rec_1 equation-lemma gap never bites in term
  position. Demand-driven iterative driver: fixpoint → parse wf-transport
  pendings → closure over body refs → topo synth → re-fixpoint.
- **The 686 lesson (load-bearing)**: tactic goals inside term-mode match
  arms can be POSTPONED outside the arm's context, losing pattern-bound
  hypotheses — `(by omega)` is only safe context-free; every
  context-dependent bound rides a NAMED component/hypothesis.
- **Caller-side resolution**: value texts resolve to wf proofs by
  lets-chasing (`tmp__N`), raw projection keys (unboxed fields), boxed
  bare vars as `{v}.deref` own-hyp keys, ctor literals as ⟨…⟩ with named
  bound comps, and synthesized-lemma application with interleaved
  value/hyp args. Paren handling MUST be depth-aware
  (`strip_outer_parens`) — `trim_matches` mangles nested ctor texts.
  Straight-line closers RETRY, converting resolver failures naming own
  params into own wf hypotheses (corollaries' stm-literal args).
- **decreasing_by**: term-thm bullets are ILLEGAL in multi-self-call arms
  (later termination VCs carry self-referencing premises). Heights are
  WF-compiled → equations exist → the uniform
  `all_goals (simp [{Dt}.height] <;> omega)` closes every goal
  (`<;>`, not `;` — simp may close outright).
- **N1/N2 adaptation**: match-split statements carry
  `∀ field-binders, scrut = Ctor fields →` — field binders instantiate
  with the arm pattern's tokens (accessor-mapped for named fields);
  patterns always name binders (`_pb{i}`, never `_`); the ctor equation
  closes via the existing `(by simp)` branch argument.
- **Consumption (bootstrap-66/probe37)**: the adequacy spine consumes
  `ref_wp_sound_closed` by `iff_of_eq` with DEFINITIONAL unification —
  the option-(iii) bet paid in full. The wf hypotheses are the honest
  residual interface, by-construction for serializer output.

Next frontier: the gt census (2900+ fns of trait/generic/Seq-view shapes
tactus-core doesn't have) — every pending is a work-item toward
universality.
