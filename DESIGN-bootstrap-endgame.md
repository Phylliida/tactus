# DESIGN — bootstrap endgame: from rung 5 to the full claim

**Date:** 2026-07-24. **Status:** agreed plan (policy points P1–P4 confirmed
by Danielle 2026-07-24; Q1–Q4 resolved same day under her delegated
guidance — "verify as much as possible, the right way, no hacks or
half-way measures" — resolutions in §9).
**Position:** rungs 1–5 of the claim ladder (`VERIFICATION-PATH.md` §4) are
held. W5/W6/W7 boards are closed. What remains is rung 6: making the
certificate **default, corpus-wide, and census-honest**. The hard theoretical
spine is done; everything below is coverage arms, policy, and infrastructure
honesty.
**Supersedes:** the "Later / parked" ordering in `NEXT.md` §4 (this doc is
now the ordered map; NEXT.md points here). Board cards remain the source of
per-brick detail.
**Inputs:** `FINDINGS-b74-slice2.md` (§5 gap list, §4 process lessons),
`DESIGN-b74-slice2-serializer.md` §7 (follow-up queue),
`DESIGN-bootstrap.md` (W-ladder), review findings of 2026-07-24.

---

## 0. Shape of the remainder

Six milestones. C is small and first (restores a clean number the rung-5
claim leans on). A is the coverage grind (seven arms, two of them real
machinery). B is the payoff flip — the bootstrap becomes something a user
*gets* rather than something the program *has*. D is a standing discipline,
not a brick. E and F are the end-state polish.

```
C (discharge 0-pending)          small, next
A1..A7 (coverage arms)           small ×4, medium ×2, medium-large ×1
B (W4 default flip)              gated on P2/P3 + A-coverage
D (W5 keeps pace)                standing policy + one tripwire
E (W8 authority flip)            after B soaks
F (trust-inventory shrink)       parallel, small
```

Definition of fully bootstrapped (rung 6 held): every claim in every crate
flows through packages whose composition, axiom closure, statements
(structure **and** expressions), and definitions are kernel-checked against
the proven-sound reference, **by default**, with the census naming exactly
what is uncovered and the trust inventory printed per run.

---

## 1. Policy decisions (P1–P4, agreed 2026-07-24)

These four came out of the b74 slice-2 review and are now standing policy,
not suggestions.

### P1 — the poison bit is a trust-surface widening; treat it with care

`FINDINGS-b74-slice2.md` §2.1: the "mentions residue" wrap-forcer is a
*text* check computed serializer-side; the model reads the mark. The
serializer is TCB, so the wrap-vs-hoist gate is currently partially
trusted, not checked. A lone wrong bit fails loudly (refWp diverges from
production), but it is a common-mode channel of the bootstrap-48/B1 class:
correlated bugs in the serializer's mentions-logic and the emitter's
`lexpr_mentions_var` could let a wrong wrap decision bridge green.

Mitigations, in order:

1. **Now (with C, cheap):** add a poison-flip mutation to the existing
   mutation-kill battery — flip the serialized poison mark on a fixture
   cert, assert the bridge verdict flips 1→0. This pins that the channel
   is live, in both directions.
2. **Now:** add the poison mark to the serializer faithfulness-contract
   doc comment (`sst_serialize.rs` header) — it is a semantic predicate
   mirrored in Rust, not a transcription, and the contract must say so.
3. **At A7 (decided — §9 Q3):** once leaves are deep `ExprData`,
   recompute "mentions" reference-side and *derive* the poison mark
   instead of trusting it; the serializer's copy becomes a cross-check,
   then retires. This lands with A7's vocabulary work, not deferred to
   E — a trusted bit should not outlive the first milestone able to
   check it.

### P2 — honest-fail classes need a policy before the W4 flip

Today the six documented honest-fails are fine: the bridge is a
differential gate and the runners assert "behaves as classified." W4c
makes bridge failure a verification error. Standing policy from now on:

> Before the b68 flip, **every** honest-fail class becomes either
> (a) a fixed serializer/refWp arm, or (b) a **loud census rejection** —
> the serializer refuses with a named tag, the fn is counted uncertified
> in the gate's `certified M/N` line. A red bridge on an unclassified
> shape is a hard error with the "goal drift against reference"
> diagnostic (O7), never a silent or confusing failure.

Concrete obligations under this policy:

- `assert-forall` → census tag now (A6 short form).
- `hoist-mixed-shadow` (the unhit MIX case: a shadow before a later
  wrap-forcer) → the serializer must **detect** the MIX condition and
  reject with a tag. Unhit-so-far is not a detector; today a user hitting
  it would get an unexplained bridge mismatch.
- call-mut, tactus-mode assert-query, N2-match, apply_hom call-arg-temps,
  vec_read stage-B → each either fixed by its A-item below or tagged at
  flip time.
- The census-tag vocabulary is closed and documented (one table in the
  b68 card); adding a tag is a reviewed event, per the fail-loud
  philosophy in `VERIFICATION-PATH.md` §6.

### P3 — infra staleness holes gate the flip

Both known staleness holes erode trust in the gate exactly when the gate
becomes the default product surface, so both are **b68 gate conditions**,
promoted from "parked":

- **stmts-olean staleness** (FINDINGS §4): a fresh `TactusStmts_*.lean`
  written without its `.olean` rebuilt, producing misleading
  Type-mismatch/sorry cascades pointing everywhere except the cause.
  Investigate the stmts-module rebuild logic; fix; pin with a test that
  regenerates a stmts module and asserts the olean is rebuilt (or the
  gate detects and reports the skew).
- **emitter-binary fingerprint** not in the verification-cache key: add
  a build-fingerprint tag. The flip multiplies bridge-module traffic;
  cache-adjacent staleness at scale means spurious red gates nobody can
  diagnose.

### P4 — Link discharge back to 0-pending is near-top priority

The 144/6 residual is called "pre-existing" but rung 5's claim leans on
premise-free per-fn closure — the 6 are a standing asterisk. The fix is
spec'd (`DESIGN-b74-slice2-serializer.md` §7.1) and half-landed
(`HypProvenance::HoistEq` exists on main, `9a88b6c`). This is milestone C,
first in the order.

---

## 2. Milestone C — Link discharge 0-pending — **DONE 2026-07-24**

**Result: Link discharge 150/0** (was 144/6; 12 fix + 15 straight-line +
123 zero-spine), tactus-core gate 231/0 + package gate kernel-verified,
lean_verify units 406/0, e2e 551/0, probe9 all-classified, probe13/14
green. Full log on `bootstrap-73` (now closed).

The 6 pendings split into two classes, both composed in
`link_discharge.rs`: **HoistEq** (4 fns — the N1 hoisted-let pair parses
to `Node::HoistEq`, `leading_alls` trims the value binders, `replay_lets`
replays `let x := v;` in spine order, the ∀ instantiates with the let
name and the equation premise closes by `rfl` zeta-defeq) and **Req**
(2 fns — the fn's own `requires` carried as a hypothesis binder, its
contract not a woven premise). Loud-pend guards: malformed hoist strips,
hoisted binder in a postcondition leaf, calls to requires-carrying fns,
hoist/requires in fix fns. Six unit pins in `tests/link_discharge.rs`.

**P1 items landed with it:** the serializer contract names the poison
mark as a trusted semantic predicate (sst_serialize.rs header), and
probe13 gained the `poison_flip` kill (zeroing ALL marks flips the
bridge 1→0). Two live finds from its first runs, now recorded on the
card: a single-bit flip is masked by the duplicated Assert+Assume hyp
pair (FINDINGS §3) — the honest channel-kill zeroes all marks; and
probe13/14 had been stale-red since the prelude split + b74 reshape —
repaired (probe9 all-preludes glob), with the deref class parked as an
`=0` tripwire that fires when A5 lands.

---

## 3. Milestone A — coverage arms to census-clean

tgt census after b74: call-generic 0, call-forall-path 0; remaining tags =
1 call-mut + 4 assert-query-tactus, plus the six documented honest-fails
(probe9: vec_read, head_exec; probe11: apply_hom_gen/inv, the two
assert-forall lemmas). The arms, smallest first:

### A1 — b70/71 close-out (small, unblocked)

Re-run the vec_read/use_clamped bridges end-to-end to the pre-b74 limit,
mutation-kill the ∀-path frame, close cards `bootstrap-70`/`bootstrap-71`.
Pure follow-through; b74 cleared the blocker.

### A2 — apply_hom class: call-arg temp lets + auto-ref coercion (small-medium)

Production wraps the whole goal when call-arg temps appear as typ-less
`Wp::LetRaw` frames; the serializer currently types them from `local_typs`
and hoists — wrong side of the 3-mode gate. Classify them plain-wrap, and
keep the `Tactus.Ref.mk <arg>` coercion in instantiated requires (today
dropped). **Acceptance:** apply_hom_gen/apply_hom_inv bridge-close on
probe11. **Card:** new, `bootstrap-75` (or fold into the b70/71 close if
the diff is small).

### A3 — b69: Tactus-mode assert-query (small-medium; decided — §9 Q1)

Production renders the 4 remaining tgt assert-query fns inline
(`have h : P := by <tactic>` — no separate goal, P enters as hyp).
**Decided: dedicated `StmData::AssertQueryTactus` variant** (Q1), not
Assume-with-mark. Rationale: `AssertQueryNl` is already a first-class
variant — modeling one assert-query mode as a constructor and the other
as a marked Assume is an asymmetric half-measure; and the trust story is
cleaner as data — the P is *proven inline* (kernel-checked at
elaboration), not assumed, so the mirror should say so structurally
rather than via a side-channel bit that only census reads. Shape: wp
semantics = the Assume arm (P enters the continuation's hyp frame, no
separate goal); own W5 soundness arm delegating to the Assume argument;
census/trust reporting counts it as proven-inline, never as an assume
(it must not trip assume-warnings). One cache-churning tactus-core edit
(batch with A5's `StmData::Match` if timing aligns — one churn, not
two). **Acceptance:** the 4 fns serialize and bridge;
`assert-query-tactus` census tag drops to 0; the in-model column (D)
gains the variant. **Card:** `bootstrap-69` (in_progress).

### A4 — call-mut arm: prophecy/rebind in the frame mirror (medium-large)

The genuinely new machinery: `&mut` args at call sites — prophecy/rebind
of the arg in the frame mirror (serializer + refWp side; the W5d *model*
already has the ∀-final-value prophecy story, this is the stage-A
statement mirror catching up). Unblocks vec_push7, fill_zeros fixtures +
runtime.copy_word on tgt. **Card it before starting** (standing
instruction from NEXT.md) — the card should freeze the frame shape from
step-0 evidence (regenerated certs for vec_push7) before any model edit,
per the b74 lesson. **Acceptance:** all three subjects bridge-close;
`call-mut` census tag drops to 0; mutation-kill on the prophecy binder.

### A5 — Match-statement arm (medium)

`StmData` has no Match today; head_exec honest-fails on the N2 match-split
(per-arm value temps hoist as FLetH pairs inside per-arm goals). Work:
`StmData::Match` + per-arm frame assembly + serializer transcription.
Same step-0-evidence-first discipline. **Acceptance:** head_exec closes;
probe9 20/20 minus only stage-B classes. **Card:** new, from the b74
residue note ("Card separately").

### A6 — assert-forall: census rejection now, binder arm planned (small, then medium)

Short form (pre-flip, required by P2): serializer detects skolem binders
and rejects loud with an `assert-forall` tag — today these emit
non-bridging certs, the worst of both worlds. Real fix (**planned
post-flip work, not optional — §9 Q4**): a quantifier binder in the
stage-A telescope (`∀ (k : Int)` frames), so these lemmas join the
certificate. The tag is a bridge-era stopgap only; under the
verify-as-much-as-possible policy no census tag is intended to be
permanent unless the construct is genuinely outside the frontend subset.
The tag suffices for b68. **Acceptance (short):** the two
lemma_runtime_word_view fns census-reject with the tag; no non-bridging
certs emitted anywhere. **Acceptance (full):** the tag population drops
to 0 and the binder frame enters the D in-model column.

### A7 — stage-B deep-leaf growth: the vec_read class (medium)

Stage-B reference-renderer coercion derivations: the View-call deref
(`render_exp` derives `v.deref` where production writes `v`) and per-arg
spec-call coercions on CallN (`Int.ofNat` sites) need **callee signatures
in the mirror vocabulary** — a real vocabulary extension, not another
G-pattern in the deepener. This is also where P1 item 3 (reference-side
mentions-check) becomes possible if not deferred to E. **Acceptance:**
vec_read bridge-closes deep; the atom-fallback census for tgt obligations
shrinks measurably (report the before/after table).

---

## 4. Milestone B — the W4 default flip

Two bricks, existing cards:

### B1 — b67: cert + bridge caching + cost numbers

Content-keyed warm-run skip for cert emission and bridge checking (the
M5e content-compare machinery already covers bridge modules structurally;
this brick makes the *cost* story true). **Acceptance:** warm-run bridge
overhead ≈ 0 on unchanged fns; a cost table (cold/warm, fixture + tgt) in
the card; the emitter-fingerprint key from P3 lands here (same code area).

### B2 — b68: flip `--tactus-bridge` on by default in package mode

**Gate conditions (all of):**

1. P2 implemented: every honest-fail class fixed or census-tagged; the
   tag table documented; unclassified drift = hard error with the O7
   diagnostic.
2. P3 done: stmts-olean fix pinned; fingerprint in the cache key.
3. b67 cost story: warm overhead acceptable (target: gate wall-time
   within ~10% of pre-bridge warm runs).
4. A-coverage: one full tgt acceptance run where **every serializable fn
   bridges or is loudly tagged** — zero unclassified failures.

**Gate output gains:** "N obligations bridge-checked against tactus-core,
M fns census-excluded (tags: …)" — the per-run trust inventory line the
whole program exists to print.

---

## 5. Milestone D — W5 keeps pace with the mirror (standing discipline)

The soundness theorem covers the W5a–e statement family (assert/assume/
assign/call/ret/if/seq/loop/deadend, partial correctness). Every new
stage-A arm from milestone A — Match, call-mut frames, tactus
assert-query, ∀-binders — must either:

- enter the operational model + `wp_stm_sound`, or
- be **explicitly census'd out of the soundness claim** in the scope
  statement (`VERIFICATION-PATH.md` §4 rung 5's scope-honesty paragraph).

Otherwise "bridged" quietly outgrows "proven sound" and rung 5 erodes
without anyone deciding it.

**One tripwire brick (small):** the golden vir-variant coverage test
(`bootstrap_coverage.rs`) gains a second column — *in-model?* — so the
gap between mirrored and modeled is a compile-visible list, and growing
it is a reviewed decision, not an accident. Wire the rung-5 scope
paragraph to that list (doc states "the model covers exactly the
in-model column").

Expected consequences for A: A5 (Match) and A4 (call-mut frames) should
land with model extensions (W5 already has the prophecy story, so A4's
model delta may be small); A3's Assume-like form likely inherits the
Assume arm for free — say so explicitly in each card.

---

## 6. Milestone E — W8 authority flip (optional end state)

After B soaks: emitted statements become refWp's rendered output; the
production renderer is demoted to a dev-UX pretty-printer. Deletes
`lean_pp` (931 lines) from the trust inventory and the pp-drift question
with it. Also the natural home for P1 item 3 (derive the poison mark
reference-side) if A7 didn't get there first.

**Soak criterion (proposed, Danielle to confirm — §9 Q2):** bridge
default-on across the full corpus (tgt + suite + tutorial) for two
consecutive weeks of active development with zero unclassified drift
errors, before starting E. **Card:** `bootstrap-13` (todo, existing).

---

## 7. Milestone F — trust-inventory shrink (parallel, small)

Independent of the critical path; pick up in gap sessions:

- **Prelude hygiene** (closure-doc §4): definitionalize `Tactus.index`,
  `Tactus.hasResolved`; audit the `Tactus.heightLt` companions. Target
  end state: the `arch_word_bits` pair is the only tactus axiom.
- **vstd as a package**: the Boundary module shrinks to imports; the
  remaining vstd axioms become the explicit, closure-checked cross-crate
  trust surface.
- **Dual-backend differential mode**: same crate through Verus-Z3 and
  tactus, verdicts compared fn-by-fn — the standing cheap evidence for
  the frontend residue (`VERIFICATION-PATH.md` §5). The machinery
  exists; the brick is a runner + a CI-shaped report.
- `bootstrap-25` (G4 in-crate guard) stays optional; fold in if a G4
  mutation escape ever shows up.

---

## 8. Order, sizing, board mapping

| # | Item | Size | Card | Gated on |
|---|---|---|---|---|
| 1 | C — HoistEq discharge + P1 poison mutation/contract | **DONE 07-24** | b73 (closed) | — |
| 2 | A1 — b70/71 close-out | small | b70, b71 | — |
| 3 | A2 — apply_hom call-arg temps + auto-ref | small-med | new (b75) | — |
| 4 | A6-short — assert-forall census tag | small | new | — |
| 5 | A3 — tactus assert-query variant + arm | small-med | b69 | — (Q1 resolved) |
| 6 | A5 — Match arm (+ D model delta; batch churn w/ A3) | medium | new | — |
| 7 | A4 — call-mut arm (+ D model delta) | med-large | new (card first) | — |
| 8 | A7 — stage-B callee-signature vocabulary | medium | new | — |
| 9 | D — in-model tripwire column | small | new | — |
| 10 | B1 — b67 caching + fingerprint + costs | medium | b67 | — |
| 11 | B2 — b68 default flip | small | b68 | P2, P3, 1–8, 10 |
| 11b | A6-full — ∀-binder telescope arm (kills the tag) | medium | new | post-flip (Q4) |
| 12 | E — W8 authority flip | small-med | b13 | B soak (Q2) |
| 13 | F — hygiene / vstd / differential | small ×3 | new ×3 | — |

Items 2–4 are independent of each other and of 1; parallelize freely.
7 and 8 are the only real machinery arcs left in the program.

---

## 9. Open questions — all resolved 2026-07-24

Danielle delegated these to Claude's judgment with the standing
guidance: *verify as much as possible; do things the right way; no
hacks or half-way measures.* Resolutions under that principle:

- **Q1 (A3) — RESOLVED: dedicated `StmData::AssertQueryTactus`
  variant.** This reverses the earlier Assume-with-mark recommendation.
  `AssertQueryNl` is already a first-class variant, so mode symmetry
  alone argues for it; more importantly the construct's trust status
  (proven inline, not assumed) should be structural in the mirror data,
  not a side-channel bit. The extra cost is one small soundness arm and
  a cache-churning edit that batches with A5's Match variant.
- **Q2 (E) — RESOLVED: adopt the §6 soak criterion** — bridge
  default-on across the full corpus (tgt + suite + tutorial) for two
  consecutive weeks of active development with zero unclassified drift
  errors, then E may start.
- **Q3 (P1 item 3) — RESOLVED: the poison derivation lands with A7**,
  the first milestone whose vocabulary can express the reference-side
  mentions-check. A trusted bit should not outlive the first point it
  can be checked. Not a flip-blocker (the P1 mutation test covers the
  bridge era).
- **Q4 (A6) — RESOLVED: the ∀-binder arm is planned post-flip work,
  not optional.** No census tag is intended as permanent unless the
  construct is genuinely outside the frontend subset; assert-forall is
  not. The tag is scaffolding for b68 sequencing only.
