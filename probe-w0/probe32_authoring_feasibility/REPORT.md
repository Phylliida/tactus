# probe32 — W5 loop-closure AUTHORING feasibility

**Board:** bootstrap-59. **Date:** 2026-07-14.
**Run:** `probe-w0/probe32_authoring_feasibility/run.sh` (real tactus binary,
`--lean-backend --lean-all-proofs`, isolated scratch crate, no tactus-core rebuild).

## Why this probe exists

The W5 soundness ladder is proven as **hand-Lean probes** (probe21..31) over the
emitted `lib.*` defs. Genuine **loop closure** (DESIGN-W5-soundness §0, §4) requires
*authoring* that soundness as Rust spec/proof fns **inside tactus-core**, verified by
the tactus binary (routed to Lean) and emitted as a kernel-checked package.

But tactus-core today contains **zero `spec_fn`-typed params** and **zero recursive
proof fns** — every one of its proof fns is a closed `by { decide }` bridge. So loop
closure had two untested mechanism questions, which this probe answers by porting a
**stripped** `wp_stm_sound` (probe21) — the mechanism spine minus the frame machinery
(whose soundness the hand-Lean already proved):

- **Q1** — does the Verus→Lean backend accept a **`spec_fn` leaf oracle** param (the
  valuation-parametric model, DESIGN-W5 §1 option b) in spec fns AND proof fns, and
  emit it kernel-clean?
- **Q2** — can it author a **recursive structural-induction `proof fn`** (the analog of
  `wp_stm_sound`) with a recursive helper lemma?

## Result

### Q1 — CONFIRMED (the crux). `spec_fn` oracle + recursive spec fns author + verify + emit clean.

`8 verified` in the run:
- The 4 oracle-parametric recursive `open spec fn`s — `gappend`, `all_true(hp, ·)`,
  `wp`, `exec_safe(hp, ·)` — where `hp : spec_fn(u64) -> bool` is the leaf oracle.
  The backend translates `spec_fn(u64)->bool` to Lean `Int → Prop` and emits the
  recursive defs (structural, over `Box`-nested own datatypes) with a clean axiom
  closure. **This was THE feasibility unknown for loop closure and it is positive:
  the valuation-parametric leaf-oracle semantics is expressible in tactus-core.**
- The 4 one-step **unfold lemmas** `u_gappend_nil/cons`, `u_all_true_nil/cons`
  (empty-body `proof fn`s whose `ensures` is a single constructor-unfold equation)
  — they verify, i.e. the default closer `tactus_auto` **does** discharge an isolated
  one-step unfold of a recursive `open spec fn`.

### Q2 — SOLVED. The recursive structural-INDUCTION proof fns verify kernel-clean.

Verus accepts the recursive structural-induction `proof fn` shape: it generates the
per-arm VCs, and (with `#[verifier::structural_decreases]` on the proof fn) discharges
the **height-decrease termination VC**, and threads the **induction hypothesis** into
the Lean context correctly. `all_true_append` (recursive append lemma), `wp_sound` (the
soundness induction, analog of probe21's `wp_stm_sound`), and `wp_sound_bites` (the
non-vacuity witness) all verify. **The full run is `19 verified, 0 errors`, and the
three top-level soundness postconditions have axiom closure `[propext]` only** — no
`sorryAx`, no `Classical.choice`, no stray axioms.

**The discharge idiom (the deliverable):**

```
#[verifier::tactus_tactic("first | tactus_auto |
   (intros <;> tactus_case_split (simp_all (config := { zetaDelta := true }) [and_assoc]))")]
```

Three ingredients, each necessary (found by direct-`lean` iteration on the emitted VCs):

1. **`config := { zetaDelta := true }`.** After `intros`, the unfold equalities the body
   established (via the `u_*` lemma calls) are `let`-bound LOCAL Props — `h : tmp__k`
   where `tmp__k := (… = …)`. Plain `simp_all` zeta-reduces `let`s *in the goal* but does
   NOT unfold local let-*fvars*, so it never sees `h` is an equation and reports "made no
   progress". `zetaDelta` unfolds those local defs so `simp_all` can rewrite with them.

2. **`tactus_case_split` (a real `cases s`), NOT an `s == Ctor(..)` bridge assert.** With
   `zetaDelta` on, a bridge hyp `a = Cons g t` (where `g := a.Cons_val0`) is self-
   referential — `simp_all` rewrites `a ↦ Cons a.Cons_val0 …` forever → **maxRecDepth**.
   Dropping the bridge instead leaves the unfold hyps carrying opaque `match a with …`
   projection terms that simp can't concretize → **unsolved goal**. `tactus_case_split`
   (prelude: it runs `cases` on each user-datatype-typed local, committing the branch
   whose closer discharges all subgoals) replaces `a`/`s` with a *fresh* constructor
   `Cons g' t'` — proper substitution, no self-reference — so the `u_*` unfold hyps and
   the IH apply, and the impossible arm (e.g. `Nil` under `¬isNil`) dies by contradiction.

3. **`[and_assoc]`.** After the rewrites, the residual is pure re-association,
   `A ∧ (B ∧ C) ↔ (A ∧ B) ∧ C`; `simp` does NOT normalize `∧`-nesting by default, so
   `and_assoc` is added explicitly. (`wp_sound_bites` has no datatype local, so its
   closer omits `tactus_case_split`: `first | tactus_auto | (intros <;> simp_all
   (config := { zetaDelta := true }) [and_assoc])`.)

The attribute (`source/lean_verify/src/sst_to_lean.rs`, `attributes.rs`) overrides the
closer for every VC of the fn; `first | tactus_auto | …` keeps the default closer for the
atomic sub-goals and only falls through to the custom closer for the compound
postcondition. This is the same shape the corpus already uses
(`tactus-group-theory/src/runtime.rs:376`).

**Body scaffolding is the transparent T1 partner.** The height-recursive spec fns
(`wp`/`exec_safe`/`all_true`/`gappend`) get **no** Lean equational lemmas — Lean can't
generate `.eq_def` for tactus's `Stm.rec_1` structural-recursion encoding, and the `u_*`
proof fns are emitted only as VC obligations, not as reusable `lib.u_*` simp lemmas. So
each per-constructor unfold is injected into the VC context by a **lemma CALL** in the
body (`u_wp_seq(a,b); u_exec_safe_seq(hp,a,b); all_true_append(hp, wp(*a), wp(*b));
wp_sound(hp,*a); wp_sound(hp,*b)` for the `Seq` arm). This is exactly probe21's
`simp only [named u_* lemmas]` idiom, expressed at the Rust-source level — the closer
then does multi-hyp substitution over those hyps.

## Bottom line for loop closure

- **The math is done** (hand-Lean probe21..31).
- **The hard authoring unknown is resolved positive** (Q1): tactus-core CAN carry the
  `spec_fn`-oracle valuation-parametric recursive semantics with a clean axiom closure.
- **The discharge idiom is nailed** (Q2): recursive-induction soundness proofs
  (`all_true_append` + `wp_sound`) close **kernel-clean** (`[propext]` only) inside a real
  `--lean-all-proofs` tactus run, via the per-fn `tactus_tactic` above + per-arm `u_*`
  unfold-lemma calls in the body. **No open feasibility question remains** for authoring
  W5 soundness in tactus-core: scaling to the real `wp_stm_sound` + its frame lemmas is
  the (now mechanism-known) authoring work under bootstrap-10.

## Files

- `lib.rs` — the probe. `Stm`/`GList` mirror datatypes; `gappend`/`all_true`/`wp`/
  `exec_safe` oracle-parametric spec fns; `u_gappend_*`/`u_all_true_*`/`u_wp_*`/
  `u_exec_safe_*` one-step unfold lemmas (all verify); `all_true_append` (recursive append
  lemma) + `wp_sound` (structural-induction soundness) + `wp_sound_bites` (non-vacuity) —
  all discharged by the idiom above.
- `run.sh` — pass/fail gate: re-emits + verifies; PASS == `0 errors`.
- `out/lib/pkg/lib__*.lean` — the emitted VCs (read these to see the IH threading and the
  discharged closer).
