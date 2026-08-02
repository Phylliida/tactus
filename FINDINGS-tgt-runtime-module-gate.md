# FINDINGS — tgt runtime-module gate red (diagnosed + defs layer fixed) — 2026-08-02

Triggered by the b67 cost measurement: `verus --lean-backend --crate-type=lib
tactus-group-theory/src/lib.rs --verify-module runtime -V cache` (scoped per
Danielle's no-full-tgt-gates constraint) was RED with 11 errors under the
worktree binary. First action: bifurcate — IDENTICAL error set under tgt's own
blessed binary (`tactus/source` @ e018b69), so NOT a bootstrap-lane regression.

## Timeline (established)

- 2026-07-17 13:50: last recorded GREEN full tgt gate (3116/0, commit e05a0c4).
- 2026-07-19: mainline N3-M0/M1/M2 (script IR + forms) + b74 slice day; a tgt
  run at 13:37 left a pkg .lean with NO olean (already red mid-transition).
- 2026-07-21: cb1ebc4e "N3: every decreasing_by arm named (TERM_SIMP_LEMMAS)"
  — bare `simp_all` → `simp_all only [TERM]` in all termination templates.
- 2026-07-26: 4th sync arc (loop_normalize etc.). No full tgt gate since
  07-17 (probe11 = scoped --emit-lean, no defs elaboration; Danielle's
  constraint). The drift accumulated silently.

## Root causes found + FIXED (commit 00827513, worktree)

All in the decreasing_by/mono-companion generation; latent since the
mainline-10/N3 named-simp arcs; unmasked one module at a time as each was
fixed (word_numbering → ii_subset → m1_guard → m3_blinker; `finite`'s
`Option.isSome` error was ladder-fallback cascade noise from the same roots):

1. **Ctor mis-classification** (`collect_arg_signals`): `<Type>.mk`
   (`KPWord.mk`, `Ref.mk`, `Box.mk`) passed the lowercase check and was
   treated as a suffix fn, so a ctor-wrapped `drop_first` in a self-call arg
   set `nested_suffix` → ii_subset's `kp_value` mis-dispatched to the
   Chaining rung (foreign `m3_blinker` mono) instead of direct
   `drop_first_len_lt`. Fix: `.mk` with uppercase penultimate segment = ctor.
2. **Dite-encoded Prop-connective guards**: `∨`/`∧` guards elaborate through
   decidable instances into dite-form context hyps the named TERM set can't
   decompose (`h : ¬if x : c then True else P` / `h : if h : c then P else
   False`). `simp_all?` named the minima: TERM_DITE_OR
   (`dite_eq_ite, if_true_left, not_imp, Nat.not_le, not_false_eq_true` — the
   last for the self-rewrite-to-`¬False` wall at `¬len W = 0` goals),
   TERM_DITE_AND (`gt_iff_lt, dite_eq_ite, if_false_right`). Wired into a
   shared `companion_close_tail()` across
   SeqSubrange/SeqDropFirst/SeqDropLast/Chaining/Ladder templates + an inline
   Div leg (positive-goal variant, no `not_false_eq_true`).
3. **Mono-companion template** (`fun_induction` proof of
   `drop_base_run_len_le`): same dite family across its four case shapes —
   TERM_DITE_PROP union leg.

Result: **the entire tgt defs layer elaborates again** (scoped module gate;
the defs ladder no longer falls back to standalone — 1m37 vs 5m+). Battery:
units 432+7/0, tactus-core gate 291/0 + 54 + discharge 198/0 (bridge re-ran
live 166/166 — emitter-fingerprint invalidation working as designed), probes
9/11/13/14/17/37/38 ✓, fixture golden byte-stable, vstd 1531/0, e2e (see
commit log).

Known residue of the dite-leg design: ~1 `unusedSimpArgs` warning per
connective-guard site (the wrong-shape leg's `dite_eq_ite` fires before the
right-shape leg closes; unavoidable with shape-split legs — each warning is
honest documentation of which leg fired; zero would require per-site sets).

## Residual: 11 errors in 3 recursive proof fns (N3 script-form class)

`lemma_inverse_word_element` (6), `lemma_runtime_word_view_subrange` (3),
`lemma_runtime_word_view_append` (2). Error text now reads "Lean tactic
failed" (the script-form path). These are N3-M2 script-author mismatches on
the fns' obligation shapes — established facts:

- Termination VC (runtime.rs:358:13): goal
  `0 ≤ len rest ∧ ↑(len rest) < decrease_init0 ∨ (↑(len rest) = decrease_init0 ∧ False)`
  with `rest = drop_first w`, `decrease_init0 = Int.ofNat (len w)`,
  `¬len w = 0` in context, and `axiom_seq_subrange_len` as a context `have`.
  Provable, but the conditional rewrite's side condition `(1:Int) ≤ ↑(len w)`
  does not discharge from `¬len w = 0` via any simp lemma chain I found
  (omega closes the side condition but simp's discharge doesn't call omega);
  the formA leg (`subst; simp only [drop_first]; assumption|omega|rfl; split`)
  has no instantiation move for the context axiom. Also note the goal shows
  `↑`/`Int.ofNat` as two atoms to omega in one counterexample.
- runtime.rs:361:20: `apply axiom_seq_add_index2` against a non-add-shaped
  goal (`index w (↑len w - 1 - k) = index rest (↑len rest - 1 - k)`) — the
  script's axiom leg doesn't match the goal shape (needs the subrange-index
  rewrite + the same length bridge).
- word_view_subrange (532:12): `apply array_len_matches_n` against
  `len rhs = len lhs` — wrong-axiom leg. (534:16): `@Eq.symm` unify failure.
- word_view_append (518:20): `@Eq.symm` against a `let`-wrapped goal
  (`let ab := ...; let lhs := ...; let rhs := ...`) — zeta-wrapping blocks
  the apply.

Paths forward (Danielle's call):

- (a) N3 script-author work: a `have`-instantiation move for context axioms
  (the `have _tactus_bc_*` family is right there), and/or leg-set coverage
  for the let-wrapped/length-bridge shapes. This is the derivation-first
  arc's home turf.
- (b) fn-level overrides (S2c precedent, `#[verifier::tactus_tactic(...)]`)
  for the 3 fns — sanctioned residue path, but couples to emitted hyp names
  and adds 3 bespoke scripts.

**Danielle 2026-08-02: HOLD on the class-3 fixes** — they will be
addressed by the Z3-tactic-recreation arc (nonlinear etc., in a
different branch). The tactus-side bugs in this class are still worth
fixing eventually (the script-author gaps above are real machinery
gaps, just not urgent).

## Port note

Fixes live in `tactus-bootstrap/source` (commit 00827513). tgt's check.sh
binary (`tactus/source`, main @ b38eabb2) has the same bugs — port/sync
needed before tgt gates go green anywhere. Mainline owners of the touched
files: `to_lean_fn.rs` (decreasing dispatch + templates), `tactic_select.rs`
(named sets), `generate.rs` (mono-companion template).
