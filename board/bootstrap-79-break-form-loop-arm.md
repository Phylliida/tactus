# bootstrap-79 — break-form loop arm (loop_normalize cert-lane debt)

Status: **card — step-0 evidence frozen 2026-07-28, design DIRECTION
frozen, full design freeze + implementation not started.**
Unblocks: b78 S5 (call-mut census retirement on tgt via
`runtime.copy_word`) + `runtime.find_cancellation_exec` cert return
(A7 tripwire set). Sequencing decided by Danielle 2026-07-28: **this
arm BEFORE A7.**

Subjects: `runtime.copy_word` (loop + cond-setup `v.len()` call +
in-loop mut call `out.push(v[j])` + AQT asserts — the composition
subject) and `runtime.find_cancellation_exec` (loop + cond setup +
early `return i` in body). Fixture: needs a minimal break-form
subject (call-in-cond while, e.g. `while i < v.len()` over a
`&Vec<u64>` param) — none exists today; all fixture loops have
local-pure conds (`sum_to`, `fill_zeros`, `count_down`), which is why
the 4th sync's probe battery never saw this class.

## Background (what the 4th sync changed)

Main's audit arc added `loop_normalize::normalize_setup_loops`
(lean_verify), which rewrites every `while` with a NON-EMPTY cond
setup (`StmX::Loop { cond: Some((setup, exp)), .. }`) into break-form:

```
loop { <setup…>; if !exp { break; } <body…> }
```

with the original `(setup, exp)` kept on the Loop node as
`original_cond`. Production's `build_wp_loop` builds goals from
`original_cond`; the exit continuation is wrapped with the
`setup; ¬exp` exit facts (re-checked via
`count_breaks_targeting_this_loop == 1`). The serializer
(`sst_serialize.rs:4320`) applies the same pre-pass and then walks —
and its stage-A stm walk rejects `StmX::BreakOrContinue` loud
(`break-or-continue` census tag, pre-existing arm, previously
population 0 on tgt). Result (b78 S5 run, `9bf4a32`): copy_word +
find_cancellation_exec census-reject before the Call arm;
find_cancellation_exec LOST its b77-era cert.

## Step-0 evidence (frozen 2026-07-28, from the live S5 emit)

Source: `probe-w0/probe11_w3_tgt/out/lib/runtime__copy_word.lean`
(production emission, 935 lines) vs
`bootstrap-fixture/out/lib/pkg/lib__sum_to.lean` (classical
empty-setup while, bridge-CLOSE today).

### E1 — theorem census: the break-form has THREE invariant phases, classical has TWO

copy_word (ids): entry `2,3,4` — [5 = cond-setup `v.len()` fresh_ret
gensym] — **`6,7,8`** — [9 = `vec_index` fresh_ret; 10 = push
precondition; 11,12 = push mut gensyms; 13,14 = user AQT asserts;
15 = j-increment] — **`16,17,18`** — 19 decrease — [20 unaccounted,
find at impl] — 21 postcondition.

sum_to (ids): entry `1..4` — body asserts `5,6` — second invariant
set `7..10` — 11 decrease — 12 postcondition. TWO sets only.

Conclusion: the break-form SPLITS what the classical loop merges —
one of the two new sets is the exit re-close (`inv_obligs_exit`)
becoming non-coincident with maintain. Phase identification (from
telescope contents, E2/E3): **`6,7,8` = exit re-close** (needs no
body walk, emits early; carries ¬cond) and **`16,17,18` = maintain**
(emits after the body theorems; carries the body WP inline).

### E2 — exit-phase goals carry `setup; ¬exp` as HOISTED BINDERS

Exit re-close `_tactus_loop_invariant_..._445_13_6` telescope:

```
(v) (tmp__1) (_h_hoist_1 : view tmp__1 = empty)      -- pre-loop frames
(out) (j) (_h_hoist_2 : bounds) (_h_hoist_3/4/5 : invariant clauses)
(tmp__3 : Nat) (_h_tmp__3_hoist1 : tmp__3 = j)       -- setup let (cond lhs temp)
(_h_hoist_6 : 0 ≤ spec_vec_len v ∧ · < usize_hi)     -- setup call BOUND hyp
(tmp__2 : Nat) (_h_tmp__2_hoist1 : tmp__2 = spec_vec_len v)  -- setup call dest
(_h_hoist_7 : ¬(tmp__3 < tmp__2))                    -- ¬cond
leaf: <invariant clause>
```

The postcondition `_21` carries the SAME hoisted setup + ¬cond frame
run (then the return-value binder). So: exit-side goals = ordinary
hoist-mode frames — the b74 dual-mode machinery already renders this
vocabulary; the CONTENT (setup frames incl. a call's bound hyp +
ret-eq) is the Call/Assign arms' existing output.

### E3 — maintain goals carry the setup + cond INLINE in the goal body

Maintain `_16` telescope = havoc binders + invariant hyps ONLY (stops
at `_h_hoist_5`); the goal BODY opens:

```
let _tactus_d_old_0_0 := spec_vec_len v - j;   -- decreases old (inline let)
let tmp__3 := j;                                -- setup lets (inline)
0 ≤ spec_vec_len v ∧ · < usize_hi →             -- setup call bound (imp)
(let tmp__2 := spec_vec_len v; …                -- setup call dest (inline let)
```

i.e. maintain = WRAP-MODE rendering (FLet/FHyp inline in the prop),
with the positive cond expected deeper in the wrap (confirm exact
position at impl — the line truncates). The exit side being hoisted
while maintain is inline mirrors production's per-goal-type mode
selection; the mirror must reproduce BOTH placements.

### E4 — id-consumption discipline (E5 of b78 applies here too)

The cond-setup call consumes a fresh_ret id (5) between entry and
exit-re-close — a new row for the serializer's emit-counter contract
table (loop entry: +1 per cond-setup CALL). The exit-phase setup
replay reuses the SAME temp names (tmp__2/tmp__3 in both maintain and
exit goals) — no fresh ids there. Id 20 (between decrease 19 and
postcondition 21) is unaccounted — identify at impl (likely the
post-loop/return-path gensym).

## Design direction (frozen)

**D1 — NO Break arm. Mirror the loop at the `original_cond` level.**
The break-form is a canonical encoding: the normalized Loop node
carries `original_cond = (setup, exp)` and a body of exactly
`[setup…, If(¬exp, [break], _), body…]`. The serializer's Loop arm
pattern-matches THIS shape (anything else with BreakOrContinue keeps
the loud `break-or-continue` tag — genuine user break/continue has no
corpus population and stays rejected), recovers `(setup, exp, body)`,
and assembles the three goal families per E1–E3. The setup stms are
ordinary Assign/Call content — the existing stm walk + Call arm
(incl. b78's mut machinery, for `while f(&mut x)` conds) transcribes
them.

**D2 — vocab growth on the existing `StmData::Loop` node, not a new
arm.** The node already carries `inv_hyps / inv_obligs /
inv_obligs_exit / binders / binder_bounds / cond_name / cond_ann /
neg_cond_ann / d_old_* / decrease_oblig / body`. Add a setup slot
(transcribed setup as mirror stms — reference-side frame derivation
per the b78-D2 philosophy, NOT serializer-written frames). refWp's
Loop arm splices the setup frames at the three positions (exit-reclose
hoisted / maintain inline wrap / continuation hoisted), reusing the
b74 dual-mode close functions. Classical loops get the empty setup —
byte-stability for sum_to/fill_zeros/fill_probe certs is the churn
check.

**D3 — W5 churn unknown until impl; hope is dispatcher-level.** The
S3-pre payoff (wp_stm_sound holding at dispatcher level when frame
concat stays generic) is the precedent. If the Loop soundness arm
must open, scope it then; the in-model tripwire column (endgame D)
gains the setup-frame rows either way.

## Open questions (resolve at design freeze, BEFORE impl)

1. sum_to's cert: how do `inv_obligs` vs `inv_obligs_exit` populate
   for a classical empty-setup loop — is exit re-close elided, or
   coincident-by-content with maintain? (Determines whether the
   break-form's extra goal set is a new FIELD or a mode of an
   existing one.)
2. Maintain inline wrap exact structure: cond imp position, d_old let
   placement relative to setup lets, how the body WP nests (E3's
   truncation).
3. Id 20 (pre-postcondition) identity.
4. Does the exit re-close set appear at all for empty-setup
   classical loops (tie to Q1)?
5. Whether the exit-phase setup frames derive from `original_cond`'s
   setup or the body copy — evidence says same names; confirm the
   serializer needs only one transcription.

## Acceptance

- Fixture gains a minimal break-form subject (call-in-cond while);
  its cert emits and bridge-CLOSES (probe9), with mutation kills on
  the new setup-frame channels (probe13).
- `runtime.copy_word` + `runtime.find_cancellation_exec` certs emit;
  probe11 population pin fires SUBJECT-RETURNED → classify (copy_word
  predicted A7-class honest-fail per b78 §5; find_cancellation_exec's
  dormant A7 reason reactivates).
- b78 S5's acceptance (`call-mut` census tag → 0 on tgt) finally
  verifiable.
- `break-or-continue` census tag population back to 0 on tgt (genuine
  user break/continue would still tag loud).
- Churn: classical-loop certs byte-identical; W5 gate + Link discharge
  hold.
