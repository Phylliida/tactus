---
title: "W7 residual — obligation-position multi-arg call: live refWp bridge over raw_exp CallN"
status: done
claimed_by: opus-w7-appn-oblig
created: 2026-07-14T11:30:00Z
updated: 2026-07-14T11:40:00Z
---

## Description

Close the one honest residual left by `bootstrap-34` (multi-arg AppN/CallN):
the SST `raw_exp` `CallN` arm (`sst_serialize.rs` L708) is currently exercised
only by the DEF bridge (VIR `raw_vir_exp`, validated live by probe17). Its own
obligation-position path — `oblig_slot` → `raw_exp` on an ensures/invariant/
assert whose expression contains a `>= 2`-arg spec-fn call — has **no fixture
site**, because every fixture obligation with a call uses a single-arg callee
(`tri(1)` in `tri_one`, `tri(i)` in `sum_to` invariants).

`tri_one` already PROVES the mechanism for the single-arg `Call` arm: its
ensures `tri(1) == 1` emits `RawExp.Call 2 …` inside `cert_tri_one_sst`, and
**probe9_bridge** builds the real refWp obligation bridge over it:
`goals_eq (ref_wp ctx sst) goals = 1 := by decide`. That bridge exercises
`render_exp`'s `Call → App` mapping and compares against production's
`lexpr_to_exprdata` App. The `CallN → AppN` path needs the identical treatment.

**Done when:**
- a fixture proof fn with a `>= 2`-arg call in its ensures (analog of `tri_one`)
  emits a `.cert.lean` whose `cert_<fn>_sst` contains `RawExp.CallN`;
- `probe9_bridge` closes the refWp bridge over it (`close-ok`), i.e.
  `goals_eq (ref_wp …) … = 1 := by decide` elaborates rc=0, and every other
  fixture cert stays `close-ok` (no regression);
- (bonus) a 3-arg case too, to cover `RawList` length 3 in obligation position.

## Progress
- (2026-07-14, opus-w7-appn-oblig) Claimed. Read the two-layer cert
  architecture: `emit_cert` (`<fn>.cert.lean`, obligation/WP layer via
  `oblig_slot`→`raw_exp`) vs `emit_def_cert` (`.defcert.lean`, defs layer via
  `raw_vir_exp`). probe17 covers only defs; **probe9_bridge is the obligation
  refWp bridge** and is where this residual gets live coverage. Confirmed
  `tri_one.cert.lean` L27 already carries a single-arg `RawExp.Call` in an
  obligation slot and probe9 bridges it. Plan = mirror `tri_one` for a 2- and
  3-arg callee (`g2`/`g3`, already in the fixture), re-emit, run probe9.
- (2026-07-14, opus-w7-appn-oblig) **DONE.** Added `call_g2_ob`/`call_g3_ob`
  proof fns (F21) to `bootstrap-fixture/lib.rs` — empty bodies, ensures
  `g2(x,y)==x+y` / `g3(x,y,z)==x+y+z` (`open spec fn` ⟹ unfolds definitionally,
  no tactic). Re-emit (`--tactus-emit-cert`, NO serializer rebuild — fixture-only
  change): 23 verified/0 errors (was 21), 28/36 certified. `call_g2_ob.cert.lean`
  L26 now carries `RawExp.Span 6 (BinOp Eq TyBool (CallN 5 TyNat [Var 0, Var 2])
  …)` — the widened `raw_exp` CallN arm live in an obligation slot; goal L33 has
  the matching production `AppN 5 [Atom 0, Atom 2]`. **probe9_bridge: both new
  fns `close-ok` on decide AND rfl, all 14 pre-existing fixtures unregressed**
  (ALL BRIDGES BEHAVE AS CLASSIFIED ✓). probe17 (def layer) still green after
  re-emit. **Non-vacuity kill:** swapped the goal's `AppN` arg order
  (`[Atom 0,Atom 2]`→`[Atom 2,Atom 0]`) → `decide` PROVES `goals_eq (ref_wp …)
  goals = 1` is FALSE (rc=1), positive stays rc=0. Arg-ORDER is load-bearing,
  which only bites with ≥2 args ⟹ a multi-arg-specific non-vacuity proof.

## Writeup
**DONE — the SST `raw_exp` `CallN` arm now has a live, non-vacuous obligation
refWp bridge; `bootstrap-34`'s honest residual is closed.**

**What landed (1 tracked file):** `bootstrap-fixture/lib.rs` F21 —
`call_g2_ob(x,y: nat) ensures g2(x,y)==x+y` and
`call_g3_ob(x,y,z: nat) ensures g3(x,y,z)==x+y+z`, both empty-bodied proof fns.
The serializer (`sst_serialize.rs`) is UNTOUCHED — the CallN arm landed in
`bootstrap-34` (d3349be); this card only adds fixture SITES that drive it into
an obligation slot.

**How it works.** `bootstrap-34` validated the multi-arg `CallN`→`AppN` render
only through the DEF bridge (VIR `raw_vir_exp` → `render_def`, probe17). The
OBLIGATION path is a different serializer entry: `emit_cert` → `oblig_slot(e)`
→ `raw_exp(e)` for each ensures/invariant/assert `e`. `tri_one` already drives
the SINGLE-arg `Call` arm this way (`tri(1)==1` → `RawExp.Call` in
`cert_tri_one_sst`), and **probe9_bridge** builds the real refWp obligation
bridge over every cert: `goals_eq (ref_wp ctx sst) goals = 1 := by decide`,
which runs `render_exp` over the SST obligation (mapping `CallN`→`AppN`) and
compares against production's `lexpr_to_exprdata` goal. A ≥2-arg call in an
ensures was the one shape no fixture obligation had. F21 supplies it: the
emitted `cert_call_g2_ob_sst` carries `RawExp.CallN 5 TyNat (RawList[Var 0,
Var 2])` inside the deep `RawExp.Span` obligation slot, and the emitted goal
carries production's `ExprData.AppN 5 (ExprList[Atom 0, Atom 2])` — same interned
fn id (5), flat arg order — so the bridge closes by construction, exactly as the
def bridge does.

**Verification.**
- Re-emit: `TACTUS_LEAN_OUT=… verus --lean-backend --emit-lean --lean-all-proofs
  --tactus-emit-cert bootstrap-fixture/lib.rs` → 23 verified / 0 errors, 28/36
  certified (the +2 over 21 are the new proof fns; empty bodies verify because
  `g2`/`g3` are transparent `open spec fn`s).
- probe9_bridge (obligation refWp bridge): `call_g2_ob`, `call_g3_ob` →
  `close-ok` on both `decide` and `rfl`; all 14 other fixtures unregressed.
- probe17_w7d_live (def bridge): 8/8 def+dt certs still positive OK + kills
  non-vacuous (no def-layer perturbation from the re-emit).
- Non-vacuity kill (manual, mirrors probe17's discipline): perturb the goal's
  `AppN` arg order → `decide` proves the `= 1` bridge FALSE; correct order
  closes rc=0. The RawList/ExprList element ORDER is load-bearing — a property
  that only distinguishes ≥2-arg calls, so this is genuinely testing the CallN
  spine, not just the fn id (which the single-arg arm already covered).

**Assumptions/limits (honest).**
1. The obligation exercised is an ensures (`Return`-goal position). Invariant/
   assert positions route through the SAME `oblig_slot`→`raw_exp`→`CallN` arm,
   so they are covered by the same code path, but F21 does not add a call inside
   a loop invariant or a bare `assert` — a further belt-and-suspenders site if
   ever wanted (low value: identical arm).
2. `--emit-lean` skips the Lean goal discharge, so the *frontend* verification
   of `call_g2_ob`/`call_g3_ob` was via the SST-level 23 verified/0 errors, not
   a full-Lean run. The obligation bodies are empty and the ensures are
   definitional identities, so this is verification-neutral for the e2e gate.
3. As always the serializer is the TCB (stage-A scope, per the cert header);
   this bridges statement ASSEMBLY of the multi-arg obligation, not leaf
   rendering adequacy (W5/W6 caveats unchanged).
