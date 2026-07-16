---
title: "W5-auth-1 — land the W5 semantic model in tactus-core (one batched cache-churning edit)"
status: done
claimed_by: fable-b61
created: 2026-07-16T17:15:00Z
updated: 2026-07-16T18:40:00Z
---

## Description

Author the W5 semantic model as tactus-core spec fns, in the shape frozen by
bootstrap-60. This is the one deliberate cache-churning edit of the authoring
arc — batch **all** model spec fns + any datatype additions into a single
commit so the tactus-core fn cache invalidates once (the N2/W6b discipline).

Contents (mirroring `DESIGN-W5-soundness.md` §2 and probes 21–24):

- Oracle params as `spec_fn` arguments (probe32-validated): leaf-holds oracle
  `hp`, let-value oracle `lv` (+ state type St per the frozen interface).
- `holdsAll : GoalList → …` (Val-level goal denotation over oracles).
- `closeSem : FrameList → St → cont → …` (FBind→forall, FHyp→implies,
  FLet→let) in the bootstrap-60 winning shape.
- `execSafeF : FrameList → StmData → St → …` — **total over all 10 StmData
  constructors** (Skip/Assume/Assert/Assign/Seq/If/Call/Ret/DeadEnd/Loop; the
  W5c frame-carrying formulation, no inFragment predicate).
- `frameDelta` + any frame-algebra spec helpers the proofs need
  (`frame_append` exists already).
- `structural_decreases` throughout; decide guards pinning kernel computation
  on a small concrete St/oracle instance (the W6b guard pattern), so a
  kernel-inert regression is caught at crate-verify time.

No soundness proofs on this card — spec fns + guards only, so the churn commit
stays reviewable.

**Done when:** tactus-core verifies `--lean-backend --lean-all-proofs` with 0
errors, axiom closures kernel-verified, decide guards pass, `out/lib`
regenerated, and the existing probe suite (probe9 16/16, probe17, probe21–26
runners) still passes against the regenerated emission.

**Blocked by:** bootstrap-60 (frozen shape).

## Progress

- (2026-07-16, fable-b61) Landed in one append-only edit at the end of
  `tactus-core/lib.rs`, per the probe33 frozen interface. First verify run:
  **98 verified, 0 errors** (was ~63), package gate "50 modules elaborated
  (48 reused); composition + axiom closures kernel-verified". No iteration
  needed.

## Writeup

**DONE — the W5 semantic model is IN tactus-core, kernel-checked.**

What landed (all at file end, append-only — no datatype touched, so the
warm cache survived: 48/50 modules reused):

- Type aliases `St = spec_fn(u64) -> int`, `HpOracle`/`HeOracle`/`LvOracle`
  (type aliases of spec_fn types emit cleanly — `Int → Int` etc.).
- `upd` (spec-closure state update), `holds` (GoalData denotation, all 5
  arms incl. LeafE), `holds_all`, `obligs_safe`, `close_sem_e` +
  `close_sem_obligs` (the two DEFUNCTIONALIZED telescope interpretations —
  probe33 frozen decision: no ContK, no higher-order continuations),
  `exec_safe_f` (frame-carrying, TOTAL on all 10 StmData constructors,
  transcribed from probe24 with Loop's mframe/endf via let).
- 28 st-generic `u_*` one-step unfold pins (closer `first | tactus_auto |
  (intros <;> rfl)`), covering every arm of every new fn — these both pin
  kernel-clean emission per arm and are the rewrite rules the soundness
  proofs consume (∀st-equations usable under binders, probe33 F2).

Notes for bootstrap-62..64:
- Struct-literal Loop/Call in ENSURES works (u_esf_loop / u_esf_call are
  the precedent alongside the older stm_size pins).
- `exec_safe_f`'s Loop arm conjunction is Rust left-assoc (probe24's Lean
  groups right) — the discharge closer carries [and_assoc], so this is
  cosmetic, but the u_esf_loop equation is the authored truth.
- Plan note: 62/63 should land the SUPPORT lemmas (holds_close_e /
  holds_all_append; then the close_each_e ↔ close_sem_obligs bridge), and
  64 lands the one total `wp_stm_sound` induction — all ingredients exist
  by then, so no fragment scaffolding is ever needed.
