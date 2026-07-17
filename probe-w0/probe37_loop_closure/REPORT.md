# probe37 — THE LOOP CLOSURE (board bootstrap-66, after bootstrap-73)

**Status: PASS ✓** (`./run.sh`). **The W5 bootstrap loop is closed:** the
adequacy spine consumes the AUTHORED, kernel-checked
`lib.ref_wp_sound_closed` (Link module, bootstrap-73) by plain
application. The ~200-line hand-Lean `wp_stm_sound` induction and hand
`ref_wp_sound` are DELETED from the spine.

## The composition

- The spine's Val-level spec is now the authored tactus-core model
  directly: `abbrev holds := lib.holds`, `holdsAll := lib.holds_all`,
  `execSafeF := lib.exec_safe_f` (`upd` stays a computable hand twin,
  defeq to `lib.upd`, so `eval`/`bindArm` compile and the `u_holds_*`
  arm lemmas stay `rfl`).
- FACT 4:
  ```lean
  theorem soundness_concrete (E c s st)
      (hwf_s : lib.StmDataWf s) (hwf_c : lib.FnCtxDataWf c) :
      holdsAll (hpOf E) … (lib.ref_wp c s) st ↔ execSafeF … (lib.seed_frame c) s st :=
    iff_of_eq (lib.ref_wp_sound_closed … hwf_s hwf_c)
  ```
  Unifies DEFINITIONALLY — zero bridging lemmas. The two R-b wf
  hypotheses are the honest interface: serializer output satisfies them
  by construction (kernel-decidable per literal).
- Axiom closure: `soundness_concrete` = `[propext, Classical.choice,
  Quot.sound]` — pure core, no sorryAx. All v1/v2/match adequacy facts
  carry over unchanged (mostly `[propext]`, several axiom-FREE).

## Runner mechanics

The Link module ships as `.lean` only (the package gate elaborates it
in-memory) — `run.sh` copies it beside the spine and builds the olean
once (Lean requires input files under the root dir), rebuilt when the
emission is newer. Elaborates against `tactus-core/out/lib` — NO
tactus-core rebuild.

## What is now claimed (per VERIFICATION-PATH.md §5)

Kernel-checked obligations ⟹ the operational spec, end to end: user
obligations (`ref_wp c s`, read through the pinned concrete denotation)
hold ⟺ operational safety of the seed-framed program — where the
soundness proof under the spine lives in the kernel-checked package, and
only the adequacy spine (denotation/oracle pins/binder embeddings)
remains hand-Lean as the trusted SPEC — the permanent residue, by design.
