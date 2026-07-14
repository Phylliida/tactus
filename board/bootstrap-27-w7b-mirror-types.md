---
title: "W7b — land the frozen defs-layer vocabulary in tactus-core (one batched cache-churning edit)"
status: in_progress
claimed_by: opus-w7b
created: 2026-07-14T23:00:00Z
updated: 2026-07-14T14:20:00Z
---

## Description

The ONE batched `tactus-core/lib.rs` edit for W7 (the W6b discipline, bigger
batch). W7a (`bootstrap-26`) **froze the exact shapes** — see
`probe-w0/probe15_w7a_defs/probe15_w7a_defs.lean` (the Lean mirror) +
`REPORT.md` §"The frozen extended vocabulary". Land them additively so the
base-hash change / whole-crate re-verify / olean re-emit happens **once**.

Concretely, extend `tactus-core/lib.rs`:

1. **`TypData` += `TyBox(u64)`** — Box<T> field type, DISTINCT from `TyRef`
   (§7 Q4 verdict). Extend `td_tag` (new tag 5), `deref_type` (`TyBox inner →
   TyNamed inner`).
2. **`ExprData` += `Ite` / `Match` / `AppN` / `Forall` / `Exists`.** `Match`
   needs `MatchArm(u64 ctor, <binder-id list>, ExprData body)` + an `ArmList`;
   `AppN` needs an `ExprData` list. Mirror production's dedicated-list
   discipline (like `RawExpList`), NOT `Seq`/`Vec` — keep it structural so
   `decide` reduces (W7a proved this reduces with no `WellFounded.fix`).
   Extend `ed_tag` + the tag/projection accessors, `expr_size` (arm-list
   recursive → needs its own structural measure), `expr_eq` (+ `arms_eq`, the
   one novel equality — match first arg, tag+projection on the second; W7a's
   `Q1_arms_eq_*` is the template).
3. **`RawExp` += `Ite`/`MatchR`/`CallN`/`ForallR`/`ExistsR`** (matchR/callN
   carry a result `TypData`). Extend `type_of`, `render_exp` (arm-body /
   ite-branch coercion via `needs_nat_coercion`, parallel to `BinOp`; quantifier
   + AppN pass-through). No `HasType` addition (already present; not a body
   construct).
4. **New top-level mirrors:** `DefData`/`RawDef` (name, typed params, ret,
   body), `DtData`/`CtorData`/`RawDt`/`RawCtor` (positional field types),
   `render_def`, `render_dt`, `def_eq`, `dt_eq`. Params carry `TypData` (a wrong
   param type is a real bug — not the opaque-`u64` `BinderList`).
5. **Keep probe9/13/14 green** + re-emit oleans. Add an in-crate
   `defs_mirror_kernel_computes` proof fn (the analog of
   `expr_mirror_kernel_computes`) pinning the W7a cases against the LANDED
   `render_def`/`render_dt`/`def_eq` — `tri`(Ite), `tree_head`(Match),
   `Tree.height`(self-recursive Match), the `Tree` `DtData`, each correct=1 +
   a mutation=0.

**Done when:** the extended vocabulary is in `tactus-core`, the crate
re-verifies (0 errors), oleans re-emit, probe9/13/14 stay green, and the
in-crate kernel-computes guard pins the W7a cases against the landed code.

**Blocked by:** `bootstrap-26` (W7a) — **DONE, shapes frozen.** UNBLOCKED.
**Blocks:** W7c (serializer transcriptions), W7d (wire into def emission +
bridge), W7e (mutation-kill).

## Progress

- (2026-07-14, opus-w7a) Created as the W7a hand-off. Shapes frozen in
  `probe15_w7a_defs.lean`; the Lean mirror is a near-1:1 template for the Rust
  enums (translate `inductive`→`enum`, `List Nat`→a binder-id list type, the
  mutual list inductives→`Box`-nested `enum`s like `RawExpList`).

- (2026-07-14, opus-w7b) **CLAIMED + DE-RISKED the mutual-recursion crux before
  touching the shared crate** (the W7a "de-risk the novel mechanic first"
  discipline). The whole W7b edit rests on Verus accepting a MUTUAL
  `structural_decreases` render/eq/size across the `ExprData ↔ ArmList` Match
  cycle — but `tactus-core/lib.rs:12-17` explicitly says
  `structural_decreases` covers ONLY single-fn recursion, and W7a only verified
  the LEAN side (hand-written `mutual`), not the Verus emission. Ran two
  standalone Verus probes (`tactus-core/probe_mutual{,2}.rs`, fork verus
  `--lean-backend --lean-all-proofs`, out in `out_probe{,2}/`). **Final probe:
  6 verified, 0 errors, package gate kernel-verified.** Four real gotchas found
  — each would have broken the batched edit mid-way (cache re-churn):
  1. **✅ Verus DOES accept mutual `structural_decreases` across nested
     datatypes.** The preamble's "single-fn only" note is conservative/stale.
     Emits `termination_by structural`, kernel-reduces under `decide` (mutual
     `expr_size` AND mutual `expr_eq` both confirmed, `#print axioms` clean).
  2. **⚠ Single-variant enums are the trap.** A single-variant Rust enum
     (`enum Arm { Arm(..) }`) lowers to a Lean `structure` (ctor `.mk`), but the
     AUTO-generated `.height` measure references the Rust *variant* name
     (`Arm.Arm`) → `Invalid pattern: Expected a constructor marked with
     [match_pattern]` → poisons the whole file → every proof gets `sorry`. FIX:
     **never use a single-variant enum**; INLINE the arm fields into
     `ArmList::Cons(u64 ctor, BinderIdList binds, Box<ExprData> body,
     Box<ArmList> tail)` — the crate's own `BinderList::Cons(u64,u64,Box<..>)`
     idiom. Clean 2-type cycle `ExprData ↔ ArmList`, no `MatchArm`/`RawArm` type.
  3. **⚠ W7a's frozen `arms_eq` did NOT actually validate the mutual eq.** Its
     `arm_eq` compared arm bodies with Lean's DERIVED `DecidableEq` `=`
     (`marm_body a = marm_body b`), sidestepping the `arms_eq → expr_eq`
     recursion. The genuine mutual nat-returning `expr_eq ↔ arms_eq` (arms_eq
     recurses into expr_eq on bodies) was UNPROVEN by W7a. I validated it
     independently (`/tmp/mut_eq4.lean` + probe_mutual2): it decide-reduces,
     axioms clean, binder-id-mismatch kill correctly flips to 0. **W7b uses the
     genuine mutual eq (NOT derived `=`)** — the crate's `expr_eq` is
     nat-returning tag+projection, so the derived-`=` shortcut isn't available
     and isn't needed.
  4. **⚠ Nested `match` on the 2nd arg breaks Lean structural-recursion
     inference in emission** (`failed to infer structural recursion / Missing
     cases / Redundant alternative`). ALL eq fns — including binder-list eq —
     must follow the crate's `goal_eq`/`expr_eq` idiom: match the FIRST arg
     only, read the 2nd through NON-recursive tag+projection accessors
     (`bil_is_nil`/`bil_hd`/`bil_tl` etc.), arm bodies a chain of `if`s. (This
     is exactly WHY the crate hand-writes that idiom instead of nested match.)
  - **Validated template lives in `tactus-core/probe_mutual2.rs`** (the exact
     datatypes + spec-fn idioms to lift into lib.rs). Probe files +
     `out_probe*/` are throwaway (deleted before the real commit).
  - **NEXT:** land the vocabulary into `lib.rs` per §Description, using the
     inline-arm shape (gotcha 2) + genuine mutual eq (gotcha 3) + projection
     idiom (gotcha 4). Verify with:
     `TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus
     --crate-type=lib --lean-backend --lean-all-proofs lib.rs` (from
     `tactus-core/`; toolchain confirmed ready — verus Jul 14, lean 4.25.0,
     vstd.vir + prelude cache present). Then re-emit oleans + rerun probe9/13/14.

## Writeup

_when done: the landed diff summary, re-verify counts, olean re-emit
confirmation, probe9/13/14 status, and any shape adjustments from the freeze._
