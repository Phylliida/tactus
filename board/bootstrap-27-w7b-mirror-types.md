---
title: "W7b — land the frozen defs-layer vocabulary in tactus-core (one batched cache-churning edit)"
status: todo
claimed_by:
created: 2026-07-14T23:00:00Z
updated: 2026-07-14T23:00:00Z
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

## Writeup

_when done: the landed diff summary, re-verify counts, olean re-emit
confirmation, probe9/13/14 status, and any shape adjustments from the freeze._
