---
title: "tgt defs family: `coset_group` fails — generated Option accessor `lib.option.Option.Some_val0` not in scope"
status: todo
claimed_by:
created: 2026-07-14T14:40:00Z
updated: 2026-07-14T14:40:00Z
---

## Description

Surfaced once **bootstrap-40** unblocked the base defs family: with
`TactusDefs_lib{,_exec}__base` now building, the full-krate tgt defs build
reaches the per-module defs and `TactusDefs_lib__coset_group` fails to elaborate:

```
TactusDefs_lib__coset_group.lean.failed:16:11: error:
  Invalid field `Some_val0`: The environment does not contain
  `lib.option.Option.Some_val0`
    seq.Seq.index (option.Option Nat) (...) ↑col   has type   option.Option Nat
```
(3 sites in coset_group; all `(... : Option Nat).Some_val0`.)

`Some_val0` is the generated variant-field accessor for a multi-variant datatype
(Option = Some | None). The emitter renders a `Some`-variant field access as
`lib.option.Option.Some_val0`, and the `[Nonempty T]` machinery
(`nonempty.rs:74-84`, Seed 3) is explicitly built around this accessor. So the
accessor is *expected to exist* — the failure is that it is **not present in the
environment** the `coset_group` module-defs file elaborates against.

## Why it matters / what it blocks

Blocks **bootstrap-39** (in-gate bridge on real tgt). The package gate needs the
FULL defs module to build; any module-defs failure ⟹ `package gate skipped:
shared-defs module unavailable` ⟹ islands fallback ⟹ the in-gate bridge
(`run_bridge_step`) never fires. This is one of two remaining blockers (the other
is **bootstrap-42**, pattern arity in `britton_via_tower`).

## Provenance / not a regression

Byte-identical `coset_group.lean.failed` between run #2 (`/tmp/w4a-tgt-ingate2`,
before the bootstrap-40 fix) and run #3 (`/tmp/w4a-tgt-ingate3`, after) — so this
is pre-existing, independent of the DeepView value-vs-Ref fix. Run #2 just never
reached it (it aborted at the base defs first).

## ROOT CAUSE (traced 2026-07-14) — this is a FALLBACK ARTIFACT of bootstrap-42

The accessor `lib.option.Option.Some_val0` IS emitted — as
`@[simp] noncomputable def lib.option.Option.Some_val0 {V} [Nonempty V] ...` —
but only when the defs render has `emit_accessors == true`. The ladder in
`crate_defs.rs:315-323` controls this per scope:
```
ScopeKind::Exec  => [(full_roots, !exec_roots.is_empty() || wp_routed_proof, true, true)]
ScopeKind::Proof => [(proof_roots, wp_routed_proof, false, true),   // attempt 1: accessors ON
                     (proof_roots, false,           false, false)]  // attempt 2: accessors OFF
```
- **Exec base** (`TactusDefs_lib_exec__base`): exec roots present ⟹ accessors ON
  ⟹ `Some_val0` declared (line 33). Builds.
- **Non-exec base** (`TactusDefs_lib__base`): the ladder tried attempt 1
  (accessors ON) — which FAILED (because `britton_via_tower`, **bootstrap-42**, a
  pattern-arity bug independent of accessors, fails in EVERY attempt) — and fell
  back to **attempt 2 (accessors OFF)**. That render has NO `Some_val0`, and
  `coset_group` (a non-exec/spec-side module that references `.Some_val0` in a
  spec-fn body) then fails. Both ladders record `FAILED` (`lib.ladder`,
  `lib_exec.ladder`), and the `.failed` dumps on disk are from attempt 2.

**Evidence it's pure-accessor:** `coset_group.lean.failed` has EXACTLY 3 errors,
ALL `Some_val0`, ZERO others. So if the accessor were present (attempt 1), it
would build clean.

**Prediction:** fixing **bootstrap-42** lets the non-exec attempt 1 (accessors
ON) win, which auto-resolves this card (coset_group finds `Some_val0`). Verify
that prediction before doing independent work here — this card may close for free.

**BUT there's a real latent design flaw worth its own fix:** attempt 2's
`emit_accessors == false` can NEVER succeed for a crate whose SPEC fns reference
variant accessors (`.Some_val0`) — dropping the accessor guarantees the failure.
The fallback's stated purpose (comments at `crate_defs.rs:280-309`) is to drop
broken BROADCAST AXIOMS / exec closures, not accessors. Consider: keep accessors
in the fallback (add an accessors-ON / union-OFF rung before the accessors-OFF
rung, or make attempt 2 `emit_accessors = wp_routed_proof_present`). Accessors are
cheap and their emission does NOT fail for tgt (the exec base proves it). Caveat:
accessor defs carry `[Nonempty V]`; if a datatype lacks a Nonempty instance the
accessor def won't elaborate — the original reason the OFF fallback exists — so a
blanket always-ON could regress a different crate. A referenced-only accessor
emission (emit just the accessors actually used) would be the principled fix.

## Scope of the fix

Preferred order: (1) fix **bootstrap-42**, re-run, check whether this closes for
free. (2) If it doesn't (or to harden regardless), address the accessors-off
fallback dropping needed spec-side accessors, per the design note above.

Repro: rebuild the bootstrap binary, then run the bootstrap-39 run #2 recipe
(`--lean-backend --crate-type=lib <tgt>/src/lib.rs --tactus-bridge
--verify-module runtime`, no `--emit-lean`, no `-V cache`); inspect
`$TACTUS_LEAN_OUT/lib/TactusDefs_lib__coset_group.lean.failed`. Elaborate it
standalone with `LEAN_PATH="$OUT/lib:<core-out>:<prelude>" lean <that file>`.

**Done when:** `TactusDefs_lib__coset_group` builds with 0 Lean errors under the
bootstrap fork (whether via bootstrap-42 or the fallback fix).

## Progress

- (2026-07-14, opus-bootstrap40-deepview) Filed from the bootstrap-40 /
  bootstrap-39 tgt run, then ROOT-CAUSED: it's the accessors-OFF fallback
  (crate_defs.rs ladder attempt 2), reached because bootstrap-42 sinks attempt 1.
  coset_group's only errors are the 3 `Some_val0` refs. Likely closes when
  bootstrap-42 lands; independent fix = don't drop needed accessors in the
  fallback.

## Writeup

_pending a fix._
