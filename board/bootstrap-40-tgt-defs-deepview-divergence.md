---
title: "tgt package-gate defs family fails under bootstrap fork: Option<T> DeepView emits deep_view on a bare value (expects Tactus.Ref)"
status: todo
claimed_by:
created: 2026-07-14T12:55:00Z
updated: 2026-07-14T12:55:00Z
---

## Description

Discovered while validating the W4a in-gate bridge on the real tgt corpus
(`bootstrap-39`). Under the **bootstrap** fork, a full package-gate run over
`tactus-group-theory` (`--lean-backend`, package-check default-on, no
`--emit-lean`) **fails to elaborate the unified defs family**:

```
defs part `TactusDefs_lib_exec__base`: (failing source dumped to
  /tmp/w4a-tgt-ingate2/lib/TactusDefs_lib_exec__base.lean.failed)
TactusDefs_lib_exec__base.lean:371:137: error: Application type mismatch:
  argument   T
  expected   Tactus.Ref ?m.9
  in         lib.view.DeepView.deep_view t
```
Both `TactusDefs_lib_exec__base` and `TactusDefs_lib__base` fail the same way.

**The offending emitted instance** (the recursive `DeepView` for `Option<T>`):
```lean
noncomputable instance {T : Type} {_tactus_assoc_T_DeepView_V : Type}
    [lib.view.DeepView T _tactus_assoc_T_DeepView_V] :
    lib.view.DeepView (lib.option.Option T) (lib.option.Option _tactus_assoc_T_DeepView_V) where
  deep_view := fun (self : _) => match self.deref with
    | lib.option.Option.Some t => lib.option.Option.Some (lib.view.DeepView.deep_view t)  -- ← t : T, but deep_view wants Tactus.Ref
    | lib.option.Option.None    => lib.option.Option.None
```
After `match self.deref with | Some t =>`, `t` is the deref'd **value** (`: T`),
but `lib.view.DeepView.deep_view` is typed to take a `Tactus.Ref …`. The emitter
recurses on the bare value without re-wrapping (or the emitted class field's
expected argument type is Ref while the call site passes a value). Same shape
will hit any generic container's recursive DeepView (Seq, Vec, tuple, …).

## Why it matters / what it blocks

- **Blocks `bootstrap-39`** (in-gate bridge validation on real corpus). The
  in-gate bridge (`--tactus-bridge`, `run_bridge_step`, `generate.rs:3319`) runs
  only at the END of `check_package`, *after* the full-krate defs family builds.
  With the defs build failing, the gate never reaches the bridge step, so the
  in-gate bridge can't be exercised on tgt at all — independent of which
  `--verify-module` scopes the per-fn checks (the package gate builds the
  **full-krate** defs family "independent of bucketing", `verifier.rs:3332`;
  run #2 built the unqualified `TactusDefs_lib{,_exec}__base` and both failed).
- **Why the EXTERNAL def-bridge (bootstrap-37, probe20) dodged this:** the
  external path emits certs with `--tactus-emit-cert` and elaborates each cert
  file standalone with `LEAN_PATH=<tactus-core/out/lib>:<prelude>`. Each cert
  `import TactusDefs_lib_exec` — i.e. **tactus-core's** prebuilt olean — and does
  NOT build tgt's own defs family. So the def/dt bridge over the `symbol` slice
  (135/135 close) never triggered the Option DeepView emission. Only the in-gate
  package-gate path builds tgt's defs family and trips this.

## Scope of the fix (not yet investigated in depth)

The emitter that lowers generic `DeepView` instances into the defs family needs
to keep the recursion in Ref-space (wrap `t` back to a `Tactus.Ref`, or emit
the recursive call so its argument type matches `deep_view`'s expected Ref
parameter). Likely lives near the std_specs/view instance emission in the
serializer (grep the defs-family emitter for `DeepView`/`deep_view`/`View`
instance synthesis). Cross-check against how production's Lean prelude declares
`DeepView.deep_view`'s parameter (Ref vs value) — the emitted instance must
match that signature exactly.

**Done when:** a bootstrap-fork `--lean-backend` package-gate run over tgt (or a
tgt slice that references `Option<T>`/`Seq`/`Vec` deep views) builds
`TactusDefs_lib__base` + `TactusDefs_lib_exec__base` with 0 Lean errors, so the
package gate reaches `run_bridge_step`. Then `bootstrap-39` can close.

## Progress

- (2026-07-14, opus-w4a-tgtval) **Filed from the bootstrap-39 investigation.**
  Failing source preserved at `/tmp/w4a-tgt-ingate2/lib/*.lean.failed` (line 371
  in `TactusDefs_lib_exec__base.lean.failed`) — may be cleaned; regen with the
  bootstrap-39 run #2 recipe. A local model (port 8051) asserted this is a
  "known W7 defs-layer emitter gap" (naive value-space recursion) — **unverified
  by me**; bootstrap-37's writeup does NOT mention it (that card used the
  external path and never built tgt's defs family). Treat provenance as open;
  the failing-source evidence above is the ground truth.

## Writeup

_pending a fix._
