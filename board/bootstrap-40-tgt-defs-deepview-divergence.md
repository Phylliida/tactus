---
title: "tgt package-gate defs family fails under bootstrap fork: Option<T> DeepView emits deep_view on a bare value (expects Tactus.Ref)"
status: done
claimed_by: opus-bootstrap40-deepview
created: 2026-07-14T12:55:00Z
updated: 2026-07-14T14:40:00Z
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

- (2026-07-14, opus-bootstrap40-deepview) **ROOT-CAUSED + FIXED + VALIDATED.**
  Not a "value-space recursion" gap in the DeepView emitter — it's a
  **match-ergonomics** miss in the general VIR→Lean match renderer
  (`to_lean_expr.rs::ExprX::Match`). vstd's instance body is
  `match self { Some(t) => Some(t.deep_view()), None => None }` where
  `self : &Option<T>`, so Rust match ergonomics binds `t : &T`. VIR records the
  pattern binding's typ decorated (`&T`). But the renderer emits the scrutinee at
  VALUE depth (`self.deref`, via `render_place_with_derefs`), so the Lean-level
  `t` is a bare value — while its binder-map typ still says `&T`. At the
  `t.deep_view()` receiver-coercion site the code reads `t`'s typ as
  already-`Ref` and skips the `Ref.mk` wrap → `deep_view t` (value) where
  `Tactus.Ref` is expected. Tuple/Vec DeepView dodged it because they use field
  projection (`self.deref.1`), which reports a value typ and DOES wrap.
  See the full trace at `to_lean_expr.rs:536` (class-method src_typ) and
  `:145`/`:208` (structural_typ Var/ReadPlace) — all read the same binder map.

## Writeup

**Fix (one file, `source/lean_verify/src/to_lean_expr.rs`):** in the
`ExprX::Match` arm, peel exactly `scrut_derefs` OUTER reference-decoration layers
off each pattern binding's typ before it enters the arm's binder map, where
`scrut_derefs` = the number of `.deref`s applied to bring the scrutinee to value
depth (the same count `render_place_with_derefs` uses). Match ergonomics stamped
each binding with the scrutinee's outer `&` layers; since the scrutinee renders
deref'd, the bound var is a bare value at the Lean level, so its binder typ must
be peeled to match. New helper `peel_n_ref_decorations` (loops the existing
`strip_one_ref_decoration`, which stops at the first non-ref layer).

**Why it's safe (strict no-op for every prior case):** the peel count is
`lean_level_wrap_count(scrutinee)` — **0 whenever the scrutinee is already a
value**. Every existing match in the e2e suite matches a VALUE parameter
(`match t` with `t: Tree`; grep: zero `match self` in `rust_verify_test/tests/
tactus.rs`), so `scrut_derefs == 0` and the binder typ is unchanged — including
the P8 `Box` cases (`test_spec_let_box_use_derefs`,
`test_structural_decreases_kernel_computes`), whose bound vars stay `Box<T>` and
use explicit `*a`. Only Ref-typed scrutinees (`match self` in a `&self` instance
method — the previously-untested shape that carried the bug) change, and there
the peel strips ONLY the outer ergonomics `&`, leaving genuine inner Box/Rc/Arc
field wrappers intact.

**Validation (three levels):**
1. **Minimal repro** (`/tmp/dv-repro/lib.rs`: an exec fn whose `requires`
   references `Option::<u64>::deep_view`, forcing the instance into the base
   defs). Post-fix emission (`TactusDefs_lib_exec__base.lean:33`):
   `... Option.Some (lib.view.DeepView.deep_view (Tactus.Ref.mk t)) ...` — the
   `Ref.mk t` wrap is present. Base defs family builds to `.olean`, **no
   `.failed`**.
2. **Real tgt corpus** (bootstrap-39 run #2 recipe, rebuilt binary): both
   `TactusDefs_lib__base.olean` AND `TactusDefs_lib_exec__base.olean` now build
   with **0 Lean errors** (no `.lean.failed`). The exact `base`-defs criterion of
   this card is met. Run: `24 verified, 0 errors`.
3. **Unit tests** `cargo test -p lean_verify --lib`: 365 pass, 1 pre-existing
   failure (`sst_serialize::tests::lexpr_to_exprdata_census_rejects`) that is
   UNRELATED — it expects a 2-arg app to reject with `ed-app-arity`, but commit
   `d3349be` (bootstrap-34) deliberately widened those arms to accept multi-arg
   `ExprData.AppN`; the test is stale from that prior commit (my diff touches
   only `to_lean_expr.rs`, not `sst_serialize.rs`). Filed as **bootstrap-43**.

**Honest scope — this fix does NOT by itself unblock bootstrap-39.** With the
base defs now building, the full-krate tgt defs build reaches TWO more, SEPARATE,
pre-existing defs-family elaboration failures that keep the package gate skipped
(`note: package gate skipped: shared-defs module unavailable (defs build
failed)` → islands fallback → bridge never fires):
- **`coset_group`** — `Invalid field 'Some_val0'`: the generated multi-variant
  accessor `lib.option.Option.Some_val0` is not in scope when the module's defs
  elaborate. (Confirmed byte-identical to run #2's failure — pre-existing, not
  from my fix.) → **bootstrap-41**.
- **`britton_via_tower`** — `Invalid pattern: Not enough arguments to
  DerivationStep.FreeExpand` (constructor-pattern arity in the defs emission). →
  **bootstrap-42**.

Both are distinct root causes from the DeepView value-vs-Ref bug this card names,
and both must be fixed before the tgt defs family builds whole and the in-gate
bridge (bootstrap-39) can run. **Assumption:** I mark this card done on its
titled bug (Option DeepView `deep_view t` → `deep_view (Ref.mk t)`) + its literal
`__base` build criterion, both verified; the gate-reaches-bridge consequence is
gated on the two follow-ups.
