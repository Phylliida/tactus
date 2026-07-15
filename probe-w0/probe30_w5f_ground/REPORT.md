# probe30 — W5f v2 grounding, RUNGS 1+2 (board bootstrap-57)

**Status: PASS ✓** (`./run.sh`, ~1.6s elaborate). Grounds the leaf oracles `fn`/`fnN`
(rung 1, CALL fragment) and `proj`/`FieldProj` (rung 2, over the real emitted
`fixlib.Point` record) of the W5f-v2 reference-WP soundness model to REAL emitted
defs — discharging probe29's FACT 5/8 free hypotheses by `rfl`, and proving the
FACT 12 field-projection consistency as a genuine base-2^64 **encoding theorem**.

## What this closes

probe29's `adequacy_leaf_app_grounded` (FACT 5) / `adequacy_leaf_appn_grounded`
(FACT 8) are stated over an **abstract** `E : SymEnv` with a **free** hypothesis
`hfn : E.fn fId = g` / `hfnN : E.fnN fId = h`. The oracle interpretation was
unconstrained — the honest content was arm-selection + call-shape, not the leaf
meaning. This probe **pins** `fn`/`fnN` to the actual emitted spec fns, so the leaf
denotation is tied to emitter output, not an assumption.

## Files

- `fixlib/TactusDefs_fixlib_exec__root.lean` — the fixture's emitted `sq`/`g2`/`g3`,
  **verbatim bodies** from `bootstrap-fixture/out/lib/TactusDefs_lib_exec__root.lean`,
  with only the module name + `lib.`→`fixlib.` namespace prefix rewritten. This is
  the one-time "plumbing tax" of **obstacle D**: both crates emit the SAME module
  name (`TactusDefs_lib_exec__root`) in namespace `lib`, so the Lean loader can't
  put both on `LEAN_PATH` — a rename makes tactus-core's `render_exp` and the
  fixture's `sq`/`g2` importable together. Rename of emitter OUTPUT, not a
  hand-authored fn (which would bypass the emitter-output pin — recon point D).
- `ground.lean` — the concrete `crateEnv : W5f.SymEnv` literal + the specialized
  facts + `#print axioms` regression guard.
- `run.sh` — builds the fixlib + probe29 oleans if stale, then elaborates ground.lean
  over all four sources (tactus-core / probe29 / fixlib / prelude).

## The grounding

```
crateEnv.fn  0 = sqLift  := rfl        -- sqLift x = (fixlib.sq x.toNat : Int)
crateEnv.fnN 0 = g2Lift  := rfl        -- g2Lift [a,b] = (fixlib.g2 a.toNat b.toNat : Int)
```

`hfn_sq`/`hfnN_g2` depend on **no axioms**. The specialized denotation facts
`ground_app_sq` / `ground_appn_g2` expose `fixlib.sq`/`fixlib.g2` directly in the
RHS and carry only `[propext]` (inherited from FACT 5/8 — grounding adds nothing).

## Nat/Int seam

The emitted fns are `Nat → Nat`; FACT 5's `g` and the goal language are `Int → Int`.
`sqLift`/`g2Lift` bridge with `Int.toNat` on args + Int-coercion on the result — the
render path's `needs_nat_coercion`/`coerce_if` decision made explicit at the pin
(FACT 5's `Call … TyInt … TyInt` shape carries no cast node, so the coercion is
honest to place here).

## RUNG 2 — proj/FieldProj grounded to the real `fixlib.Point`

`proj : Int → Int → Int` reads an **Int** base, so a 2-field record can't survive the
flat-Int `eval` as itself — grounding proj is an **encoding theorem**, not an `rfl`
discharge (recon note A). Because `Point` has ONE constructor (no tag decode), the
encoding is a plain base-2^64 pairing:

```
POW = 2^64
embPoint p          = p.x * POW + p.y        -- REAL fixlib.Point projections
crateEnv.fnN 1      = mkPointLift            -- = embPoint (fixlib.Point.mk a b)
crateEnv.proj v fld = if fld = xFieldId then v / POW
                      else if fld = yFieldId then v % POW else 0
```

The consistency theorems `proj_x_consistent` / `proj_y_consistent`:
`crateEnv.proj (embPoint (fixlib.Point.mk a b)) xFieldId = a` (resp. `= b`), closed by
`omega` given the field bound `0 ≤ b < 2^64` — **exactly the fixture obligation's own
`h_b_bound`** (`mk_point.lean`). `embPoint (fixlib.Point.mk a b)` reduces (`rfl`, via
the genuine `.x`/`.y` structure projections of the real emitted record) to `a·POW+b`;
`omega` recovers each field. This is what "grounded to emitter output" means for proj:
the flat-Int oracle provably **agrees** with the real `fixlib.Point` projection.

New FACT 12 in probe29 (`adequacy_leaf_proj`): the FieldProj render→denote step —
`(base.f < 10)` denotes `E.proj ⟦base⟧ f < 10`, abstract `E`, `[propext]` (like FACT
5/8). The grounded facts `ground_proj_x`/`ground_proj_y` compose FACT 12 with the
encoding theorem over base = the emitted constructor `Point.mk a b` (rendered as an
AppN, recon note B), exposing the REAL `(fixlib.Point.mk (st a) (st b)).x`/`.y` in the
RHS. All four rung-2 theorems carry `[propext, Quot.sound]` (standard core axioms; the
`Quot.sound` enters via `omega`'s Int div/mod) — **no `Classical.choice`, no `sorryAx`**.

The `fixlib.Point` structure is itself a **verbatim rename** of the emitter's
`bootstrap-fixture/out/lib/TactusDefs_lib_exec__base.lean` `structure lib.Point`
(only `lib.`→`fixlib.`) — the real emitted datatype, the faithful analog of rung-1's
`fixlib.sq`.

## Remaining (this card stays in_progress)

- **RUNG 3** (deferred) — `ctorTag`/`ctorField` over a real enum+match
  (`fixlib.Tree`/`tree_head`). This is the **Hard Rung**: a genuine encoding-adequacy
  theorem (choose `emb : Tree → Int`, prove `ctorTag`/`ctorField` consistent with the
  constructor encoding), not an `rfl` discharge. Deferred per Danielle's steer —
  bodies are already fn-pinned (bootstrap-56 census), so direct Match-in-goal is the
  rare case.
