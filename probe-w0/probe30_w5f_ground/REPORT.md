# probe30 — W5f v2 grounding, RUNG 1 (board bootstrap-57)

**Status: PASS ✓** (`./run.sh`, ~1.2s elaborate). Grounds the CALL-fragment leaf
oracles `fn`/`fnN` of the W5f-v2 reference-WP soundness model to REAL emitted defs,
discharging probe29's FACT 5/8 free hypotheses by `rfl`.

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

## Remaining (this card stays in_progress)

- **RUNG 2** — `proj`/`FieldProj` over `lib.Point`/mk_point. Same crateEnv shape.
- **RUNG 3** (deferred) — `ctorTag`/`ctorField` over a real enum+match
  (`fixlib.Tree`/`tree_head`). This is the **Hard Rung**: a genuine encoding-adequacy
  theorem (choose `emb : Tree → Int`, prove `ctorTag`/`ctorField` consistent with the
  constructor encoding), not an `rfl` discharge. Deferred per Danielle's steer —
  bodies are already fn-pinned (bootstrap-56 census), so direct Match-in-goal is the
  rare case.
