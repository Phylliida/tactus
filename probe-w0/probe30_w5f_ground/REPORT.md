# probe30 — W5f v2 grounding, RUNGS 1+2+3 (board bootstrap-57)

**Status: PASS ✓** (`./run.sh`, ~2.1s elaborate). Grounds the leaf oracles `fn`/`fnN`
(rung 1, CALL fragment), `proj`/`FieldProj` (rung 2, over the real emitted
`fixlib.Point` record), and `ctorTag`/`ctorField` (rung 3, over the real emitted
`fixlib.Tree` enum + `fixlib.tree_head` match) of the W5f-v2 reference-WP soundness
model to REAL emitted defs — discharging probe29's FACT 5/8 free hypotheses by `rfl`,
and proving the FACT 12 field-projection + FACT 9/10/11 Match-decode consistency as
genuine **encoding theorems**.

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

## RUNG 3 — ctorTag/ctorField grounded to the real `fixlib.Tree` + `fixlib.tree_head`

The **Hard Rung** (recon note A): the flat-Int model stores a whole `Tree` value as ONE
Int, so `ctorTag`/`ctorField` grounding is a genuine **encoding theorem**, not an `rfl`
discharge. The emitted `tree_head` (`Leaf v => v | Node _ _ => 0`) maps EXACTLY onto FACT
9/10/11's 2-arm shape (arm0 = 1 binder, body reads it; arm1 = 2 binders, body 0), so
grounding = pin the scrutinee slot to `embTree t` and discharge the FACTs'
`htag`/`hmiss`/`htag1` by the encoding consistency.

The encoding (parity tag; low bit = constructor):

```
leafTag = 0, nodeTag = 1
embTree (Leaf v)   = 2 * v                                  -- EVEN (value survives in high bits)
embTree (Node l r) = 2 * (embTree l.deref + embTree r.deref) + 1   -- ODD (recurses through BOTH children)
crateEnv.ctorTag   = fun n => if n % 2 = 0 then leafTag else nodeTag  -- low-bit read
crateEnv.ctorField = fun n _ => n / 2                       -- Leaf payload recover
```

Consistency (`ctorTag_leaf`/`ctorTag_node`/`ctorTag_node_ne_leaf`/`ctorField_leaf`): closed
by `omega` over the parity encoding. `embTree` is well-founded (recurses through
`Tactus.Box`, mirroring the emitted `Tree.height`); its two head equations
(`embTree_leaf`/`embTree_node`) come out by `simp only [embTree]`.

**The sign trap (flagged by Danielle's local model):** the naked `n % 2` is unsound for
negative-odd Ints under the Int emod/tdiv convention. The **guarded** form `if n % 2 = 0
then 0 else 1` is used instead — robust to the convention (odd is never `≡ 0 mod 2` under
either; `omega` proves `(2v)%2=0`, `(2p+1)%2 ≠ 0` for ALL Int).

The three grounded facts tie the flat-Int Match evaluation to the REAL `fixlib.tree_head`:
- `ground_match_leaf_val` — scrutinee = `embTree (Leaf v)`, FACT 9 selects arm0, `= tree_head (Leaf v)` (= v).
- `ground_match_node_val` — scrutinee = `embTree (Node l r)`, FACT 10 walks past arm0 to arm1, `= tree_head (Node l r)` (= 0).
- `ground_match_leaf_prop` — prop-position mirror (FACT 11), `↔ tree_head (Leaf v) ≠ 0` (= `v ≠ 0`).

All rung-3 theorems carry `[propext, Quot.sound]` (standard; `Quot.sound` via `omega`'s
Int div/mod + the wf-rec `embTree` unfold) — **no `Classical.choice`, no `sorryAx`**. The
`fixlib.Tree` enum + `fixlib.tree_head` are a **verbatim rename** of the emitter's
`bootstrap-fixture/out/lib/TactusDefs_lib_exec__base.lean:22-25` +`…__root.lean:13-14`
(only `lib.`→`fixlib.`) — the REAL emitted enum and the only real Match-carrying user fn
on the slice (recon C).

## Scope / remaining (honest)

`tree_head` never READS Node children (returns 0 for every Node), so its faithful
grounding needs the Node **parity (tag)** only, NOT Node-child **decode**. Full injective
Node decode = an invertible **unbounded pairing** for the two children — which is OUTSIDE
`omega`'s Presburger fragment (no Mathlib here; base-2^64 like rung 2 fails at depth > 1),
so it is the genuine remaining hard kernel and is **explicitly deferred**. What lands: the
tags (both ctors) + the Leaf field grounded to a real recursive encoding of the real
`Tree`, tying the Match evaluation to the real `tree_head t` for ALL t. Per the card +
Danielle's steer, this is the right scope — bodies are already fn-pinned (bootstrap-56
census), so direct Match-in-goal is the rare case, and node-child inspection would be a
follow-on only if the census ever finds a live one.
