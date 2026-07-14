# probe13 — W6e expression-level mutation-kill (the Friction-2 kill)

The expression-granularity sibling of `probe10_mutations`. Where probe10 kills at
the **GoalList structure** level (reorder goals, drop a binder, change a leaf
id), probe13 kills at the **expression** level — inside the deep `ExprData` leaf
that W6d made load-bearing.

## What it proves

W6d wired the deep bridge: `goals_eq (ref_wp ctx sst) goals = 1`, where

- the **LEFT** side (`ref_wp`) INDEPENDENTLY re-derives each obligation's
  expression tree via the trusted Lean `render_exp` (materializing coercions
  from the SST's type tags), and
- the **RIGHT** side (`goals`) is the production serializer's `ExprData` output.

The blind spot W6 exists to close: a stage-A string / atom-id compare reused the
SAME renderer on both sides, so a serializer that emitted a structurally-wrong
`ExprData` — a dropped `Int.toNat`, a dropped `.deref`, a wrong field accessor,
a wrong overflow bound — would render a *right-looking string* and **silent-pass**.
The deep symmetric compare against the independent `render_exp` must instead
**FLIP** the bridge `1 -> 0`.

probe13 demonstrates the flip, positively and by `decide`, for **four
coercion-drop classes**, one per fixture fn on its own live cert:

| class | fn | gap | mutation (GOAL side) |
|---|---|---|---|
| `cast_drop`   | `sum_to`     | nat-coercion | drop one `Int.toNat`: `Cast IntToNat (Atom N)` → `Atom N` |
| `deref_drop`  | `head_exec`  | G2 auto-deref | drop the `.deref`: `FieldProj (Atom N) 0` → `Atom N` |
| `wrong_field` | `mk_point`   | G3 struct field | wrong accessor: `FieldProj (Atom N) F` → `FieldProj (Atom N) 999999` |
| `wrong_width` | `add_capped` | G6 HasType | wrong overflow bound: `Lit 2^64` → `Lit 2^32` |

For each class the generated `ExprMutations.lean` asserts, all by `decide`:

```
example : lib.goals_eq (lib.ref_wp <fn>_ctx <fn>_sst) <fn>_goals     = 1 := by decide  -- baseline closes
example : lib.goals_eq (lib.ref_wp <fn>_ctx <fn>_sst) <fn>_goals_mut = 0 := by decide  -- the drop flips
```

One `lean` elaboration with `rc=0` proves every deep baseline closes AND every
single-edit coercion drop is provably rejected. If any mutation failed to flip
(still `= 1`), its `= 0` example would error.

## Why mutate the GOAL side

The mutation models *the production serializer dropped a coercion*. So we mutate
the **untrusted** production output (`goals`) and keep `ctx`/`sst`/`ref_wp`
intact — the trusted reference re-derivation stays correct, and the divergence
is exactly what the deep compare catches. Mutating the SST would corrupt the
reference itself, which is not the bug class being modelled.

## Repeatability / regen-survival

`gen.py` reads the LIVE certs and applies **structural pattern transforms** (drop
/ replace a node), not hard-coded leaf ids, so the suite survives a fixture regen
that renumbers leaves. Each mutation asserts it actually changed the text — a
regen that removed the target shape fails LOUD here (signalling the harness needs
updating), never a silent no-op "kill".

## Run

```
probe-w0/probe13_expr_mutations/run.sh
```

Needs the live fixture certs (`bootstrap-fixture/out/lib/cert/*.cert.lean`) and
the tactus-core oleans (`tactus-core/out/lib`). Regen recipe: board/bootstrap-15
(vargo release build + `--tactus-emit-cert`).

## Relation to the in-crate kernel guard

The render-level mechanism for each class is ALSO Lean-verified abstractly in
`tactus-core/lib.rs :: expr_mirror_kernel_computes` (Case A cast-drop, Case C/G2
deref-drop, G6 wrong-width, G3 dropped-proj, G1 value-flip). probe13 is the
END-TO-END complement: it proves the deep structure is genuinely wired into the
LIVE bridge path (`ref_wp → close_e → render_exp → LeafE`, compared against real
serializer `goals`), not merely that the abstract `render_exp`/`expr_eq`
functions work on hand-written inputs.
