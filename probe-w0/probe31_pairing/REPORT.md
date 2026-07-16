# probe31 — bootstrap-58 feasibility: the invertible unbounded pairing, self-contained

## What this settles

bootstrap-58 (the deferred "full injective Node-child decode" for the `fixlib.Tree`
encoding) was gated on one open **feasibility** worry, quoted from its recon:

> a faithful two-child decode needs an invertible **unbounded pairing** for
> `(embTree l, embTree r)` — Cantor (needs a triangular sqrt) / 2-adic (needs a
> valuation) are OUTSIDE `omega`'s Presburger fragment, and there is no Mathlib in
> the probe.

This probe answers that worry: **YES, an invertible unbounded pairing with a
machine-checked round-trip is achievable here.** The trick is to avoid Cantor/2-adic
altogether and use a **bit-interleaving** pairing, made **fuel-structural** so it
needs no well-founded-termination proof:

- `pair f a b` weaves bit `i` of `a` into output position `2i`, bit `i` of `b` into
  `2i+1`, for `f` bit-pairs: `pair (f+1) a b = a%2 + 2·(b%2) + 4·pair f (a/2) (b/2)`.
- `unfst`/`unsnd` peel two output bits per step (`/4`) to recover each lane.

Each recursion step is pure `%2` / `/2` / `/4` arithmetic — **inside** omega's
fragment — so the two round-trips go by induction on `f` with a single `omega` per
step. The only non-omega fact is `2^(f+1) = 2^f·2` (core lemma `Nat.pow_succ`, no
Mathlib), used to push the bit-length bound `a < 2^f` to the children.

## What landed (all `[propext, Quot.sound]`, no `sorryAx`, no Mathlib)

| theorem | statement |
|---|---|
| `unfst_pair f a b` | `a < 2^f → b < 2^f → unfst f (pair f a b) = a` |
| `unsnd_pair f a b` | `a < 2^f → b < 2^f → unsnd f (pair f a b) = b` |
| `pair_injective`   | equal codes (enough fuel) ⇒ equal component pairs |
| `unzz_zz x`        | `unzz (zz x) = x` — the Int→Nat zig-zag seam (pure omega) |

Compiles with the bare Nix `lean` (4.25.0) in ~1.6 s, no imports beyond `Init`, no
oleans. `./run.sh` reproduces it and prints the axiom closures.

## How a future Node-child decode uses this

The card's encoding stores only the child **sum** (`2·(embTree l + embTree r)+1`),
which is why it isn't injective on Node. Replace it with the pairing:

```
embTree (Node l r) := 2 * pair F (zz (embTree l)) (zz (embTree r)) + 1
```

where `zz : Int → Nat` is the zig-zag (children embeddings can be negative — a
`Leaf v` holds an arbitrary `Int v`), and `F` is a fuel bounding the child bit-length.
Then `ctorField (embTree (Node l r)) 0 = embTree l.deref` follows from `unfst_pair`
+ `unzz_zz`, and likewise for index `1` via `unsnd_pair`.

## What is still deferred (honest scope)

This probe is **the mathematically hard core only** — the invertible pairing. It is
**not** the full bootstrap-58 deliverable. Still to do, if a live obligation ever
needs it (see the board card — the census is currently empty, so this is parked):

1. Pick a fuel discipline `F` for `embTree` — either a global bound, or thread a
   height/`sizeOf`-derived fuel so `zz (embTree child) < 2^F` is dischargeable at
   every Node. (The round-trip theorems need that bound; `embTree` is a whole-tree
   fold, so `F` must dominate the deepest child's code width.)
2. Re-ground `ctorField`/`ctorTag` on the new pairing-based `embTree`, redo the
   rung-3 `ground_match_*` facts, and add a fixture spec fn whose `Node` arm
   actually **reads** its children (unlike `tree_head`, which returns 0 for Node),
   so a grounded `Match` denotes to a real Node-child-reading emitted fn.
3. The Int seam adds `Int.toNat` reasoning at the pairing boundary; `zz`/`unzz`
   here are omega-clean, but composing them under `pair`'s `Nat` domain needs a few
   bridging lemmas.

None of that is blocked anymore — the feared "no invertible pairing without
Mathlib/sqrt" obstacle is gone. The remaining work is integration engineering,
gated (per the card) on the census finding a live Node-child-inspecting `Match`.
