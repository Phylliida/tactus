# bootstrap-83 — F2: vstd-as-package (scope fork after step-0 probe)

Status: **CARDED 2026-08-06 — step-0 probe FROZEN, scope fork needs
Danielle's call before implementation.** Implements endgame table row
13, second of the three milestone-F bricks (DESIGN-bootstrap-endgame.md
§7: "vstd as a package: the Boundary module shrinks to imports; the
remaining vstd axioms become the explicit, closure-checked cross-crate
trust surface"; the full end state is DESIGN-emit-module.md M6).
The endgame sizes the F bricks "small ×3" — **the step-0 probe shows
the full M6 end state is NOT small today** (new coverage class, §E3).
Two scoped options at the bottom; both honor the wording, at different
horizons.

## Step-0 evidence (frozen 2026-08-06)

### E1 — how the vstd surface works today

Consumers read the exported `vstd.vir` (vstd_build's `--export`
artifact; `rust_verify/src/main.rs:82` auto-imports it). The tactus
emission re-declares the vstd cross-crate surface as `Command::Axiom`s
inside each CONSUMER's defs modules (root + per-module), per consumer,
per crate. The Link module's `#tactus_check_axioms <thm>_closed
[<Boundary>]` whitelists exactly that set (Boundary = all
`Command::Axiom` names in the defs module; `generate.rs:4651-4659`).
tactus-core's own Boundary is `[]` (self-contained — its gate's trust
inventory is clean).

### E2 — the inventory (from probe11's live tgt out-tree)

Root defs module (`TactusDefs_lib_exec.lean`): **52 axioms**, splitting
into:

- **~36 base stipulations** (irreducible while vstd's `Seq` is
  `external_body`): the `axiom_seq_*` (17), `axiom_set_*` (11),
  `axiom_array_*` (3), `axiom_vec_*` (4), ext-equal pairs, plus the
  per-module type axioms (`lib.seq.Seq`, `lib.set.Set`, `lib.vec.Vec`,
  `lib.alloc.Global`) and uninterpreted spec-fn axioms
  (`Seq.new/len/index/empty/push/update/subrange/add`, Set ops,
  `View.view`).
- **~16 vstd-PROVED lemmas** — theorems in vstd, re-stipulated as
  axioms in every consumer: 8 `arithmetic.div_mod.lemma_*`, 5
  `seq_lib` (`add_empty_left/right`, `push_distributes_over_add`,
  `lemma_seq_concat_contains_all_elements`,
  `lemma_seq_two_subranges_index`), `set_lib.lemma_set_subset_finite`,
  `array.lemma_array_index`, `array.array_len_matches_n`,
  `std_specs.vec.vec_clone_deep_view_proof`, `axiom_spec_len`.
  Crate-wide the provable layer is much larger: `seq_lib.rs` alone
  has **175 proof fns**.

### E3 — the probe: vstd through the lean-backend emit (verdict: blocked)

Command (vstd_build's flag set, scoped):

```
verus --internal-test-mode --extern verus_builtin=… --extern … --is-vstd \
  --cfg feature="std" --cfg feature="alloc" --lean-backend --emit-lean \
  --verify-module seq_lib source/vstd/vstd.rs
```

Result: **140 errors, ALL ONE CLASS** — "Tactus codegen produced
unresolved references": trait associated-type / instance-projection
coverage gaps (`vstd.contrib.exec_spec…`: unresolved `V`;
`std_specs.convert.TryFromSpec`: unresolved `Error`; `instance`:
unresolved `(Self := (A))`, `(Self := (T))`, `USize`). These are
codegen-level (defs/instance emission), NOT census-level — the census
itself runs fine (151/820 certified; tags: branch-forced-state-join ×5,
rawvir-arrayliteral ×5, rawvir-call-arity ×3, rawvir-withtriggers ×2,
branch-forced-state-leak ×1, emit-counter-drift ×1, rawvir-binaryopr,
rawvir-readplace-nonlocal). Plain `verus vstd.rs` without the
vstd_build flags doesn't compile at all (feature cfgs missing) —
the flag set above is required and now recorded.

**Verdict: theorem-izing vstd's lemma layer (the real trust shrink) is
blocked on a NEW coverage class — trait associated-type/instance
projections in defs emission. That is a milestone-A-style arm
(subject matrix, serializer/model work), not an F "small" brick.**

## The fork (Danielle picks)

### Option A — the explicit, closure-checked vstd Boundary (SMALL, ~this session)

Single-source the scattered per-consumer re-declaration into ONE
versioned Boundary artifact and add the package-level closure roll-up
(closure-doc §5's end-state line): a generated `Boundary` module whose
declared set the crate gate checks EVERY closed theorem against, so
the crate's soundness claim becomes one machine-checked line — "every
theorem in this package rests on ⊆ classical core ∪ arch pair ∪ THESE
vstd axioms". **No trust shrink** — the same axioms, made explicit,
single-sourced, machine-inventoried (transparency/predictability wins;
sets up Option B's diff to be visible: every lemma that later becomes
a theorem visibly LEAVES the artifact). Sized small: the Boundary
list machinery already exists (`generate.rs:4651`); the brick is the
artifact + the roll-up + pins.

### Option B — card the trait-assoc-projection coverage arm FIRST (medium-large), vstd-as-package after

Treat the probe's blocker as what it is: the next coverage arm, in the
milestone-A idiom (card + subject matrix + serializer/model work +
probe13 kills). Only after it lands does "vstd as a package" (lemma
layer theorem-ized, Boundary genuinely shrinking to imports) become a
tractable brick. This is the direct route to the actual trust shrink
(~16 consumer-surface axioms → theorems immediately; the 175-fn
seq_lib layer over time).

### Recommendation

**A now, B carded as its own arm.** A is cheap and turns the trust
surface into a diff-able artifact; B is the next real arm and deserves
its own card/subject-matrix cycle rather than being folded into an F
brick. B's card can be drafted from this card's E3 (the blocker census
is already frozen).
