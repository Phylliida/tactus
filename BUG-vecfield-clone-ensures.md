# The final e2e residue: `test_exec_vec_field_index_clone` — full diagnosis

**Status (2026-07-18): root cause pinned with a machine-checked witness.
Not fixable by closer work. Two-layer gap; the blocking layer is the
`call_ensures` / trait-ensures encoding (B6-adjacent), not sequence
extensionality as previously guessed.**

Repro: `probe-vecfield-clone/run.sh` (regenerate the artifact first —
instructions in the script header).

## The test

```rust
struct Holder { imgs: Vec<Vec<u8>> }
fn clone_field_index(h: &Holder, i: usize) -> (out: Vec<u8>)
    requires (i as int) < h.imgs@.len(),
    ensures out@ == h.imgs@[i as int]@,
{ h.imgs[i].clone() }
```

## What the postcondition theorem has (all hoisted, N1/N2 working fine)

From the inlined `Vec<u8>::clone` ensures:

1. `spec_vec_len (mk tmp__3) = spec_vec_len tmp__1` — length equality.
2. `∀ j ∈ [0, len), cloned Int (index (view tmp__1) j) (index (view (mk tmp__3)) j)` — pointwise.
3. `vec_clone_trigger …` — opaque trigger.
4. `view tmp__1 = view (mk tmp__3) → view tmp__1 = view (mk tmp__3)` — **vacuous**: in
   Verus this is `self@ =~= res@ ==> self@ == res@`, and the Lean
   rendering collapses `=~=` to `Eq`, so the ext-bridge conjunct
   becomes `A → A`. (Same collapse hits
   `vec_clone_deep_view_proof`, the `=~~=` bridge.)

Broadcast haves include `axiom_seq_ext_equal` — which, under the same
`=~=`→`Eq` collapse, renders as **true extensionality**
(`(s1 = s2) = (len-eq ∧ pointwise-eq)`), i.e. the collapse that makes
conjunct 4 vacuous simultaneously makes the ext axiom strong enough to
compensate. Also present: `axiom_spec_len` bridging `spec_vec_len` to
`Seq.len ∘ view`.

## The gap

`cloned` unfolds (emitted def):

```
cloned T a b := strictly_cloned T a b ∨ a = b
```

but `strictly_cloned` is an **opaque axiom Prop**. Its Verus body is

```rust
pub open spec fn strictly_cloned<T: Clone>(a: T, b: T) -> bool {
    call_ensures(T::clone, (&a,), b)
}
```

and the emitter deliberately axiomatizes any spec fn whose body
mentions `call_ensures`/`call_requires` (`CallTarget::BuiltinSpecFun`)
— there is no Lean encoding for it (see
`expr_shared.rs` "Does this spec fn emit as a Lean AXIOM" and
`generate.rs` `body_references_builtin_spec_fun`; history: the
raw `builtinSpecFun` placeholder poisoned whole artifacts).

Z3 closes the original test through exactly that body: `call_ensures`
unfolds via fndef axioms to u8-clone's `ensures res == *self`, giving
pointwise **equality**, then seq-ext. With `strictly_cloned` opaque,
the disjunction in `cloned` cannot be resolved and the theorem is
**unprovable** — a model may satisfy `strictly_cloned` everywhere
while views differ. No tactic can fix this.

## Machine-checked witness (probe-vecfield-clone/)

* `repro_hand_proof.lean` — the artifact's postcondition theorem with
  ONE extra hypothesis
  `∀ a b : Int, strictly_cloned Int a b → a = b`
  and a 20-line structured proof: substitute hoist equations, rewrite
  the goal by `axiom_seq_ext_equal`, split; length leg via
  `axiom_spec_len` twice; pointwise leg by instantiating hyp 2 at `j`,
  unfolding `cloned`, and discharging the disjunction with the granted
  fact. **Closes clean.** Everything else the theorem needs is already
  in context.

* `repro_derived_closer.lean` — the same granted hypothesis with the
  artifact's actual derived closer. **Fails** (omega counterexample):
  `simp_all + omega` cannot instantiate the ∀-pointwise hypothesis,
  eliminate the disjunction, and apply the ext axiom backward.

## Consequences

Two independent work items, in dependency order:

1. **[blocking] `call_ensures` encoding** — give
   `CallTarget::BuiltinSpecFun(ClosureEns/ClosureReq)` a Lean
   rendering so `strictly_cloned`'s body survives. For a statically
   resolved callee, the machinery to render "callee's ensures with
   arguments substituted" already exists (`render_call_ensures` in
   sst_to_lean, used for exec-call inlining) — the natural shape is a
   per-fn ensures-predicate def (`g.ensures_pred typ_args args ret`).
   The hard case is the one this test needs: `T::clone` under a
   GENERIC `T` inside the one-time emission of `strictly_cloned` —
   that requires trait-method ensures dispatch (a typeclass carrying
   the ensures predicate per impl), i.e. the **B6 user-trait gap**
   machinery. This is a design arc, not a patch.

2. **[secondary] an ext-capable closer step** — once (1) lands, the
   derived closer still needs to do what the hand proof does. Either
   an N3 provenance-driven script (the call site knows the callee's
   ensures shape and can emit the ext-split + pointwise instantiation
   deterministically) or a structural-rung extension for Seq-equality
   goals (apply `axiom_seq_ext_equal` ← direction, intro the index,
   specialize pointwise hypotheses). The hand proof in the probe is
   the template: it is entirely derivable from information the emitter
   already has at the call site.

## Correction of the earlier note

DESIGN-leaf-normal-emission.md §3a called this "N3's first customer
(seq extensionality)". Half right: the ext machinery is *present and
sufficient*; the blocker is clone-ensures semantics (item 1). N3 shows
up only as the delivery vehicle for item 2's script.
