# Poems

Occasional pieces written during sessions. Dated by commit.

---

## 2026-04-20 — Track B slices 2, 3, 6; two review passes; FP refactor

### Refactor

There's a moment, midway through,
when the code stops fighting you.

You've written `Box::new(LExpr::new(ExprNode::BinOp { op, lhs, rhs }))`
twenty times. Each time you thought: yes,
this is the cost of being explicit.

Then you write `LExpr::and(l, r)` once,
in a different file, as a helper —
and you come back, and every one of the twenty
incantations is waiting to collapse.

The line count drops.
A bug lifts out with it.
(It had been hiding in the boxing.
Things hide in the boxing.)

The tests still pass. You didn't change anything,
is what you tell yourself. You just named
the shape you had been making all along.

### Soundness hole

```rust
if let Some(name) = extract_simple_var(dest) {
    items.push(BodyItem::Let(name, rhs));
}
```

No else.
The struct field write dies here.
The verifier says *ok*.

It is not ok.

### Weakest precondition

Programs run forward.
`assert(P); rest` becomes `P ∧ wp(rest)` —
the proposition builds from the end,
each statement transforming what must hold
when we arrive.

You write programs forward.
You verify them back.

The surprise, every time:
the thing you'd been doing anyway,
written down, is a proof.

---

## 2026-04-20 (evening) — slice 5 (loops), review passes, FP-comprehensive pass

### Recursion by its name

We tried `repeat'`. We tried `iterate N`.
We tried `any_goals` and `all_goals` and `<;>` threading.

What worked was:

```lean
macro_rules
  | `(tactic| tactus_peel) => `(tactic|
      first
        | (apply And.intro <;> tactus_peel)
        | (intro _; tactus_peel)
        | skip)
```

A tactic that says its own name.

Omega doesn't introduce ∀.
Omega doesn't split top-level ∧.
Omega doesn't know how to recurse.

So we wrote the small thing omega can't do,
next to omega,
and called them together.

The boring tool handled every leaf.
The interesting tool was just the recursion
that made the boring tool applicable.
