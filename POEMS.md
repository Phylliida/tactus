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

---

## 2026-04-24 — #34 renderers, #52/53/49/50/57, two cleanup passes

### Honest shape

There were two smells.

The first was a field called `typ_inv_exps`
carrying what was not a type invariant.
The name pointed one way.
The data went the other.
A future reader would trust the name.
A future reader would be wrong.

The second was a function
whose signature said pure
and whose body held a RefCell.
The type was a promise the code did not keep.

We moved the data to where its name was.
We moved the state to where it already belonged.

The file got longer by the explanation
of why it was shorter.

### The third time

```
Wp::AssertByTactus { cond: Some(e), ... }   // #50
Wp::AssertByTactus { cond: None,    ... }   // #49
Wp::Loop           { cond: Option<&Exp>, ... }  // #57
```

`assert by` landed on a new variant.
`proof blocks` made `cond` an Option.
`break/continue` made the loop's `cond` an Option.

Three tasks, one trick:
the thing that was always there
becomes the thing that can be absent.

The estimate was a week.
The work was thirty minutes.
The difference was the two tasks before it,
which had already found the shape.

### Against the thing I wanted to build

I kept wanting to write a derive macro
for the walker I had to write twice.

Each time I counted the walkers,
the count was honest: five, maybe six.
Each time I counted the pain of writing one,
the count was also honest: two minutes.

The answer that wins a debate
is not the answer that wins a day.
The walker that writes itself
costs a week to teach.
The walker you write by hand
costs a coffee.

I'm saving the macro
for when I forget to write a walker,
or when I write one wrong,
or when a variant slips past three of them.

None of these has happened.
The tool I didn't build
is the quietest kind of right.

---

## 2026-04-24 (continued) — #54, #58: non-int decreases + match automation

### done

I assumed `first` meant first-to-succeed.
It meant: first-to-run-without-error.

`simp_all`, faced with a goal it can't close,
does not raise. It simplifies what it can,
reports success, and moves on.
The next alternative never sees the goal.

The fix was one word, glued to each branch:
`done`.
A tactic that fails unless the goal is closed.

Now `simp_all; done` behaves the way
I thought `simp_all` did, alone.
The contract was always: finish the goal.
I had just forgotten to ask.

### The gate

For #58 I needed a filter:
these types we case-split, these we leave alone.

Not "user datatype" — `Int` passes that.
Not "in our namespace" — Mathlib would escape.

Then: the types I want are exactly the ones
that have a companion `.height` function.
I emit those. In the previous session.
For a different reason.

The whitelist wrote itself
while I was looking elsewhere —
a side door, already locked,
that turned out to open
for the exact room I needed next.

### Downstream

#54 was estimated three to four days.
It took a session.

#58 was estimated a week.
It fell out of #54's infrastructure
and took an afternoon.

What I did not write down:
the earlier refactors that taught me
the DSL carries its own continuation,
so branching was free.
The five-lens review where I learned
which smells were worth their cost.
The deferrals audit
where I wrote down what we'd already decided
so the next version of me could find it.

The hour is the visible cost.
The rest sits in the pages
I wrote before I knew I'd need them.
