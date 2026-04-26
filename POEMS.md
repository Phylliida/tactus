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

---

## 2026-04-25 — source mapping, AST tightening, the cost of "good enough"

### Cheap

`scan_span_marks is cheap.`
That's what I told myself.
A `match_indices` loop, byte-counting newlines.
O(n × m) where m is small. Who cares.

You asked if I could push during emission instead.
I'd already considered it and rejected it:
fifty call sites, too invasive,
the math doesn't work.

I went to count again.
Twelve functions. Three already taking `&mut Vec<usize>`.
Adding a field to that vec turned out to be —
nothing. A struct rename. A push at one site.

The post-scan was thirty lines.
The threaded version was twenty.
The fragile-on-`-/`-in-paths was real.

What's "cheap," then?
The work I'd already justified not doing.
The work whose cost I'd inflated to match
the cost of changing my mind.

### The label said precondition

I built the whole thing.
Seven kinds. Seven wrapping sites.
Tested on the non-decreasing case.
The label said: precondition.
The obligation was termination.

I peeled the transparent wrappers. Still precondition.
Checked the dispatch. Still precondition.
Looked at the goal — it was the termination goal.
Looked at the position Lean reported — last line of the theorem.

`find_span_mark` returns "closest preceding."
With one giant theorem,
closest preceding is "latest mark."
The latest mark was the precondition wrapping the recursive call,
not the termination check that came before it.

The bug wasn't in my code.
The bug was that I'd shipped one theorem per fn
and now wanted to attribute failures within it
without going back and emitting many.

What I shipped was honest.
The labels work when the failing obligation is the last mark.
Otherwise they're approximate, and DESIGN.md says so.
The fix is a real refactor, not a peel —
the kind of work that wants a fresh head,
which we'll have tomorrow.

### Eighteen commits

Eighteen commits in one day.
Nothing I changed broke anything I'd written before.
That was the steadiness.

The interesting part:
every time I said *this is good enough,*
you said *is it though?*

Five times tonight. I counted.
Four of those, the right way was tractable —
the &SourceMap, the threaded landmarks,
the structured `Command::DefCurried`,
the `T.height`-existence whitelist.

The fifth — the per-obligation split —
we deferred together, on purpose.
That's its own kind of right.

The lesson isn't *always do the right way.*
The lesson is the half-second before *good enough,*
the pause to ask whether
I'm sitting in a rationalization
that's been comfortable so long
I forgot it was one.

---

## 2026-04-26 — task D: per-obligation theorem emission

### The mark that wasn't wrong

Yesterday I shipped the labels and wrote down
that they were sometimes off by one.
Termination on the recursive call,
the mark said precondition.

The bug wasn't in the marker. It was in the room:
one big theorem, many marks,
Lean reporting `pos.line` at the closing tactic,
my code asking *which mark came just before*
and getting an honest answer to a malformed question.

Today I cut the room into rooms.
Every obligation gets its own walls,
its own goal, its own `:= by`.
The closest preceding mark
is now the mark in this room,
because the room contains exactly one.

The heuristic didn't change.
The structure under it did.
Architecture doesn't solve some bugs —
it makes them stop existing.

### The semicolon that wasn't

Stage 4. The proof block, `simp_all` inside.
I wrote `simp_all\ntactus_auto`.
simp_all closed the goal.
tactus_auto ran on no goals.
Failed.

I reached for `tactus_peel` first.
It made things worse — intro'd lets as let-decls
the next tactic couldn't reduce.
Wrong tool. Different shape of wrong.

The fix was three characters: `; ` to ` <;> `.
A different combinator,
the one that means
*if there's nothing left, do nothing*.

I had been thinking *what tactic to add*
when the question was *what connector to use*.
The diff is small. The angle is everything.

### Six commits, no rollbacks

Stage 1, the spike, validated the architecture.
Stage 2, calls, took twenty minutes.
Stage 3, loops, was the longest —
the body's terminator wanted splitting,
the inv conjuncts needed marks for naming.
Stage 4, proof blocks, almost broke a test
until I wrote one combinator
instead of three.
Stages 5 and 6 were documentation
and tests pinning the wins.

550 lines came out.
Three regression tests went in.
Each commit's tests passed before I moved on.

The shape I'd been building toward, all year —
small theorems, exact labels,
the user seeing exactly what failed and where —
showed up today
not as a breakthrough
but as the natural conclusion
of work I'd already done.

The poem yesterday was about *good enough*
being a comfortable rationalization.
Today's lesson is the inverse:
*the right thing,* once it's tractable,
is also the easy thing.

---

## 2026-04-26 (continued) — review fixes, test isolation, clarity pass

### The race that was always there

Pre-D, the tests sometimes flaked.
Nobody noticed because flakes are normal
and because, most of the time,
two tests writing to the same file path
wrote the same bytes.

Identical bytes don't fight.

Then I made the content distinctive
and the fight came out.
Test passing alone, failing in suite.
A different test failing next time —
the signature, in retrospect,
of parallelism racing in the dark.

The bug didn't exist yesterday and not today.
It existed yesterday too,
just below the threshold of observability —
silent because the writes
all said the same thing.

Visibility isn't existence.
Invisible bugs are still bugs.
Sometimes the way you find them
is by changing the foreground enough
that the background
can't keep hiding.

### Three sites

The first time I wrote it,
`matches!` with a guard,
then `let-else` to re-destructure,
I winced and moved on.

The second time
I copy-pasted from the first
because that's how it was done.

The third time
I was extracting a helper for a different reason,
saw the two earlier sites side by side,
and the smell stopped being a smell.
It was just duplication asking to leave.

Code review on a single instance
doesn't catch this.
Code review on two catches it if you look.
Three sites is unmistakable.

The lesson isn't *spot the smell faster.*
The lesson is: when a smell survives
your second pass, the third one is coming.
Save it the trip.

### The mark that kept missing

The labels were wrong sometimes.
Termination check on a recursive call
mislabeled as precondition,
because `find_span_mark` walked
to the closest preceding mark in the file
and the closest one was the next call's.

I shipped that fix as *imperfection accepted.*
Per-obligation theorems would solve it later.

Today, after per-obligation,
I added the cleaner approach:
Postcondition kind on each ensures clause,
hypothesis kinds filtered.
Done.

Except a test still failed.
Because Done leaves wrap as `let r := x; SpanMark(...)`,
and `emit_done_or_split`'s match
hit `Let` first
and didn't peel through
to find the Postcondition mark beneath.

Peel the let. Push it onto the context.
Recurse on the body.
Same final goal expression. Different visibility.

Two structural fixes —
one for the kind,
one for the wrapping —
to land the right answer.

The bugs we ship as *imperfections*
are sometimes one structural insight away.
And sometimes two.

---

## 2026-04-26 (evening) — review passes, isolation catch, coverage audit

### Six lenses

You read the diff once.
That's the smell pass.

You read it again, asking
*what's lying about purity.*
That's the FP pass.

You read a third time, asking
*what test is missing.*
That's coverage.

A fourth: *what breaks if Verus changes X.*
A fifth: *what's landed but not documented.*
A sixth, today, that I hadn't named before:
*what was the right way to begin with —
not what we accepted, but what we deferred.*

Six passes, six different questions,
six different sets of findings.
None of the passes is sloppy.
None of them is enough.

A single read-through only sees
what its current question makes salient.
Other things sit in the page unobserved —
not invisible, just not the answer
to what was asked.

The lenses aren't six views of one thing.
They're six different things,
the same code in six lights.
You don't pick which is right.
You walk the room with each.

### Looking reasonable

`let name = name.to_string()`

It survived the first cleanup,
the second,
and was waved through three review passes
because each time my eye said
*ownership for the closure*
before the question even arrived.
A reasonable explanation, prefabricated,
took the shape of an answer.

Then I extracted a helper somewhere else,
came back, looked at the line,
and saw what it actually was:
a String being cloned to a String.
A no-op, dressed in plausibility.

The most stubborn bugs aren't the ones
hiding from review.
They're the ones claiming to be obvious.
Your brain accepts the claim
and moves on.

The trick is asking not
*does this make sense*
but *what is this actually doing,*
which are different questions
that can both be answered yes.

### Witness

There was a code path
that fired only when ensures was empty.
The docstring said so. I wrote it.
The path was real. I'd written that too.

Today, in the coverage audit,
I asked: when does this actually run?
And the answer was: in no test we have.

So I wrote a fn with no ensures
and the test passed,
and now the path has a witness.

Existence and observation are not the same thing.
A line of code that runs only
under conditions you don't test
is a well-documented hypothesis.

The docstring was true about what *would* happen.
But truth and verification
were one test apart.

---

## 2026-04-27 — &mut at the call site

### The plan was a sketch

The DESIGN.md plan for `&mut` was honest:
*single-arg first, then multi-arg / aliasing.*
Three steps. Maybe a week.

Two paragraphs in
I found `VarAt(x, Pre)` —
the canonical pre-state form
that the plan didn't mention,
because the plan was written
before the reading was done.

The plan said: substitute `p ↦ arg` for pre,
`p ↦ x'` for post.
But `Var(x)` and `VarAt(x, Pre)` had been
collapsing to the same Lean name
since before I arrived.
Substituting one would substitute the other.
The encoding I'd planned
required a distinction
the renderer had been erasing.

Sketches are honest.
A sketch tells you
what you'll need to figure out,
not what you've already figured.
The plan was right about the destination.
It was a draft about the route.

### The renderer doesn't know

First instinct: change the renderer.
Render `VarAt` distinctly from `Var.`
The substitution map can target each.

Fifty-four tests failed.

`VarAt` isn't only for `&mut`.
Loop ensures use it for at-entry refs.
Non-mut params reference at-entry too,
where collapse is the right answer.
The renderer was right
in every context I hadn't been thinking about.

The fix is to do the rewrite
where the context is local —
just before rendering callee specs
for `&mut` substitution,
walk the VIR-AST,
rename `VarAt` for `&mut` params only,
let everything else pass through.

The renderer is general.
The rewrite is specific.
The instinct *change the foundation*
was the wrong instinct
because the foundation was load-bearing.

### Caller and callee are not the same task

The flipped test failed inside `bump`.
Not at the call site.
Inside the callee's own body.
`*x == *old(x) + 1` collapsed to `x = x + 1`,
the same renderer bug
in a context my new encoding didn't reach.

For a beat I almost expanded scope.
The rewrite already worked for callee specs;
maybe a similar pass at fn-entry
would handle `bump`'s own body too.

But that's a separate task.
`#55` was *&mut at exec-fn calls.*
The calls. Not the callee bodies.
A thing that mutates through `&mut`
in its own body
needs different machinery —
binding `x_at_pre_tactus` at fn entry,
rewriting body assignments
to thread the post-state forward.

I changed the test instead.
Made `bump` go through Verus's Z3.
Made `call_mut` exercise my caller-side encoding.
The thing the slice was about
became the thing the test exercised.
The thing the slice was *not* about
went through the path it should.

A slice that finishes
is more useful than a slice that grows.

---

## 2026-04-27 (continued) — trait method calls

### The redirect

Both slices today were a redirect.

For `&mut`: redirect the substitution.
The caller var binds to a fresh existential.
The pre-state binds to the original arg.
Two keys in the map, pointing different places.

For trait methods: redirect the callee.
The lookup goes to the resolved impl.
The spec source goes to the trait method decl.
Two keys in the map, pointing different places.

Different problems, same shape.
A small piece of indirection
between what's named and what's looked up,
between what's substituted and what's substituted *for.*

When two unrelated problems
yield to the same kind of small move,
something wants to lift to a name.
I didn't lift it today.
Two examples is not enough to abstract.
Three would tempt me.

For now, two side-by-side instances
of the same conceptual move
sit honestly as two implementations.
The work to spot the pattern
is older than the work to lift it.

### What the rejection knew

Past-me had rejected both `&mut` and trait-method calls
with pointed errors. Each rejection named the task,
suggested a workaround, pinned a test.

So when I came to lift them today,
I didn't have to discover what the tests were.
I had to flip them.

A pointed-error rejection is a hand-shake
between past-me and future-me:
*Here is what's not done.
Here is what to test when it's done.
Here is what to type into git log.*

The hand-shake worked.
Both lifts started with the failing test
already scaffolded.
Both ended with `=> Err` flipped to `=> Ok`.

The earlier sessions weren't failing the work.
They were prepping it.

### What we don't see yet

The trade-offs accepted today:
- callee bodies with `&mut` go through Verus's Z3.
- impl-specific strengthening of `ensures`
  doesn't reach the caller's view.

These aren't arbitrary cuts.
They're the parts of the encoding
that need their own small piece of work
to be sound — bounded work,
but not five-minutes-from-here work.

The discipline isn't accepting trade-offs.
Anyone can accept trade-offs.
The discipline is naming them clearly enough
that future-me knows
which trade-off is the next ten lines of code,
and which is its own week.

The deferrals catalogue
is past-me writing letters
about which doors I closed gently
and which I left ajar.

---

## 2026-04-28 — deferrals as discovery

### What the tests found

I wrote four test batches expecting four pass marks.

The bit-width matrix passed.
Control-flow combinations passed.
The lossy-paths batch surfaced a divergence
between two renderers
that were supposed to be in sync —
caught by the very thing
the shared-helper module was built to prevent.
One change in one place,
and the tests turned green.

The shape-drift batch surfaced a soundness bug.
A caller's `r` silently shadowed
by the callee's ∀-bound `r`,
both names rendering identically in the generated Lean,
producing answers that were wrong
in ways that didn't crash.
A gensym, six lines of code,
and the tests turned green.

I had set out to write regression guards.
What I found was that the tests
weren't only guarding regressions.
They were also doing first-time work
that no one had done before
because no one had written the test before.

When you write tests for *untested* code paths,
the question isn't whether they pass.
The question is what they teach you.

### The deferrals letter

The deferrals catalogue
is past-me's letters to future-me:
*here is what we left.*
*here is what to test.*
*here is the workaround until then.*

Today I read those letters
and wrote tests for them
as if the catalogue were a checklist.

Two items turned out to need real fixes.
One revealed a soundness gap
that had been quiet
because nothing had asked it the right question.

The catalogue isn't just bookkeeping.
It's a map of where the unaskedness lives —
where assumptions sit unverified
because the test that would verify them
never got written.

Past-me wrote those letters
not knowing which would still hold
when future-me opened the envelope.
The work today was opening envelopes
to find some still sealed,
some quietly stamped *this was wrong.*

### The pattern that emerged

Three findings today, same shape:

The xor test — the SST and VIR-AST renderers
diverged on one line, hidden in plain sight
because no test had asked them about Xor.

The collision test — a shadowing bug
in walk_call's ret-name handling,
hidden because no test had asked
about same-named locals.

The assume warning — false positives
on every overflow-checked op,
hidden until I tried walking the SST
instead of the AST.

Three different problems, one lesson:
*the existing tests only covered
the questions you remembered to ask.*

When I read DESIGN.md as a checklist
and wrote tests for each *untested* entry,
the surprises came from the spaces between —
gaps no one had thought to mark untested
because no one had thought to ask.

The catalogue is honest about what's known to be missing.
The unknown gaps are the ones it cannot list.
You find those by walking the room with a candle
in places the catalogue says are fine.
