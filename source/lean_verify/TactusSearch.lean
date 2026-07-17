-- TactusSearch.lean — the discover-mode search ladder: tactus_first,
-- tactus_auto, tactus_case_split, tactus_usize_bound, tactus_bit_vector.
-- Imported only by artifacts whose USER tactic texts reference these
-- tactics (overrides / inline proofs) — never by default emission
-- (B5, DESIGN-transparent-automation.md §5; the B6 gate asserts
-- "no artifact imports the search module").
--
-- (Split from the former TactusPrelude.lean, 2026-07-17.)
import TactusDefs
-- TactusDefs slims its import to `Lean.Elab.Command`, whose closure
-- lacks `bv_decide` (syntax AND elaborator) — the `tactus_bit_vector`
-- macro below quotes `bv_decide` tactic syntax, so the import is
-- needed here even before any use.
import Lean.Elab.Tactic.BVDecide
-- `tactus_first | t1 | t2 | …` desugars to `first | (t1; done) |
-- (t2; done) | …`. Each alternative is required to fully close
-- the goal — without `done`, a tactic that succeeds while
-- leaving unsolved subgoals (e.g., `simp_all` in some
-- configurations) commits early and blocks later alternatives.
-- `tactus_first` makes the closure contract explicit at the
-- combinator name rather than relying on every alternative to
-- remember to append `; done`.
syntax "tactus_first" ("|" tacticSeq)+ : tactic
macro_rules
  | `(tactic| tactus_first $[| $ts:tacticSeq]*) => do
    let wrapped ← ts.mapM (fun t => `(tacticSeq| ($t:tacticSeq); done))
    `(tactic| first $[| $wrapped:tacticSeq]*)

-- `tactus_case_split closer`: try each user-datatype-typed
-- local in turn, running `closer` on each subgoal produced by
-- `cases`. Commit the first candidate where `closer` closes ALL
-- subgoals; restore state and try the next candidate
-- otherwise. Throws if no candidate works (so it composes with
-- `tactus_first` / `first` for fallthrough).
--
-- "User datatype" is gated on having a companion `.height` fn
-- (emitted by `to_lean_fn::height_fn_for_datatype` for every
-- concrete non-generic datatype — see DESIGN.md "Non-int
-- decreases"). This filters out `Int` / `Nat` / `Bool` /
-- `Option` / core types that have their own automation (omega)
-- and would explode the subgoal count if case-split.
--
-- Two candidate shapes are recognised:
-- 1. Direct: `local : T` where `T.height` exists. We case-split
--    on `local`, the standard shape.
-- 2. Wrapper: `local : Tactus.X T` (where X is Ref/MutRef/Box/Rc/
--    Arc) and `T.height` exists. We case-split on `local.deref`,
--    which has type T. Needed for fns taking `&T`/`Box<T>`/etc.
--    params after the body-shadow drop (β refactor Piece 1) — the
--    local's Lean type carries the wrapper distinguishability,
--    but the obligation reasons about the inner T's structure.
--
-- Trying each candidate (rather than just the first) means a fn
-- with multiple datatype locals — e.g., `(a: Foo, b: Bar)` —
-- works regardless of which one is the right scrutinee. Cost is
-- O(n_candidates × closer_cost), bounded by the locals in
-- scope.
open Lean Elab Tactic Meta in
elab "tactus_case_split" closer:tacticSeq : tactic => do
  let goal ← getMainGoal
  -- Each candidate is (LocalDecl, needsDeref?). needsDeref=true
  -- means the local has Tactus wrapper type and we case-split on
  -- `local.deref` instead of `local`.
  let candidates ← goal.withContext do
    let ctx ← getLCtx
    let env ← getEnv
    let mut out : Array (LocalDecl × Bool) := #[]
    for decl in ctx do
      if decl.isImplementationDetail then continue
      let ty ← whnf decl.type
      let .const name _ := ty.getAppFn | continue
      -- Direct case: name itself is an inductive with .height.
      if let some info := env.find? name then
        if info matches .inductInfo _ then
          let heightName := Name.str name "height"
          if env.find? heightName |>.isSome then
            out := out.push (decl, false)
            continue
      -- Wrapper case: Tactus.X T whose inner T has T.height.
      let isWrapper :=
        name == ``Tactus.Ref || name == ``Tactus.MutRef
          || name == ``Tactus.Box || name == ``Tactus.Rc
          || name == ``Tactus.Arc
      if isWrapper then
        let args := ty.getAppArgs
        if h : args.size > 0 then
          let innerTy ← whnf args[0]
          if let .const innerName _ := innerTy.getAppFn then
            if let some info := env.find? innerName then
              if info matches .inductInfo _ then
                let heightName := Name.str innerName "height"
                if env.find? heightName |>.isSome then
                  out := out.push (decl, true)
    return out
  for (decl, needsDeref) in candidates do
    let saved ← saveState
    try
      if needsDeref then
        -- `cases h : <local>.deref` names the discharged-term equation
        -- so subsequent simp_all can substitute occurrences. Without
        -- the `h :` form, `cases <local>.deref` case-splits but
        -- doesn't propagate the value into the goal's other
        -- references to `<local>.deref` (since `<local>.deref` is a
        -- term, not an fvar).
        let h_name ← mkFreshUserName `h_split
        let h_ident := mkIdent h_name
        let localIdent := mkIdent decl.userName
        evalTactic (← `(tactic| cases $h_ident:ident : ($localIdent).deref))
      else
        let subgoals ← goal.cases decl.fvarId
        setGoals (subgoals.map (·.mvarId)).toList
      evalTactic (← `(tactic| all_goals ($closer)))
      -- All goals closed if we got here.
      return
    catch _ =>
      restoreState saved
  throwError "tactus_case_split: no datatype-local case-split closes the goal"

-- `tactus_usize_bound`: discharge a goal involving `usize_hi` /
-- `isize_hi` (i.e., `2 ^ arch_word_bits` or `2 ^ (arch_word_bits -
-- 1)`) by case-splitting on `arch_word_bits_valid` and reducing
-- the resulting concrete `2 ^ 32` / `2 ^ 64` literals. The
-- `tactus_auto` toolbox (rfl/decide/omega/simp_all) can't handle
-- symbolic exponents, so usize/isize arithmetic obligations
-- normally need an explicit `proof { tactus_usize_bound }` block.
--
-- Order of operations:
-- 1. `rcases` arch_word_bits_valid into the two literal cases.
-- 2. `subst` substitutes 32 or 64 throughout the goal.
-- 3. `simp_all only [usize_hi, isize_hi]` unfolds the defs to
--    expose the `2 ^ ...` literal.
-- 4. `decide` (for purely-arithmetic-on-literals goals) or
--    `omega` (for linear-arith with the literal as a constant)
--    closes the case.
--
-- Composes with `tactus_first` so users can layer it: e.g.,
-- `tactus_first | tactus_auto | tactus_usize_bound | ...`.
macro "tactus_usize_bound" : tactic => `(tactic|
  rcases arch_word_bits_valid with h | h <;>
    (subst h; simp only [usize_hi, isize_hi]; first | decide | omega))

-- `tactus_bit_vector`: closer for `assert(…) by(bit_vector)` goals
-- (#111 / #130). The goal is rendered in BitVec mode — u-typed
-- variables get wrapped as `BitVec.ofInt n x`, and bitwise/
-- arithmetic ops resolve to BitVec instances. Lean's BitVec
-- tactics then handle the reasoning.
--
-- Ladder:
-- 1. `intros` — strip any `req → ens` implication.
-- 2. `decide` — closes concrete cases like `(5 ^^^ 3 : BitVec 8) = 6`.
-- 3. `simp_all` with BitVec lemmas — handles commutativity,
--    associativity, identity (`x ^^^ 0 = x`), x ^^^ x = 0, etc.
--    Mathlib's `Mathlib.Data.BitVec` has the relevant lemmas
--    tagged `@[simp]` so plain `simp_all` picks them up.
-- 4. `fail` with a workaround hint.
--
-- Future (#130 follow-up): introduce fresh `BitVec n` witnesses
-- with bound-hypothesis bridges so `bv_decide` (full SAT-backed
-- decision procedure) becomes viable for parameterized terms.
-- Today's ladder handles algebraic identities cleanly via simp;
-- richer reasoning needs the bridge.
macro "tactus_bit_vector" : tactic => `(tactic|
  first
    -- `bv_decide` is Lean core's full SAT-backed bit-vector
    -- decision procedure (in `Lean.Elab.Tactic.BVDecide`). It
    -- handles both free `BitVec n` vars AND parameterized
    -- `BitVec.ofInt n x` terms — closes general bit-vector
    -- identities including XOR/AND/OR commutativity,
    -- associativity, distributivity, identity laws, masking,
    -- etc. Tactus renders u-typed operands as `BitVec.ofInt n x`
    -- so users can write any algebraic / decidable bitwise
    -- assertion and have it close.
    | (intros <;> bv_decide)
    | bv_decide
    -- Fallbacks for goals bv_decide can't (somehow) handle:
    -- structural equality reduction via decide (concrete cases),
    -- then simp_all (Mathlib BitVec lemmas).
    | (intros <;> decide)
    | decide
    | (intros <;> simp_all)
    | simp_all
    | fail "tactus_bit_vector: could not discharge — try \
       `assert(P) by { … }` with a Lean tactic instead")

-- Tactus: the *atomic closer* used at the leaves of the tactics we emit.
-- Intentionally kept to simple, always-closing tactics — `rfl`,
-- `decide`, `omega`, `simp_all`, and `tactus_case_split` for goals
-- that need case analysis on a user datatype (recursive-enum fns,
-- #58).
--
-- Any structural peeling (`refine ⟨?_, ?_⟩`, `intros`, etc.) is the
-- codegen's job, not this macro's: the emitter knows exactly what
-- goal shape each theorem has, and wraps the right structural
-- tactics around `tactus_auto` calls. See `sst_to_lean`'s loop-
-- theorem emission.
--
-- `tactus_first` enforces that each alternative closes the goal
-- (wraps each in `; done`), preventing partial-success tactics
-- like `simp_all` from blocking later alternatives.
--
-- `fail` turns "nothing worked" into a real error instead of a `sorry`.
--
-- **The `simp_all <;> omega` rung — composition, not a bigger simp set.**
-- `omega` does not substitute a `let`-bound value: a goal guarded by a
-- synthetic binding (e.g. Verus's read-before-write snapshot for a
-- self-assignment, `let tmp% := x; … tmp% * k < 2^n`) leaves `tmp% * k`
-- and the asserted `x * k ≤ B` as DISTINCT opaque atoms, so bare `omega`
-- (and bare `simp_all`, which zeta-reduces the `let` but isn't an
-- arithmetic decision procedure) both fail. `simp_all <;> first | omega
-- | done` zeta-reduces the binding (unifying the atoms) and THEN runs
-- `omega`. This combo already existed in the ladder, but only inside
-- `tactus_case_split`, which throws when there's no user-datatype local
-- to split on — so a plain `Int`-typed let-guarded goal never reached
-- it. Lifting it to a standalone rung is the "layered composition, not
-- exclusive gates" shape; it strictly subsumes the bare `simp_all` rung
-- it replaces (if `simp_all` closes the goal, `<;>` runs on zero goals).
-- It is NOT a simp-set extension — no new lemmas — so design principle
-- #1 holds (it composes tactics already present rather than teaching the
-- closer new facts). Closes the BUG-synthetic-temp-let-blocks-asserted-
-- bounds class (factorial / power / modular-multiply iterative impls).
--
-- **Why still no extras in `simp_all`'s set.** Beyond that composition,
-- the closer stays intentionally dumb — NO extra simp lemmas. When a
-- real obligation falls through, the preferred response is for the user
-- to write the proof explicitly: `assert(P) by { simp_all [SomeLemma] };`
-- or a `proof { ... }` block. This matches Tactus's design principle #1
-- (Transparency) and the user's stated UX preference: a visible proof is
-- a more pleasant proof. See DESIGN.md § "Bool vs Prop" for the
-- canonical example (Bool xor commutativity is closable with `simp_all
-- [Bool.xor_comm]` at the assertion site, NOT by extending the closer).
macro "tactus_auto" : tactic => `(tactic|
  tactus_first
    | rfl
    | decide
    | omega
    | (simp_all <;> first | omega | done)
    | tactus_case_split (simp_all <;> first | omega | done)
    | tactus_case_split (simp_all)
    | fail "tactus: auto-tactic failed — add explicit proof block")
