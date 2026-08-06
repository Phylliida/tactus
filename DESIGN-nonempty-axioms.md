# Nonempty-bracketed axioms — scoping (2026-07-03)

Arc plan for REVIEW-2026-07-02 § 1.1 (the top soundness finding): the
emitted Lean axiom environment is INCONSISTENT. Scoped with the N0
de-risking experiments already run; implementation is a follow-up
session.

> **ARC COMPLETE (same day).** N0′ pinned both exploits in-harness
> (they VERIFIED — False derived end-to-end); N1 bracketed generated
> axioms (Seed 2 + proj-typed needs propagating SUBSTITUTED +
> order-flip so proj bounds ride the impl_subst rewrite + @-form
> haves + wrapper Nonempty instances); N2 bracketed `Tactus.index`
> (Seed 3: index isn't a Call — scan element typs directly); N3
> covered ∃-conclusions (Seed 4, ensures-only) and wrote the
> model-existence argument into DESIGN.md § "Axiom-environment
> consistency". Both exploit pins now assert
> Err(failed to synthesize Nonempty Empty). Implementation surprises
> worth remembering: trait method DECLS must be excluded from Seed 2
> (they emit as class fields; seeding them cascaded premises onto
> instances and broke typeclass resolution); the broadcast-axiom
> emission path had its own augment ordering to flip; substituted
> proj needs that land concrete must be SKIPPED (Lean resolves them;
> recording renders unrewritable names). Gates at every phase: e2e
> 524/0, vstd 1530/0, group-theory 2820/32 (error set identical to
> baseline; verified count +9).

## The hole (verified)

Value-producing axioms over bare type params globally inhabit every
type. Two confirmed exploitable shapes:

```lean
axiom seq.Seq.index (A : Type) (self : seq.Seq A) (i : Int) : A   -- generated (vstd spec fn)
axiom Tactus.index {α : Type u} {n : Nat} (a : Vector α n) (i : Int) : α   -- prelude static (pre-b82 form; b82 made it a [Nonempty α]-bracketed noncomputable def)
```

`(Seq.index Empty (Seq.empty Empty) 0).elim : False` elaborates
(verified 2026-07-03); `Tactus.index (α := Empty)` on the empty vector
is the same hole. SMT never had this problem — SMT sorts are always
inhabited; Lean types can be empty. Not reachable by the tactus_auto
ladder (every green result is almost certainly genuinely green), but
user tactic bodies are free-form Lean, and the proof-factory game
makes proofs adversarial input. The kernel should enforce what
convention currently carries.

## Soundness story (to be written out in the implementation)

Goal: after bracketing, the emitted axiom set has a MODEL —
* every abstract type former (`axiom T : Type → Type`) interprets as
  `fun _ => Unit` (the pipeline already emits unconditional
  `axiom <T>.instInhabited … : Inhabited (T …)` instances — coherent
  with this model, and they're exactly the instances that DISCHARGE
  `[Nonempty A]` brackets at abstract-type instantiations);
* every value-producing axiom `… → A` carries `[Nonempty A]` — under
  the bracket, "some element of A" exists by assumption, so the axiom
  is satisfiable;
* Prop-valued axioms are satisfiable over that model given the above
  (CAVEAT, phase N3: a Prop axiom `∃ x : A, …` over a bare param is
  value-producing via `Classical.choice` — same bracket needed).

## Surfaces (all located)

1. **Generated axiom decls** — `to_lean_fn.rs:~253`
   (`Command::Axiom { binders, ret_ty }` for bodyless/cross-crate spec
   fns). Seed rule (conservative, over-approximating is harmless): any
   typ param appearing ANYWHERE in the axiomatized fn's ret typ needs
   `[Nonempty]`. Over-bracketing `Seq A`/`Option A` returns costs an
   extra instance binder that auto-discharges; refinement can come
   later.
2. **Broadcast lemma axioms** — `broadcast_lemma_axiom_cmd`
   (`to_lean_fn.rs:321`): Prop-valued, NOT value-producing per se —
   deferred to N3 (∃-over-bare-param conclusions only).
3. **Prelude statics** — 7 axioms in TactusPrelude; `Tactus.index`
   confirmed needing `[Nonempty α]`; audit the other 6 during N2.
4. **Instance dischargers** — already exist: unconditional
   `instInhabited` axioms per abstract type; user datatypes emit
   `deriving Inhabited` (Lean derives `Nonempty` from `Inhabited`).

## N0 experiments (RUN, results pinned here)

* **Bare `have _bc := axiom` BREAKS on bracketed axioms** —
  "typeclass instance problem is stuck, `Nonempty ?m`" (instance
  implicits are maximally inserted; the metavar A can't synthesize).
  This is today's broadcast-have injection form
  (`sst_to_lean.rs:~954`).
* **`have _bc := @axiom` works** — no eager instantiation — AND the
  @-bound ∀-hypothesis remains simp_all-usable at concrete
  instantiations (probe verified). ⟹ the have injection switches to
  `@`-form (uniformly — harmless for unbracketed axioms).

## Phases

* **N0′ — the exploit pin, FIRST.** An e2e test with a user tactic
  deriving False via `Seq.index Empty (Seq.empty Empty) 0` — today it
  VERIFIES (scandal, in-harness); after the arc it must be
  `Err(failed to synthesize Nonempty Empty)`. This drives and
  witnesses the whole fix.
* **N1 — generated axioms.** Extend `nonempty.rs` with the new seed
  rule (axiomatized fn + param in ret typ); brackets ride the existing
  `add_fn_nonempty_bounds` + propagation dataflow (fns REFERENCING
  bracketed axioms at param typs already propagate). Switch broadcast
  haves to `@`-form. Gates: full suite + group-theory (the krate-wide
  broadcast union is the churn detector — watch the 32-error set for
  drift, not just the count).
* **N2 — prelude statics.** `[Nonempty α]` on `Tactus.index`; audit
  the other 6; update in-prelude users.
* **N3 — ∃-conclusion Prop axioms** + write the model-existence
  argument into DESIGN.md as the standing soundness note.

## Risks / open questions

* **Churn in vstd-heavy crates**: every bracketed axiom's use at a
  param typ inside a generated theorem needs the theorem's binders to
  carry `[Nonempty T]` — the existing propagation covers fn-level
  flows, but broadcast-have usage inside tactic proofs at param typs
  is synthesized by Lean at rewrite time; if group-theory shows stuck-
  instance errors, the fallback is bracketing the THEOREM's typ params
  wherever its have-set contains bracketed axioms (coarser, still
  sound).
* **The `Type u` universe** on `Tactus.index` (`{α : Type u}`) —
  bracket as `[Nonempty α]` works at any universe; no issue expected.
* Estimate: **1–2 sessions**, N0′+N1 being the bulk.
