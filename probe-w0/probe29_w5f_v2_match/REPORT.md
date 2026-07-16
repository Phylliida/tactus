# probe29 — W5f v2 MATCH decode: the faithful `Match` denotation (board bootstrap-56)

**Status:** PASS ✓ (rc=0, ~3.7s, `lean` against the real emitted `lib.*`).
**Axiom closures:** every probe28 fact carries over unchanged; the three new Match
facts — `adequacy_leaf_match_hd` `[propext]`, `adequacy_leaf_match_tl` `[propext]`,
`adequacy_leaf_match_prop_hd` `[propext]`. **No `sorryAx`, no `Classical.choice`.**
`render_exp`/`render_arms` reduce (structural); `eval`/`evalList`/`evalArms` and
`edenote`/`edenoteArms` reduce (mutual structural); `bindArm` reduces (structural);
arm selection is a decidable `ctorTag v = c` (`Int.decEq`, constructive).

Run: `probe-w0/probe29_w5f_v2_match/run.sh` (`LEAN=<lean>` to override). Elaborates
`w5f_v2_match_sem.lean` against `tactus-core/out/lib` — NO tactus-core rebuild.
Extends probe28 (the full v1 core + the four v1 + four v2 adequacy facts carried
verbatim).

## The census (the card's required pre-check)

bootstrap-56 required confirming how often `Match` appears **directly in an
obligation goal** (`GoalData.LeafE`) before investing. Grepped every emitted
`.lean` for `MatchR`/`ExprData.Match`. All occurrences fall into three buckets:
1. the datatype/def machinery (`height`/`render_arms`/`expr_eq`/`expr_size`) —
   definitions, not goals;
2. `defs_expr_vocab_kernel_computes` — the deliberate `render_exp` vocab test;
3. `target/tactus-lean/lib/cert/tree_head.defcert.lean` — a **`DefData` BODY** cert
   (`render_def cert_tree_head_raw = cert_tree_head_defdata`), i.e. `Match` inside a
   spec-fn body reached through the pinned `E.fn` oracle — NOT a `LeafE`.

**Result: zero `Match`-directly-in-obligation on the available slice.** This
confirms the card's low-urgency note. The value of this rung is therefore
**completeness** — `eval`/`edenote` are now faithfully **total** over the full
`ExprData` vocab, with no sentinel — the last honest gap in the W5f leaf
denotation, not coverage of a common goal shape. (Danielle's steer agreed: clean
foundation before hardening the environment pins.)

## What v2-Match adds

probe28 left `Match` (`ExprData.Match`) as a sentinel (`0` in `eval`, `True` in
`edenote`) — the one node the v2 grounding realization did not reach, because the
flat-Int `St := Int → Int` model stores every datatype value as an `Int` and a
faithful `match` must **decode** that Int back to a constructor tag + field values.
v2-Match lands that decode layer:

- **Two new `SymEnv` oracles.** `ctorTag : Int → Int` (scrutinee value → its
  constructor id) and `ctorField : Int → Nat → Int` ((value, 0-based field index) →
  field value). Pinned by the concrete crate literal **consistently with the
  emitter's constructor encoding** — the same P5 oracle discipline as `fn`/`fnN` (a
  plain lookup, no fuel; the constructor encoding lives in the emitted defs). This
  is the flat-Int inverse of the `emb : U ↪ Int` embedding used at the `Forall`
  binder (`toProp_all_embed`).
- **`bindArm E v bs i st`** — standalone **structural** fold over `BinderIdList`:
  the k-th pattern binder in `bs` is bound to `E.ctorField v (i+k)`, threaded into
  the state via `upd`. Not part of the eval mutual family (never calls `eval`).
- **`evalArms`** joins the `eval`/`evalList` **mutual structural** block over the
  `ExprData`/`ExprList`/`ArmList` mutual inductive family:
  `eval (Match s arms) = evalArms E (eval s) arms`; `evalArms (Cons c bs body tl) =
  if ctorTag v = c then eval body (bindArm …) else evalArms … tl`.
- **`edenote`/`edenoteArms`** become a **mutual pair** — the prop-position mirror
  (`edenote (Match s arms) = edenoteArms E (eval s) arms`).

`eval`/`edenote`/`evalList`/`evalArms`/`edenoteArms` are now **total and faithful**
over the entire `ExprData` vocabulary (no sentinel remains except the genuinely
ill-sorted `Forall`/`Exists`-in-value-position and `OpKind.other`, which are correct
as sentinels).

## Why the decode is via oracles (and what the facts state)

In the flat-Int model the scrutinee denotes `eval E scrut st = v : Int` where `v`
is `emb u` for the user datatype value `u`. There is no in-Lean constructor
encoding to structurally invert; the decode must be a `SymEnv` oracle *consistent*
with whatever produced `v` (exactly as `fn`/`fnN` are pinned to the emitted defs).
So the faithfulness facts state **arm SELECTION + binder THREADING** with the
`ctorTag` value as a hypothesis (as FACT 5/8 take `hfn`/`hfnN`, and FACT 6 leaves
the body arbitrary) — the concrete crate `SymEnv` literal discharges the hypothesis
by `rfl`/`decide`. The arm body then reads the threaded slot through `E.av`/`E.avP`,
resolved at instantiation exactly like `toProp_all_embed` resolves the `Forall`
binder. This is the honest, composable register — not a claim that the decode
re-proves the user's datatype semantics.

## The three new facts (all over the REAL `lib.render_exp`/`lib.render_arms`)

The shared shape: scrutinee `Var scrutId (TyNamed 100)`, two arms —
`arm0 = ctor c0 binds [xId] ⇒ body xId`, `arm1 = ctor c1 binds [yId,zId] ⇒ body 0`,
result type `TyInt` (so `needs_nat_coercion _ TyInt = 0`: `render_arms` inserts no
cast on any arm body).

| # | Fact | What it pins | Axioms |
|---|---|---|---|
| 9 | `adequacy_leaf_match_hd` | `ctorTag v = c0 ⇒ eval(render(match …)) = E.av xId (upd st xId (ctorField v 0))` — tag selects arm0; the arm-0 binder `xId` is bound to field-0 and read back through the threaded state | `[propext]` |
| 10 | `adequacy_leaf_match_tl` | `ctorTag v ≠ c0 ∧ ctorTag v = c1 ⇒ eval(render(match …)) = 0` — `evalArms` **walks past** arm0 to arm1 | `[propext]` |
| 11 | `adequacy_leaf_match_prop_hd` | `ctorTag v = c0 ⇒ edenote(render(match …)) ↔ E.avP xId (upd st xId (ctorField v 0))` — the **prop-position** mirror (exercises `edenote`/`edenoteArms`) | `[propext]` |

FACT 9 is the headline: it exercises **both** new mechanisms at once (arm selection
by `ctorTag`, binder binding by `bindArm`/`ctorField`, leaf read of the bound slot).
FACT 10 exercises the recursive arm **walk**. FACT 11 lifts the same to prop
position (`assert(match …)`).

## Honest scope / what's partial

- **The decode oracles (`ctorTag`/`ctorField`) are pins, not proofs.** They are the
  flat-Int inverse of the emitter's constructor encoding, discharged by the crate
  `SymEnv` literal — exactly as `fn`/`fnN`/`av`/`opk`/`proj` are. A cross-crate
  probe pinning `ctorTag`/`ctorField` to an actual fixture-emitted datatype
  encoding (rather than a hypothesis) is the natural strengthening, mirrored on the
  same open item as the FACT 5/8 grounded-`g`/`h` strengthening.
- `eval`/`edenote`/`evalArms`/`edenoteArms`/`bindArm` are **definitions we wrote** →
  spec-adequacy (master plan §8.5), audited-once, not trusted. Faithfulness to the
  user's `match` Prop is the `rfl`/`simp only`-bridge over the real `render_exp`,
  validated on the arm-selection (hit + walk) and binder-threading classes.
- The `evalArms`/`edenoteArms` no-match default (`0` / `True`) is the total-function
  fallback; a well-typed exhaustive `match` always hits an arm, so it is never
  reached in a faithful lowering.
- Census is over the currently-emitted slice (fixtures + one real defcert). The full
  tgt group-theory obligation corpus is not emitted into this crate's `out/`, so the
  "zero-in-obligations" figure is a strong signal, not an exhaustive proof over
  every crate. Bodies (where `Match` does live, commonly) are handled by the fn-pin.

## Relationship to the board

Closes `bootstrap-56`. The last node of the W5f v2 leaf denotation is now faithful;
the natural next strengthening (shared with FACT 5/8) is a cross-crate probe that
pins the oracles — including `ctorTag`/`ctorField` — to a real fixture-emitted
datatype/spec-fn rather than a hypothesis.
