# bootstrap-85 — deref-decoration on non-Ref terms in stmt emission (2 live e2e reds)

Status: **CARDED 2026-08-06 (found by b83's revived tactus e2e suite —
both PRE-EXISTING, reproduced at fb1fcba7; suite had not run in the
standing battery since at least b68 because the full-e2e recipe
fail-fasts at the examples_state_machines pair). DESIGN NOT PROPOSED.
NOT STARTED.** Two e2e tests, one bug class: the ref-decoration
(`wrap_body_with_param_derefs` family) applies `.deref` to terms that
are not Ref-typed, emitting ill-formed Lean in the per-fn stmt modules.

## Frozen repros

**Bug A — `test_exec_generic_with_wrapper_instantiation_probe`.**
Subject: `let b: Box<u8> = Box::new(7); always_true(&b)`. The emitted
`TactusStmts_test_crate_exec__test_crate__caller.lean:6` contains

```
∀ (_h_hoist_1 : 0 ≤ 7.deref ∧ 7.deref < 256) (tmp__1 : Tactus.Box Int) …
```

— the u8 literal's IntegerTypeBound hyp got `.deref` appended to the
LITERAL `7`; Lean parses `7.deref` as a decimal-point error
("unexpected identifier after decimal point"). The hyp should be
`0 ≤ (7 : Int) ∧ (7 : Int) < 256` (a literal has no deref).

**Bug B — `test_exec_package_check_smoke`.** Subject:
`pub fn first_or_zero(v: &Vec<u8>) -> u8 { if v.len() > 0 { v[0] } else { 0 } }`.
The emitted stmt module has `Int.deref` applied to
`test_crate.seq.Seq.index Int (test_crate.view.View.view v) (Int.ofNat 0)`
(an Int-typed term) — "The environment does not contain `Int.deref`".

Both: stmt olean build fails → per-fn error → package gate skipped.
Both tests pass `--output-json`-clean otherwise; no census lines
involved.

## Suspected mechanism (unverified at card time)

The ref-decoration wrapper substitutes a Ref-typed PARAM with an
arbitrary ARG term (literal `7`; a fully-applied `Seq.index …` Int
term) and appends `.deref` unconditionally instead of gating on the
arg's rendered type/head. Both repros sit in the call-ensures
instantiation path (callee ensures/bound-hyps flowing into the
caller's stmt module). The fix should be a TYPE-gated wrap (decorate
only when the substituted term is actually Ref/Box-headed), not a
string special-case — b81 retrospective: find where production
decides the wrap and mirror THAT predicate.

## Done-when (when picked up)

- Both tests green; a probe13-class mutation pin each if the fix
  touches the cert path (it likely stays stmt-side).
- Full tactus suite 562/0; battery per convention.
- The b83 recipe note (HANDOFF) already covers why these were
  invisible; consider the standing full-e2e form (`--no-fail-fast`)
  so a future red suite is loud.
