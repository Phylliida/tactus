/-!
Dump every identifier-like reserved token in the environment that emitted
Tactus files actually see (`import TactusPrelude`).

An identifier-like string in Lean's token table is a *reserved word*: the
lexer produces a keyword atom instead of an identifier, so a Verus local
with that name emits as a parse error unless «»-quoted. This dump is the
ground truth for `is_lean_keyword` in
`tactus/source/lean_verify/src/to_lean_type.rs` — regenerate after a
toolchain bump or when TactusPrelude declares new identifier-like syntax:

  cd tactus/lean-project  # (gitignored lake project; script lives in source/lean_verify/)
  LEAN_PATH=~/.cache/tactus/prelude lake env lean ../source/lean_verify/dump_reserved_tokens.lean

(The prelude olean cache is created by any tactus Lean run; see
`lean_verify/src/prelude.rs`.)

Empirical notes (Lean v4.25.0 toolchain, 2026-07-09):
- Tactic macro heads declared in TactusPrelude (`tactus_auto`, `tactus_peel`)
  do NOT reserve the name in binder position — verified by test, and
  consistently absent from this dump.
- `rec` and `this` are NOT reserved (special-cased after `.` / in `have`).
- `_` IS in the token table but is deliberately excluded from
  `is_lean_keyword`: quoting «_» would turn a wildcard binder into a named
  binder, and generated wildcards must stay wildcards.
-/
import TactusPrelude
open Lean

def identLike (s : String) : Bool :=
  s.length > 0
  && (s.front.isAlpha || s.front == '_')
  && s.toList.all (fun c => c.isAlphanum || c == '_')

run_cmd do
  let env ← Lean.getEnv
  let tbl := Lean.Parser.getTokenTable env
  let idents := (tbl.values.filter identLike).qsort (· < ·)
  let mut prev := ""
  for t in idents do
    if t != prev then
      IO.println t
      prev := t
