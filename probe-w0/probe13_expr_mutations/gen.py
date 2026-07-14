#!/usr/bin/env python3
"""W6e expression-level mutation-kill generator (bootstrap-24).

The Friction-2 kill, made systematic. W6d wired the DEEP bridge:
`goals_eq (ref_wp ctx sst) goals = 1`, where the LEFT side (`ref_wp`)
INDEPENDENTLY re-derives each obligation's expression tree via the trusted Lean
`render_exp`, and the RIGHT side (`goals`) is the production serializer's
`ExprData` output. The blind spot W6 exists to close: a stage-A string / atom-id
compare reused the SAME renderer on both sides, so a serializer that produced a
structurally-wrong `ExprData` (dropped an `Int.toNat`, dropped a `.deref`, wrong
field accessor, wrong overflow bound) would render a "right-looking" string and
SILENT-PASS. The deep symmetric compare against the independent `render_exp`
must instead FLIP the bridge 1 -> 0.

This harness proves it, positively and by `decide`, for the four coercion-drop
classes — one class per fixture fn, each on its own live cert:

  * cast_drop    (sum_to,     nat-coercion / cast class): drop an `Int.toNat`
  * deref_drop   (head_exec,  G2 auto-deref):             drop the `.deref` FieldProj
  * wrong_field  (mk_point,   G3 struct field):           emit a WRONG field accessor
  * wrong_width  (add_capped, G6 HasType overflow):       2^64 bound -> 2^32

For each: extract the live cert's ctx/sst/goals VERBATIM, apply a single
STRUCTURAL text mutation to the GOAL side only (`ref_wp`/ctx/sst untouched, so
the reference re-derivation stays correct), and assert BOTH
    goals_eq (ref_wp ctx sst) goals      = 1 := by decide   (baseline closes)
    goals_eq (ref_wp ctx sst) goals_mut  = 0 := by decide   (the kill flips)
A single `lean` elaboration with rc=0 proves every baseline closes AND every
single-edit mutation is provably rejected. If ANY mutation fails to flip, its
`= 0` example errors and rc != 0.

The mutations are pattern transforms (drop/replace a NODE), NOT hard-coded leaf
ids, so the suite survives a fixture regen that renumbers leaves. Each mutation
asserts it actually changed the text (a regen that removed the target shape
fails loud here, signalling the harness needs updating — never a silent no-op).
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
CERTDIR = ROOT / "bootstrap-fixture/out/lib/cert"


def match_paren(s, i):
    assert s[i] == '(', f"expected '(' at {i}, got {s[i]!r}"
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '(':
            depth += 1
        elif s[j] == ')':
            depth -= 1
            if depth == 0:
                return j
    raise ValueError("unbalanced")


def extract_def(text, name):
    """Return the one-line RHS term of `@[reducible] def <name> ... := <RHS>`."""
    m = re.search(rf"def {re.escape(name)}\b.*?:=", text)
    if not m:
        sys.exit(f"def {name} not found")
    for ln in text[m.end():].split('\n'):
        if ln.strip():
            return ln.strip()
    sys.exit(f"def {name}: no RHS line")


# ── the four coercion-drop mutations (GOAL-side structural transforms) ──
# Each takes the goals RHS text and returns the mutated text. Each asserts the
# transform actually fired (mut != goals), so a fixture regen that removed the
# target shape fails loud instead of silently producing a no-op "kill".

def drop_first_cast(goals):
    """cast class: drop the first `Int.toNat` — `Cast IntToNat (Box (Atom N))`
    -> bare `Atom N`. The reference render_exp still materializes the cast from
    the nat-typed operand, so LHS diverges."""
    mut = re.sub(
        r"\(lib\.ExprData\.Cast lib\.CastKind\.IntToNat "
        r"\(Tactus\.Box\.mk \(lib\.ExprData\.Atom (\d+)\)\)\)",
        r"(lib.ExprData.Atom \1)", goals, count=1)
    assert mut != goals, "cast_drop: no `Cast IntToNat (Box (Atom N))` found"
    return mut


def drop_deref(goals):
    """G2: drop the `.deref` auto-coercion — `FieldProj (Box (Atom N)) 0`
    (field 0 = deref_field) -> bare `Atom N`. The reference derives `.deref`
    from the arg's `TyRef` tag, so the App arg diverges."""
    mut = re.sub(
        r"\(lib\.ExprData\.FieldProj \(Tactus\.Box\.mk "
        r"\(lib\.ExprData\.Atom (\d+)\)\) 0\)",
        r"(lib.ExprData.Atom \1)", goals, count=1)
    assert mut != goals, "deref_drop: no `FieldProj (Box (Atom N)) 0` found"
    return mut


def wrong_field(goals):
    """G3: emit a WRONG struct/tuple field accessor — bump the first non-deref
    (field id >= 1) `FieldProj` id to a sentinel that no real accessor interns.
    The reference reproduces production's real field id, so any divergence
    flips. (Deref, field 0, is left alone.)"""
    mut = re.sub(
        r"(\(lib\.ExprData\.FieldProj \(Tactus\.Box\.mk "
        r"\(lib\.ExprData\.Atom \d+\)\) )[1-9]\d*\)",
        r"\g<1>999999)", goals, count=1)
    assert mut != goals, "wrong_field: no non-deref `FieldProj (Box (Atom N)) F` found"
    return mut


def wrong_width(goals):
    """G6: wrong HasType overflow bound — the u64 upper bound 2^64 -> 2^32. The
    reference re-derives 2^64 from the carried `HasType(64)` width (its own
    pow2), so the bound diverges."""
    POW64 = "lib.ExprData.Lit 18446744073709551616"
    POW32 = "lib.ExprData.Lit 4294967296"
    assert POW64 in goals, f"wrong_width: no {POW64!r} (u64 overflow bound) found"
    return goals.replace(POW64, POW32, 1)


CLASSES = [
    ("sum_to",     "cast_drop",   "drop an Int.toNat nat-coercion (cast class)",      drop_first_cast),
    ("head_exec",  "deref_drop",  "drop the .deref auto-coercion (G2)",               drop_deref),
    ("mk_point",   "wrong_field", "emit a wrong struct field accessor (G3)",          wrong_field),
    ("add_capped", "wrong_width", "wrong HasType overflow bound width 2^64->2^32 (G6)", wrong_width),
]


def main():
    L = []
    L.append("import TactusDefs_lib_exec")
    L.append("set_option linter.unusedVariables false")
    L.append("set_option autoImplicit false")
    L.append("set_option maxRecDepth 8000")
    L.append("")
    L.append("-- W6e expression-level mutation-kill suite (bootstrap-24), GENERATED by")
    L.append("-- gen.py from the LIVE fixture certs. For each of the four coercion-drop")
    L.append("-- classes: the unperturbed deep bridge closes (=1); a single GOAL-side")
    L.append("-- coercion drop must FLIP the verdict to 0 (proved positively by decide),")
    L.append("-- because ref_wp INDEPENDENTLY re-derives the correct structure. If any")
    L.append("-- mutation still equalled 1, its `= 0` example would error.")
    L.append("")

    fired = 0
    for fn, cls, human, mut_fn in CLASSES:
        cert = CERTDIR / f"{fn}.cert.lean"
        if not cert.exists():
            sys.exit(f"missing cert: {cert} (re-emit the fixture; see board/bootstrap-15)")
        text = cert.read_text()
        ctx   = extract_def(text, f"cert_{fn}_ctx")
        sst   = extract_def(text, f"cert_{fn}_sst")
        goals = extract_def(text, f"cert_{fn}_goals")
        goals_mut = mut_fn(goals)

        L.append(f"-- ── {cls}: {fn} — {human} ──")
        L.append(f"@[reducible] def {fn}_ctx : lib.FnCtxData := {ctx}")
        L.append(f"@[reducible] def {fn}_sst : lib.StmData := {sst}")
        L.append(f"@[reducible] def {fn}_goals : lib.GoalList := {goals}")
        L.append(f"@[reducible] def {fn}_goals_mut : lib.GoalList := {goals_mut}")
        L.append(f"-- baseline: the unperturbed deep bridge closes.")
        L.append(f"example : lib.goals_eq (lib.ref_wp {fn}_ctx {fn}_sst) {fn}_goals = 1 := by decide")
        L.append(f"-- kill: the coercion drop FLIPS the bridge (Friction-2 caught).")
        L.append(f"example : lib.goals_eq (lib.ref_wp {fn}_ctx {fn}_sst) {fn}_goals_mut = 0 := by decide")
        L.append("")
        fired += 1

    out = pathlib.Path(__file__).with_name("ExprMutations.lean")
    out.write_text("\n".join(L))
    print(f"wrote {out}  ({fired} classes: baseline + coercion-drop kill each)")


if __name__ == "__main__":
    main()
