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

This harness proves it, positively and by `decide`, for four coercion-drop
classes plus the P1 poison-channel class, each on its own live cert:

  * cast_drop    (sum_to,     nat-coercion / cast class): drop an `Int.toNat`
  * deref_drop   (head_exec,  G2 auto-deref):             drop the `.deref` FieldProj
  * wrong_field  (mk_point,   G3 struct field):           emit a WRONG field accessor
  * wrong_width  (add_capped, G6 HasType overflow):       2^64 bound -> 2^32
  * poison_flip  (add_capped, P1 trusted wrap-gate mark): poison bit 1 -> 0,
                 SST-side — pins that a serializer mismark flips the bridge
                 (DESIGN-bootstrap-endgame §1 P1)

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


def poison_drop(sst):
    """P1 poison-channel kill (endgame policy P1, DESIGN-bootstrap-endgame §1).

    The N1 wrap-gate poison mark is a SEMANTIC PREDICATE computed by the
    trusted serializer (`hyp_poison` — "does this hyp prop mention an
    in-scope residue name"), not a transcription — the model's gate only
    READS it. This mutation pins that the channel is live in the bridge:
    zero EVERY poison mark in the SST literal (the reference's INPUT) —
    exactly what a broken `hyp_poison` (spuriously returning 0) would
    emit — and ref_wp HOISTS goals production WRAPPED; the verdict must
    flip. All marks, not one: production pushes a duplicated hyp pair
    per assert (FINDINGS-b74-slice2 §3, the Assert forward hyp + the
    following Assume carry the SAME poisoned prop), so a single-bit flip
    is masked by the twin — discovered live by this harness's first run.
    Note this is an SST-side mutation, unlike the four goal-side
    coercion classes: the mark's consumer is ref_wp itself."""
    n = 0

    def flip_after(key, tail_re, sst):
        nonlocal n
        out, i = [], 0
        while True:
            j = sst.find(key, i)
            if j == -1:
                out.append(sst[i:])
                return "".join(out)
            k = match_paren(sst, j + len(key))  # end of the leading tree arg
            m = re.match(tail_re, sst[k + 1:])
            if m and m.group(0).endswith(" 1)"):
                out.append(sst[i:k + 1] + m.group(0)[:-2] + "0)")
                n += 1
                i = k + 1 + m.end()
            else:
                out.append(sst[i:j + len(key)])
                i = j + len(key)

    # Assert (ob…) NAME HYP POISON) — the obligation is a paren tree.
    sst = flip_after("lib.StmData.Assert ", r" (\d+) (\d+) 1\)", sst)
    # Assume NAME HYP POISON) — all-numeric, plain regex.
    sst2 = re.sub(r"(lib\.StmData\.Assume \d+ \d+) 1\)", r"\g<1> 0)", sst)
    n += len(re.findall(r"lib\.StmData\.Assume \d+ \d+ 1\)", sst))
    assert n > 0, "poison_drop: no poison marks set — fixture lost its poisoned pair"
    return sst2


# (fn, class, human description, mutation, which def the mutation edits, expect)
#
# expect="close": baseline bridges (=1) and the mutation kills (=0).
# expect="divergent-parked": the fixture is a DOCUMENTED b74 honest-fail
#   (head_exec: N2 match-split unmodeled — endgame A5); its baseline
#   asserts =0 as a REGRESSION TRIPWIRE: the day the A5 arm lands and
#   head_exec closes, this example fails loud and the class must be
#   restored to expect="close" with its kill. Never a silent cap (P2).
CLASSES = [
    ("sum_to",     "cast_drop",   "drop an Int.toNat nat-coercion (cast class)",      drop_first_cast, "goals", "close"),
    ("head_exec",  "deref_drop",  "drop the .deref auto-coercion (G2)",               drop_deref,      "goals", "divergent-parked"),
    ("mk_point",   "wrong_field", "emit a wrong struct field accessor (G3)",          wrong_field,     "goals", "close"),
    ("add_capped", "wrong_width", "wrong HasType overflow bound width 2^64->2^32 (G6)", wrong_width,   "goals", "close"),
    ("add_capped", "poison_flip", "zero ALL wrap-gate poison marks (P1 trusted-predicate channel)", poison_drop, "sst", "close"),
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
    for fn, cls, human, mut_fn, side, expect in CLASSES:
        cert = CERTDIR / f"{fn}.cert.lean"
        if not cert.exists():
            sys.exit(f"missing cert: {cert} (re-emit the fixture; see board/bootstrap-15)")
        text = cert.read_text()
        ctx   = extract_def(text, f"cert_{fn}_ctx")
        sst   = extract_def(text, f"cert_{fn}_sst")
        goals = extract_def(text, f"cert_{fn}_goals")

        # Defs keyed by CLASS (a fixture fn may serve several classes).
        L.append(f"-- ── {cls}: {fn} — {human} ──")
        L.append(f"@[reducible] def {cls}_ctx : lib.FnCtxData := {ctx}")
        L.append(f"@[reducible] def {cls}_sst : lib.StmData := {sst}")
        L.append(f"@[reducible] def {cls}_goals : lib.GoalList := {goals}")
        if expect == "divergent-parked":
            L.append(f"-- PARKED (endgame A5): {fn} is a documented b74 honest-fail; this")
            L.append(f"-- =0 example is the tripwire — when the arm lands and {fn} closes,")
            L.append(f"-- it fails loud and the class must be restored to close+kill.")
            L.append(f"example : lib.goals_eq (lib.ref_wp {cls}_ctx {cls}_sst) {cls}_goals = 0 := by decide")
            L.append("")
            fired += 1
            continue
        if side == "goals":
            L.append(f"@[reducible] def {cls}_goals_mut : lib.GoalList := {mut_fn(goals)}")
            kill = f"lib.goals_eq (lib.ref_wp {cls}_ctx {cls}_sst) {cls}_goals_mut"
        else:  # sst-side mutation: the reference's own input is perturbed
            L.append(f"@[reducible] def {cls}_sst_mut : lib.StmData := {mut_fn(sst)}")
            kill = f"lib.goals_eq (lib.ref_wp {cls}_ctx {cls}_sst_mut) {cls}_goals"
        L.append(f"-- baseline: the unperturbed deep bridge closes.")
        L.append(f"example : lib.goals_eq (lib.ref_wp {cls}_ctx {cls}_sst) {cls}_goals = 1 := by decide")
        L.append(f"-- kill: the single-edit mutation FLIPS the bridge.")
        L.append(f"example : {kill} = 0 := by decide")
        L.append("")
        fired += 1

    out = pathlib.Path(__file__).with_name("ExprMutations.lean")
    out.write_text("\n".join(L))
    print(f"wrote {out}  ({fired} classes: baseline + coercion-drop kill each)")


if __name__ == "__main__":
    main()
