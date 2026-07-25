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
  * ifctor_eq_drop  (head_exec, b77/A5): degenerate the IfCtor ctor-equation
                 hyp leaf, SST-side — with ifctor_arm_swap, ALSO the interim
                 N2-detector cross-check pin (second trusted predicate,
                 sst_serialize.rs header): frame ASSEMBLY is pinned while
                 the peel decision stays shared until A7
  * ifctor_arm_swap (head_exec, b77/A5): swap the fork's thn/els bodies,
                 SST-side — per-arm goals under the wrong branch hyps
  * aqt_hyp_drop (assert_by_default, b77/A3): drop the AssertQueryTactus
                 AssertFact bare-P hyp leaf, SST-side

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


def take_sexpr(s, i):
    """Bracket-aware term splitter (b77 follow-up): scan from offset `i`,
    skip leading whitespace, and return the span `(start, end)` of the next
    term — a balanced `( … )` group or a bare atom (scalar / bare ctor).
    Makes a ctor's POSITIONAL args addressable without regex fragility:
    walk args by repeated `_, i = take_sexpr(s, i)`."""
    while i < len(s) and s[i].isspace():
        i += 1
    assert i < len(s) and s[i] != ')', f"take_sexpr: no term at {i}"
    if s[i] == '(':
        return i, match_paren(s, i) + 1
    j = i
    while j < len(s) and not s[j].isspace() and s[j] not in '()':
        j += 1
    return i, j


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


def _ifctor_args(sst):
    """Locate the (single) `lib.StmData.IfCtor` node and return the spans of
    its positional args: (pos_binders, [6 scalar spans], thn, els). Layout
    per tactus-core: pos_binders, eq_name, eq_prop, eq_poison, neg_name,
    neg_prop, neg_poison, thn, els."""
    key = "lib.StmData.IfCtor "
    j = sst.find(key)
    assert j != -1, "ifctor: no `lib.StmData.IfCtor` node — fixture lost its A5 fork"
    assert sst.find(key, j + 1) == -1, "ifctor: multiple IfCtor nodes; splitter assumes one"
    i = j + len(key)
    binders = take_sexpr(sst, i)
    scalars, i = [], binders[1]
    for _ in range(6):
        sp = take_sexpr(sst, i)
        assert sst[sp[0]:sp[1]].isdigit(), f"ifctor: expected scalar, got {sst[sp[0]:sp[1]]!r}"
        scalars.append(sp)
        i = sp[1]
    thn = take_sexpr(sst, i)
    els = take_sexpr(sst, thn[1])
    assert sst[thn[0]] == '(' and sst[els[0]] == '(', "ifctor: thn/els not paren groups"
    return binders, scalars, thn, els


def ifctor_eq_drop(sst):
    """A5/N2 kill (SST-side): degenerate the IfCtor ctor-equation hyp —
    rewrite the `eq_prop` leaf scalar (the annotated `scrut = Dt.Variant fs`
    prop the shared N2 detector's frame assembly produced) to the 999999
    sentinel no real leaf interns (wrong_field precedent; the card's
    "interned True leaf" does not exist in this cert — head_exec interns no
    True, and `goals_eq` kills on id-divergence either way). Models a broken
    frame assembly emitting a wrong/degenerate equation hyp: refWp emits
    `All eq_name 999999` where production goals carry the real eq_prop."""
    _, scalars, _, _ = _ifctor_args(sst)
    s, e = scalars[1]  # eq_prop
    assert sst[s:e] != "999999", "ifctor_eq_drop: eq_prop already sentinel?"
    return sst[:s] + "999999" + sst[e:]


def ifctor_arm_swap(sst):
    """A5 kill (SST-side): swap the IfCtor `thn`/`els` boxed bodies — the
    per-arm continuation goals emit under the WRONG branch hypotheses
    (then-goals under ¬cond, else-goals under the ctor equation + field
    binders), so refWp's goal list diverges from production's."""
    _, _, (t0, t1), (e0, e1) = _ifctor_args(sst)
    thn, els = sst[t0:t1], sst[e0:e1]
    assert thn != els, "ifctor_arm_swap: thn == els — swap would be a no-op"
    return sst[:t0] + els + sst[t1:e0] + thn + sst[e1:]


def aqt_hyp_drop(sst):
    """A3 kill (SST-side): drop the AssertQueryTactus AssertFact hyp —
    rewrite the bare-P leaf scalar (2nd-from-last arg: obligation, hyp_name,
    bare_P, poison) to 0. The continuation goals lose the proven-inline
    fact: refWp emits `All hyp_name 0` where production goals carry the
    real bare-P leaf. (The following Assume still carries the real leaf, so
    the kill isolates the AQT arm's own hyp push.)"""
    key = "lib.StmData.AssertQueryTactus "
    j = sst.find(key)
    assert j != -1, "aqt: no `lib.StmData.AssertQueryTactus` node — fixture lost its A3 assert-by"
    i = j + len(key)
    oblig = take_sexpr(sst, i)
    assert sst[oblig[0]] == '(', "aqt: obligation not a paren group"
    name = take_sexpr(sst, oblig[1])
    bare = take_sexpr(sst, name[1])
    s, e = bare
    assert sst[s:e].isdigit() and sst[s:e] != "0", f"aqt_hyp_drop: bare-P scalar {sst[s:e]!r} unusable"
    return sst[:s] + "0" + sst[e:]


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
    # RESTORED (bootstrap-77): the A5 IfCtor fork landed and head_exec
    # CLOSES — the parked tripwire fired as designed; the class is back
    # to close+kill (the .deref drop now exercises the fork's per-arm
    # goal leaves).
    ("head_exec",  "deref_drop",  "drop the .deref auto-coercion (G2)",               drop_deref,      "goals", "close"),
    ("mk_point",   "wrong_field", "emit a wrong struct field accessor (G3)",          wrong_field,     "goals", "close"),
    ("add_capped", "wrong_width", "wrong HasType overflow bound width 2^64->2^32 (G6)", wrong_width,   "goals", "close"),
    ("add_capped", "poison_flip", "zero ALL wrap-gate poison marks (P1 trusted-predicate channel)", poison_drop, "sst", "close"),
    # b77 arm-structure kills (card §Follow-ups): pin the NEW IfCtor /
    # AssertQueryTactus arms. The two IfCtor kills are ALSO the interim
    # N2-detector cross-check pin (serializer header contract, second
    # trusted predicate): the peel-to-IsVariant DECISION is shared
    # common-mode, but the FRAME ASSEMBLY is recomputed independently —
    # these kills prove the assembled frames (ctor-equation hyp, per-arm
    # goal structure) are load-bearing in the bridge until A7 derives the
    # detector reference-side.
    ("head_exec",  "ifctor_eq_drop",  "IfCtor: degenerate the ctor-equation hyp leaf (A5/N2 frame assembly)", ifctor_eq_drop,  "sst", "close"),
    ("head_exec",  "ifctor_arm_swap", "IfCtor: swap thn/els arm bodies (A5 fork structure)",                   ifctor_arm_swap, "sst", "close"),
    ("assert_by_default", "aqt_hyp_drop", "AssertQueryTactus: drop the AssertFact bare-P hyp (A3)",            aqt_hyp_drop,    "sst", "close"),
]


def main():
    L = []
    L.append("import TactusDefs_lib_exec")
    L.append("set_option linter.unusedVariables false")
    L.append("set_option autoImplicit false")
    L.append("set_option maxRecDepth 8000")
    L.append("")
    L.append("-- W6e expression-level mutation-kill suite (bootstrap-24; b77 arm kills")
    L.append("-- added), GENERATED by gen.py from the LIVE fixture certs. For each class:")
    L.append("-- the unperturbed deep bridge closes (=1); a single structural mutation")
    L.append("-- (GOAL-side coercion drop, or SST-side mark/arm perturbation) must FLIP")
    L.append("-- the verdict to 0 (proved positively by decide), because ref_wp")
    L.append("-- INDEPENDENTLY re-derives the correct structure. If any mutation still")
    L.append("-- equalled 1, its `= 0` example would error.")
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
