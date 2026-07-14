#!/usr/bin/env python3
"""W2b mutation-kill generator (bootstrap-07).

Reads the LIVE add_capped cert (bootstrap-fixture/out/lib/cert/add_capped.cert.lean),
copies its three defs (ctx / sst / goals) VERBATIM, and emits Mutations.lean:

  * baseline bridge:  goals_eq (ref_wp ctx sst) goals = 1 := by decide   (must close)
  * one perturbed goals/sst term per mutation, each asserting
        goals_eq (ref_wp ctx sst) <perturbed> = 0 := by decide
    i.e. a POSITIVE, kernel-checked proof that the single perturbation FLIPPED
    the verdict 1 -> 0. If a mutation fails to flip, its `= 0` example errors.

The perturbations are STRUCTURAL text transforms (balanced-paren surgery /
pattern swaps), NOT hard-coded leaf-id values, so the suite survives a fixture
regen that renumbers leaves. The whole point (task + DESIGN 2.4.2): a green
bridge proves nothing unless a mismatch is provably rejected.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
CERT = ROOT / "bootstrap-fixture/out/lib/cert/add_capped.cert.lean"

def match_paren(s, i):
    """Given s[i] == '(', return index j with s[j] == ')' matching it."""
    assert s[i] == '(', f"expected '(' at {i}, got {s[i]!r}"
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '(': depth += 1
        elif s[j] == ')':
            depth -= 1
            if depth == 0: return j
    raise ValueError("unbalanced")

def extract_def(text, name):
    """Return the RHS term of `@[reducible] def <name> ... := <RHS>`. These
    certs emit each def's RHS as one physical line (the line AFTER `:=`), which
    may be paren-wrapped (ctx/sst) or bare (goals)."""
    m = re.search(rf"def {re.escape(name)}\b.*?:=", text)
    if not m: sys.exit(f"def {name} not found")
    for ln in text[m.end():].split('\n'):
        if ln.strip():
            return ln.strip()
    sys.exit(f"def {name}: no RHS line")

def goal_spine(goals):
    """Split a `(lib.GoalList.Cons (Box G0) (Box (Cons (Box G1) ...)))` into
    the list of goal-term strings [G0, G1, ...] plus a rebuild() closure."""
    # strip one outer paren layer
    inner = goals
    goals_list = []
    # walk the Cons spine
    cur = goals
    def strip(s):
        s = s.strip()
        if s.startswith('(') and match_paren(s,0) == len(s)-1: return s[1:-1].strip()
        return s
    parts = []
    cur = strip(goals)
    while True:
        cur = cur.strip()
        if cur.startswith("lib.GoalList.Nil"): break
        assert cur.startswith("lib.GoalList.Cons"), cur[:40]
        # Cons (Box.mk <G>) (Box.mk <REST>)
        b1 = cur.index("(Tactus.Box.mk")
        b1e = match_paren(cur, b1)
        head_box = cur[b1:b1e+1]
        rest = cur[b1e+1:]
        b2 = rest.index("(Tactus.Box.mk")
        b2e = match_paren(rest, b2)
        tail_box = rest[b2:b2e+1]
        # G = inside head_box after 'Tactus.Box.mk '
        g_inner = strip(head_box[len("(Tactus.Box.mk"):-1])
        parts.append(g_inner)
        cur = strip(tail_box[len("(Tactus.Box.mk"):-1])
    return parts

def build_goals(parts):
    """Rebuild a GoalList term from goal-term strings."""
    out = "lib.GoalList.Nil"
    for g in reversed(parts):
        out = f"lib.GoalList.Cons (Tactus.Box.mk ({g})) (Tactus.Box.mk ({out}))"
    return f"({out})"

def main():
    text = CERT.read_text()
    ctx  = extract_def(text, "cert_add_capped_ctx")
    sst  = extract_def(text, "cert_add_capped_sst")
    goals = extract_def(text, "cert_add_capped_goals")
    parts = goal_spine(goals)
    assert len(parts) == 4, f"expected 4 goals, got {len(parts)}"

    muts = []  # (name, human, kind, term)  kind in {goals, sst}

    # M1 change-leaf-id: goal0's first `Leaf N` -> `Leaf 999999`
    p = parts[:]
    p[0] = re.sub(r"lib\.GoalData\.Leaf \d+", "lib.GoalData.Leaf 999999", p[0], count=1)
    muts.append(("mut1_change_leaf_id",
        "change one obligation leaf id (goal0 Leaf N -> 999999)", "goals", build_goals(p)))

    # M2 reorder-goals: swap goal0 and goal1
    p = parts[:]; p[0], p[1] = p[1], p[0]
    muts.append(("mut2_reorder_goals",
        "reorder two goals (swap goal0 <-> goal1)", "goals", build_goals(p)))

    # M3 drop-binder: remove goal0's OUTERMOST `All a b (Box CHILD)` wrapper
    g0 = parts[0].strip()
    m = re.match(r"lib\.GoalData\.All \d+ \d+ ", g0)
    assert m, g0[:40]
    boxpos = g0.index("(Tactus.Box.mk", m.end())
    boxend = match_paren(g0, boxpos)
    child = g0[boxpos+len("(Tactus.Box.mk"):boxend].strip()
    if child.startswith('(') and match_paren(child,0)==len(child)-1: child = child[1:-1].strip()
    p = parts[:]; p[0] = child
    muts.append(("mut3_drop_binder",
        "drop a binder (goal0 loses its outermost forall)", "goals", build_goals(p)))

    # M4 swap-hyps: swap goal0's two outermost binders (All a b) <-> (All c d)
    #   All a b (Box (All c d (Box GRAND)))  ->  All c d (Box (All a b (Box GRAND)))
    swapped = re.sub(
        r"lib\.GoalData\.All (\d+) (\d+) \(Tactus\.Box\.mk \(lib\.GoalData\.All (\d+) (\d+) ",
        r"lib.GoalData.All \3 \4 (Tactus.Box.mk (lib.GoalData.All \1 \2 ",
        parts[0], count=1)
    assert swapped != parts[0], "swap-hyps did not match"
    p = parts[:]; p[0] = swapped
    muts.append(("mut4_swap_hyps",
        "swap two hypotheses (goal0 outer two binders swapped)", "goals", build_goals(p)))

    # M5 sst-input: perturb the RetBind value (LHS ref_wp input is load-bearing)
    sst_mut = re.sub(r"lib\.RetBind\.RetLet (\d+) \d+", r"lib.RetBind.RetLet \1 999999", sst, count=1)
    assert sst_mut != sst, "RetBind perturb did not match"
    muts.append(("mut5_sst_retbind",
        "perturb SST RetBind value (ref_wp input; goal3 return-let flips)", "sst", sst_mut))

    L = []
    L.append("import TactusDefs_lib_exec")
    L.append("set_option linter.unusedVariables false")
    L.append("set_option autoImplicit false")
    L.append("set_option maxRecDepth 8000")
    L.append("")
    L.append("-- W2b mutation-kill suite (bootstrap-07), GENERATED by gen.py from the")
    L.append("-- live add_capped cert. Baseline closes (=1); every single-edit mutation")
    L.append("-- must FLIP the verdict to 0 (proved positively by `decide`). If any")
    L.append("-- mutation still equalled 1, its `= 0` example would error.")
    L.append("")
    L.append(f"@[reducible] def ctx : lib.FnCtxData := {ctx}")
    L.append(f"@[reducible] def sst : lib.StmData := {sst}")
    L.append(f"@[reducible] def goals : lib.GoalList := {goals}")
    L.append("")
    L.append("-- baseline: the unperturbed bridge closes.")
    L.append("example : lib.goals_eq (lib.ref_wp ctx sst) goals = 1 := by decide")
    L.append("")
    for name, human, kind, term in muts:
        L.append(f"-- {name}: {human}")
        if kind == "goals":
            L.append(f"@[reducible] def {name}_goals : lib.GoalList := {term}")
            L.append(f"example : lib.goals_eq (lib.ref_wp ctx sst) {name}_goals = 0 := by decide")
        else:  # sst
            L.append(f"@[reducible] def {name}_sst : lib.StmData := {term}")
            L.append(f"example : lib.goals_eq (lib.ref_wp ctx {name}_sst) goals = 0 := by decide")
        L.append("")
    out = pathlib.Path(__file__).with_name("Mutations.lean")
    out.write_text("\n".join(L))
    print(f"wrote {out}  ({len(muts)} mutations + baseline)")

if __name__ == "__main__":
    main()
