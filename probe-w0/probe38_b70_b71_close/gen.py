#!/usr/bin/env python3
"""b70/b71 close-out probe (endgame A1, DESIGN-bootstrap-endgame §3 A1).

The two serializer-arm cards landed pre-b74 and were validated only to
the pre-reconciliation limit. This probe is their post-b74 closing
evidence, from the LIVE certs:

b71 (∀-path Call assembly, use_clamped / fixture F21):
  * baseline      full-goals bridge closes (=1) — the N1-hoist mirror
                  reproduces the ∀-path post frame byte-for-byte.
  * kill A        drop the ret-bound FHyp from the Call post frame
                  (SST side) — refWp loses a named binder -> flip (=0).
  * kill B        swap the two post-frame FHyps (ret-bound <-> ens) —
                  binder order diverges -> flip (=0).

b70 (call-generic, vec_read):
  * goal census   goal 0 (the Call PRECONDITION goal) decide-closes
                  per-goal (=1): the generic instantiation + the b74
                  telescope are faithful.
  * kill          perturb the transcribed req atom (SST side) -> goal 0
                  flips (=0).
  * A7 tripwire   goal 1 (the Ret goal) is the DOCUMENTED stage-B
                  honest-fail (view-call deref + Int.ofNat CallN
                  coercion — endgame A7): asserted =0. The day the A7
                  vocabulary lands and it closes, this example fails
                  loud and the tripwire must be replaced by a
                  close+kill pair. Never a silent cap (P2).

Per-goal comparison uses a probe-local `gl_nth` over the emitted
mirror vocabulary (Nat-structural recursion; Box fields via .deref).
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
    m = re.search(rf"def {re.escape(name)}\b.*?:=", text)
    if not m:
        sys.exit(f"def {name} not found")
    for ln in text[m.end():].split('\n'):
        if ln.strip():
            return ln.strip()
    sys.exit(f"def {name}: no RHS line")


# ── b71 mutations (use_clamped SST, the Call post frame) ────────────

def drop_ret_bound_fhyp(sst):
    """Remove the FIRST FHyp of the Call post frame — the ret-bound
    hypothesis — splicing its tail up. `FBind b t (Box (FHyp n p 0
    (Box tail)))` -> `FBind b t (Box tail)`."""
    i = sst.find("lib.StmData.Call")
    assert i != -1, "no Call node in use_clamped SST"
    j = sst.find("(lib.FrameList.FHyp ", i)
    assert j != -1, "no FHyp in Call post frame"
    node_end = match_paren(sst, j)
    node = sst[j:node_end + 1]
    k = node.find("(Tactus.Box.mk ")
    assert k != -1
    inner_start = k + len("(Tactus.Box.mk ")
    assert node[inner_start] == '('
    inner_end = match_paren(node, inner_start)
    tail = node[inner_start:inner_end + 1]
    mut = sst[:j] + tail + sst[node_end + 1:]
    assert mut != sst
    return mut


def swap_post_fhyps(sst):
    """Swap the (name, prop) pairs of the two adjacent post-frame FHyps
    (ret-bound <-> ens)."""
    mut = re.sub(
        r"lib\.FrameList\.FHyp (\d+) (\d+) 0 \(Tactus\.Box\.mk "
        r"\(lib\.FrameList\.FHyp (\d+) (\d+) 0 ",
        r"lib.FrameList.FHyp \3 \4 0 (Tactus.Box.mk (lib.FrameList.FHyp \1 \2 0 ",
        sst, count=1)
    assert mut != sst, "no adjacent FHyp pair (∀-path post frame) found"
    return mut


# ── b70 mutation (vec_read SST, the Call reqs list) ─────────────────

def perturb_req_atom(sst):
    """Re-point the transcribed Call req atom at an uninterned leaf id
    (the b70 card's original kill, re-run post-b74)."""
    i = sst.find("lib.StmData.Call")
    assert i != -1, "no Call node in vec_read SST"
    m = re.compile(r"lib\.RawExp\.Var (\d+) ").search(sst, i)
    assert m, "no req Var atom after Call"
    mut = sst[:m.start()] + f"lib.RawExp.Var 9999 " + sst[m.end():]
    assert mut != sst
    return mut


def drop_index_expected(sst):
    """A7 kill: drop the Seq.index 2nd arg's EXPECTED param typ
    (TyInt → TyNat) in the Ret's CallN. reconcile_arg then derives NO
    `Int.ofNat` where production inserts one — pins that the
    expected-typ channel is live (the vec_read goal-1 close depends
    on it)."""
    pat = "lib.RawExp.Var 2 lib.TypData.TyNat)) lib.TypData.TyInt"
    i = sst.find(pat)
    assert i != -1, "no (Var 2 TyNat, expected TyInt) pair in vec_read SST"
    mut = sst[:i] + "lib.RawExp.Var 2 lib.TypData.TyNat)) lib.TypData.TyNat" + sst[i + len(pat):]
    assert mut != sst
    return mut


def main():
    L = []
    L.append("import TactusDefs_lib_exec")
    L.append("set_option linter.unusedVariables false")
    L.append("set_option autoImplicit false")
    L.append("set_option maxRecDepth 8000")
    L.append("")
    L.append("-- b70/b71 close-out suite (endgame A1), GENERATED by gen.py from the")
    L.append("-- LIVE fixture certs. See gen.py docstring for the claim table.")
    L.append("")
    L.append("-- Probe-local per-goal accessor (Nat-structural; Box via .deref).")
    L.append("@[reducible] noncomputable def gl_nth (l : lib.GoalList) : Nat → Option lib.GoalData :=")
    L.append("  fun n => match n, l with")
    L.append("  | 0, lib.GoalList.Cons g _ => some g.deref")
    L.append("  | Nat.succ m, lib.GoalList.Cons _ t => gl_nth t.deref m")
    L.append("  | _, lib.GoalList.Nil => none")
    L.append("")
    L.append("@[reducible] noncomputable def gl_nth_eq (a b : lib.GoalList) (n : Nat) : Nat :=")
    L.append("  match gl_nth a n, gl_nth b n with")
    L.append("  | some x, some y => lib.goal_eq x y")
    L.append("  | _, _ => 2")
    L.append("")

    # b71: use_clamped
    t = (CERTDIR / "use_clamped.cert.lean").read_text()
    ctx = extract_def(t, "cert_use_clamped_ctx")
    sst = extract_def(t, "cert_use_clamped_sst")
    goals = extract_def(t, "cert_use_clamped_goals")
    L.append("-- ── b71: use_clamped — ∀-path Call post frame ──")
    L.append(f"@[reducible] def uc_ctx : lib.FnCtxData := {ctx}")
    L.append(f"@[reducible] def uc_sst : lib.StmData := {sst}")
    L.append(f"@[reducible] def uc_goals : lib.GoalList := {goals}")
    L.append(f"@[reducible] def uc_sst_dropbound : lib.StmData := {drop_ret_bound_fhyp(sst)}")
    L.append(f"@[reducible] def uc_sst_swapped : lib.StmData := {swap_post_fhyps(sst)}")
    L.append("-- baseline: the ∀-path caller bridge-closes post-b74.")
    L.append("example : lib.goals_eq (lib.ref_wp uc_ctx uc_sst) uc_goals = 1 := by decide")
    L.append("-- kill A: dropping the ret-bound FHyp flips.")
    L.append("example : lib.goals_eq (lib.ref_wp uc_ctx uc_sst_dropbound) uc_goals = 0 := by decide")
    L.append("-- kill B: swapping ret-bound <-> ens FHyps flips.")
    L.append("example : lib.goals_eq (lib.ref_wp uc_ctx uc_sst_swapped) uc_goals = 0 := by decide")
    L.append("")

    # b70: vec_read
    t = (CERTDIR / "vec_read.cert.lean").read_text()
    ctx = extract_def(t, "cert_vec_read_ctx")
    sst = extract_def(t, "cert_vec_read_sst")
    goals = extract_def(t, "cert_vec_read_goals")
    L.append("-- ── b70: vec_read — generic Call, per-goal ──")
    L.append(f"@[reducible] def vr_ctx : lib.FnCtxData := {ctx}")
    L.append(f"@[reducible] def vr_sst : lib.StmData := {sst}")
    L.append(f"@[reducible] def vr_goals : lib.GoalList := {goals}")
    L.append(f"@[reducible] def vr_sst_reqmut : lib.StmData := {perturb_req_atom(sst)}")
    L.append(f"@[reducible] def vr_sst_expdrop : lib.StmData := {drop_index_expected(sst)}")
    L.append("-- baseline: goal 0 (Call PRECONDITION, generic instantiation) closes.")
    L.append("example : gl_nth_eq (lib.ref_wp vr_ctx vr_sst) vr_goals 0 = 1 := by decide")
    L.append("-- kill: perturbing the transcribed req atom flips goal 0.")
    L.append("example : gl_nth_eq (lib.ref_wp vr_ctx vr_sst_reqmut) vr_goals 0 = 0 := by decide")
    L.append("-- A7 LANDED (bootstrap-80, 2026-07-31): goal 1 (Ret) now CLOSES —")
    L.append("-- the tripwire fired as designed and is replaced by this close+kill")
    L.append("-- pair (P2). The kill drops the Seq.index 2nd arg's EXPECTED typ")
    L.append("-- (TyInt → TyNat): reconcile_arg then derives NO `Int.ofNat` where")
    L.append("-- production inserts one — the expected-typ channel is live.")
    L.append("example : gl_nth_eq (lib.ref_wp vr_ctx vr_sst) vr_goals 1 = 1 := by decide")
    L.append("example : gl_nth_eq (lib.ref_wp vr_ctx vr_sst_expdrop) vr_goals 1 = 0 := by decide")
    L.append("")

    out = pathlib.Path(__file__).with_name("B70B71Close.lean")
    out.write_text("\n".join(L))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
