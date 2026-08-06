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
  * poison_*     (add_capped, F4 derived-poison channel, bootstrap-80 stage 2):
                  residue_names zeroed (miss direction) / residue-mentioning
                  prop_deeps dropped (missing-entry kill),
                 SST-side — pins that a serializer mismark flips the bridge
                 (DESIGN-bootstrap-endgame §1 P1)
  * ifctor_eq_drop / ifctor_binder_drop / ifctor_neg_drop / ifctor_arm_swap
                 (head_exec, b77/A5, all SST-side): the four N2 frame-assembly
                 output channels — ctor-equation hyp, field-binder telescope,
                 else-branch hyp, arm attachment. Together the interim
                 N2-detector cross-check pin (second trusted predicate,
                 sst_serialize.rs header): the ASSEMBLY is pinned per-channel
                 while the peel-to-IsVariant DECISION stays shared until A7
  * aqt_hyp_drop (assert_by_default, b77/A3): drop the AssertQueryTactus
                 AssertFact bare-P hyp leaf, SST-side

For each: extract the live cert's ctx/sst/goals VERBATIM, apply a single
STRUCTURAL text mutation — GOAL-side for the coercion classes (`ref_wp`/ctx/sst
untouched, so the reference re-derivation stays correct: models a serializer
that emitted wrong goals), SST-side for the trusted-channel/arm classes (the
reference's own INPUT is perturbed: models a serializer that emitted a wrong
literal, so refWp derives goals production didn't emit) — and assert BOTH
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


def _split_mk_args(ctx):
    """Split `(lib.FnCtxData.mk a1 … a9)` into its 9 positional args."""
    s = ctx.strip()
    assert s.startswith("(lib.FnCtxData.mk "), f"unexpected ctx shape: {s[:60]!r}"
    inner = s[len("(lib.FnCtxData.mk "):-1]
    args, i, n = [], 0, len(inner)
    while i < n:
        while i < n and inner[i] == " ":
            i += 1
        if i >= n:
            break
        if inner[i] == "(":
            j = match_paren(inner, i)
            args.append(inner[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and inner[j] != " ":
                j += 1
            args.append(inner[i:j])
            i = j
    assert len(args) == 9, f"FnCtxData.mk arity {len(args)} != 9 (stale probe vs vocab?)"
    return args


def _join_mk(args):
    return "(lib.FnCtxData.mk " + " ".join(args) + ")"


def poison_residue_drop(ctx):
    """F4 derivation-input kill, MISS direction (bootstrap-80 stage 2 —
    the re-pointed P1 channel). The poison mark is now DERIVED
    reference-side (`poisoned_props` over the ctx's residue_names +
    prop_deeps); the era-1 StmData bits are unread, so the old
    zero-the-bits kill is dead by construction. Zeroing residue_names
    makes the derivation miss the REAL residue mention: refWp HOISTS
    goals production WRAPPED; the verdict must flip."""
    args = _split_mk_args(ctx)
    assert args[6] != "lib.LeafList.Nil", "poison_residue_drop: no residues in ctx"
    args[6] = "lib.LeafList.Nil"
    return _join_mk(args)


# NOTE (no spurious-direction kill class): a spurious-residue kill cannot
# bite on add_capped — the real poison wraps every post-residue goal, and
# pre-residue props are unregistered by design (no deep to poison). The
# spurious direction is covered CORPUS-WIDE by the baselines: any
# over-poisoning by the derivation would mismatch a hoisted production
# goal somewhere in the probe9/probe11 subject set.


def poison_deep_drop(ctx):
    """F4 missing-entry kill: drop the prop_deeps entries the derivation
    WOULD mark (their deep mentions a residue name) — the reference
    derives 0 for a genuinely-poisoned prop, refWp HOISTS goals
    production WRAPPED; the verdict must flip. Pins that the side table
    (not just the name list) is load-bearing, and that a missing entry
    cannot silent-pass. Entry targets are computed the same way the
    reference derives them (residue ids from the ctx's own
    residue_names), so a fixture regen re-aims automatically."""
    args = _split_mk_args(ctx)
    resids = re.findall(r"lib\.LeafList\.Cons (\d+)", args[6])
    assert resids, "poison_deep_drop: no residues in ctx"
    s = args[7]
    key = "(lib.PropDeepList.Cons "
    n_dropped = 0
    while True:
        # find the FIRST entry whose deep mentions a residue
        i = 0
        hit = None
        while True:
            j = s.find(key, i)
            if j == -1:
                break
            m = re.match(r"(\d+) ", s[j + len(key):])
            assert m, f"malformed prop_deeps entry at {j}"
            d0 = j + len(key) + m.end()
            assert s[d0] == "(", f"prop_deeps deep not a paren term at {d0}"
            d1 = match_paren(s, d0) + 1
            if any(re.search(rf"\(lib\.RawExp\.Var {r}\b", s[d0:d1]) for r in resids):
                hit = (j, d1)
                break
            i = match_paren(s, j) + 1
        if hit is None:
            break
        j, d1 = hit
        e1 = match_paren(s, j) + 1
        # splice the entry out: replace it with its own tail (the last
        # arg, a Tactus.Box.mk-wrapped PropDeepList), then RESCAN — the
        # tail may hold more matching entries (the Assert/Assume pair
        # registers the same prop twice).
        tail_open = s.index("(Tactus.Box.mk ", d1)
        tail = s[tail_open + len("(Tactus.Box.mk "):match_paren(s, tail_open)]
        s = s[:j] + tail + s[e1:]
        n_dropped += 1
    assert n_dropped > 0, "poison_deep_drop: no residue-mentioning deeps found"
    args[7] = s
    return _join_mk(args)


def expected_typ_drop(sst):
    """A7 (bootstrap-80 F3) expected-typ channel kill. The RawList pair
    slot carries the callee's EXPECTED param typ; reconcile_arg derives
    the per-arg coercion from the (actual, expected) pair. Flipping the
    Seq.index index-arg's expected typ TyInt → TyNat makes the reference
    derive NO `Int.ofNat` where production inserts one — pins that the
    per-arg signature channel is load-bearing in the bridge (an SST-side
    mutation: the reference's own input is perturbed)."""
    pat = "lib.RawExp.Var 2 lib.TypData.TyNat)) lib.TypData.TyInt"
    i = sst.find(pat)
    assert i != -1, "expected_typ_drop: no (Var 2 TyNat, expected TyInt) pair in vec_read SST"
    mut = sst[:i] + "lib.RawExp.Var 2 lib.TypData.TyNat)) lib.TypData.TyNat" + sst[i + len(pat):]
    assert mut != sst
    return mut


def _ifctor_args(sst):
    """Locate the (single) `lib.StmData.IfCtor` node and return the spans of
    its positional args: (pos_binders, [6 scalar spans], thn, els). Layout
    per tactus-core (F4 era 2): pos_binders, eq_name, eq_prop, neg_name,
    neg_prop, thn, els."""
    key = "lib.StmData.IfCtor "
    j = sst.find(key)
    assert j != -1, "ifctor: no `lib.StmData.IfCtor` node — fixture lost its A5 fork"
    assert sst.find(key, j + 1) == -1, "ifctor: multiple IfCtor nodes; splitter assumes one"
    i = j + len(key)
    binders = take_sexpr(sst, i)
    scalars, i = [], binders[1]
    for _ in range(4):
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


def ifctor_binder_drop(sst):
    """A5/N2 kill (SST-side): drop the IfCtor FIELD-BINDER telescope — the
    most N2-specific assembly output (`tmp___val0 : Int` etc., the binders
    the ctor upgrade introduces). Replace the pos_binders Cons-list with
    Nil: refWp's then-goal loses its `All field typ` frames while
    production goals still carry them."""
    (b0, b1), _, _, _ = _ifctor_args(sst)
    binders = sst[b0:b1]
    assert "lib.BinderList.Cons" in binders, "ifctor_binder_drop: pos_binders already empty"
    return sst[:b0] + "(Tactus.Box.mk lib.BinderList.Nil)" + sst[b1:]


def ifctor_neg_drop(sst):
    """A5/N2 kill (SST-side): degenerate the IfCtor ELSE-branch hyp —
    rewrite the `neg_prop` leaf scalar (the plain `¬cond` discriminator;
    negative tests never upgrade) to the 999999 sentinel. refWp's
    else-goal telescope diverges from production's `All neg_name ¬cond`."""
    _, scalars, _, _ = _ifctor_args(sst)
    s, e = scalars[2]  # neg_prop
    assert sst[s:e] != "999999", "ifctor_neg_drop: neg_prop already sentinel?"
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
    rewrite the bare-P leaf scalar (last arg: obligation, hyp_name,
    bare_P) to 0. The continuation goals lose the proven-inline
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


def _deadend_args(sst):
    """Locate the (single) `lib.StmData.DeadEnd` node and return the spans
    of its three args: (scope_binders, scope_bounds, body). Layout per
    tactus-core (b81): Box'd BinderList, Box'd ParamBoundList, Box'd body."""
    key = "lib.StmData.DeadEnd "
    j = sst.find(key)
    assert j != -1, "deadend: no `lib.StmData.DeadEnd` node — fixture lost its b81 assert-forall"
    assert sst.find(key, j + 1) == -1, "deadend: multiple DeadEnd nodes; splitter assumes one"
    i = j + len(key)
    binders = take_sexpr(sst, i)
    bounds = take_sexpr(sst, binders[1])
    body = take_sexpr(sst, bounds[1])
    for name, sp in (("binders", binders), ("bounds", bounds), ("body", body)):
        assert sst[sp[0]] == '(', f"deadend: {name} not a paren group"
    return binders, bounds, body


def scope_binder_drop(sst):
    """b81 kill (SST-side): drop the assert-forall SCOPE BINDER — replace
    the DeadEnd's Box'd BinderList with Nil. refWp's in-scope goals lose
    their `All k Int` frames (the `Wp::Scope` ∀-telescope) while
    production goals still carry them — pins that the scope_binders slot
    is load-bearing in the bridge."""
    (b0, b1), _, _ = _deadend_args(sst)
    binders = sst[b0:b1]
    assert "lib.BinderList.Cons" in binders, "scope_binder_drop: scope_binders already empty"
    return sst[:b0] + "(Tactus.Box.mk lib.BinderList.Nil)" + sst[b1:]


def scope_bound_drop(sst):
    """b81 kill (SST-side): drop the skolem's TYPE-BOUND hyp — replace the
    DeadEnd's `ParamBoundList.Bound name prop` with `NoBound`
    (forall_u64_skolem, the u64-skolem subject: production's
    push_mod_var_frames re-asserts `0 ≤ k < 2^64` right after the
    ∀-binder). refWp loses the bound FHyp in the leading telescope while
    production goals carry it."""
    _, (b0, b1), _ = _deadend_args(sst)
    bounds = sst[b0:b1]
    assert "lib.ParamBoundList.Bound" in bounds, "scope_bound_drop: no Bound entry — wrong subject?"
    return sst[:b0] + "(Tactus.Box.mk (lib.ParamBoundList.NoBound (Tactus.Box.mk lib.ParamBoundList.Nil)))" + sst[b1:]


def scope_binder_typ_flip(sst):
    """b81 kill (SST-side): flip the skolem binder's TYP LEAF — rewrite the
    BinderList.Cons typ scalar Int(leaf 16) → Nat(leaf 1, the param n's
    typ leaf, already interned in this cert). refWp emits `All k Nat`
    where production goals carry `All k Int` — the binder typ is
    load-bearing, not just the binder's presence."""
    (b0, b1), _, _ = _deadend_args(sst)
    binders = sst[b0:b1]
    pat = "lib.BinderList.Cons 15 16"
    i = binders.find(pat)
    assert i != -1, f"scope_binder_typ_flip: no `Cons 15 16` in {binders!r} (leaf ids renumbered?)"
    mut = binders[:i] + "lib.BinderList.Cons 15 1" + binders[i + len(pat):]
    assert mut != binders
    return sst[:b0] + mut + sst[b1:]


def scope_exit_name_drift(sst):
    """b81 review R1 kill (SST-side): drift the POST-SCOPE hyp's name —
    the trailing ∀-fact Assume carries `_h_hoist_1` (leaf 10): the
    scope's discarded hyps do NOT count on post-scope goal paths
    (production's per-goal-path numbering; the serializer restores
    hyp_ordinal at DeadEnd exit). Rewriting it to `_h_hoist_2` (leaf
    12) reproduces the pre-restore bug: refWp's leading prefix names
    the hyp `_h_hoist_2` where production has `_h_hoist_1`."""
    pat = "lib.StmData.Assume 10 23"
    i = sst.find(pat)
    assert i != -1, "scope_exit_name_drift: trailing ∀-fact Assume (10, 23) not found — renumbered?"
    assert sst.find(pat, i + 1) == -1, "scope_exit_name_drift: pattern not unique"
    return sst[:i] + "lib.StmData.Assume 12 23" + sst[i + len(pat):]


def _deadend_args_nth(sst, n):
    """Like `_deadend_args` but for the n-th (0-based) `lib.StmData.DeadEnd`
    node — the nested assert-forall subject (F31) has two."""
    key = "lib.StmData.DeadEnd "
    j = -1
    for _ in range(n + 1):
        j = sst.find(key, j + 1)
        assert j != -1, f"deadend: fewer than {n + 1} DeadEnd nodes"
    i = j + len(key)
    binders = take_sexpr(sst, i)
    bounds = take_sexpr(sst, binders[1])
    body = take_sexpr(sst, bounds[1])
    for name, sp in (("binders", binders), ("bounds", bounds), ("body", body)):
        assert sst[sp[0]] == '(', f"deadend[{n}]: {name} not a paren group"
    return binders, bounds, body


def scope_dedup_rebind(sst):
    """b81 review R2 kill (SST-side): REBIND the dedup'd skolem — the
    nested subject's inner DeadEnd carries Nil/Nil binders (j and k are
    already bound by the OUTER scope — production's `already_bound`
    filter). Re-inserting j makes refWp ∀-bind j a second time on the
    inner goals where production does not — pins that the dedup mirror
    is load-bearing (a serializer that naively rebound every
    assert-forall's skolems would diverge exactly here)."""
    (b0, b1), _, _ = _deadend_args_nth(sst, 1)
    binders = sst[b0:b1]
    assert binders == "(Tactus.Box.mk lib.BinderList.Nil)", \
        f"scope_dedup_rebind: inner binders not dedup'd to Nil: {binders!r}"
    outer, _, _ = _deadend_args_nth(sst, 0)
    assert "lib.BinderList.Cons 5 6" in sst[outer[0]:outer[1]], \
        "scope_dedup_rebind: outer j-binder (Cons 5 6) not found — leaf ids renumbered?"
    return sst[:b0] + "(Tactus.Box.mk (lib.BinderList.Cons 5 6 (Tactus.Box.mk lib.BinderList.Nil)))" + sst[b1:]


def _find_nth(s, key, n):
    """Offset of the n-th (1-based) occurrence of `key`."""
    i = -1
    for _ in range(n):
        i = s.find(key, i + 1)
        assert i != -1, f"occurrence {n} of {key!r} not found"
    return i


def _drop_frame_node(sst, ctor, nscalars, occ):
    """bootstrap-78 S4: drop the occ-th `(lib.FrameList.<ctor> s… (Box X))`
    node from a Call-post FrameList, splicing its tail X in place — the
    single-node structural drop the D5 kills specify. Bracket-aware via
    take_sexpr (b77 splitter); FrameList ctors only occur inside
    `StmData.Call` posts (loop binders are BinderList), so occurrence
    indexing is unambiguous."""
    key = f"(lib.FrameList.{ctor} "
    j = _find_nth(sst, key, occ)
    i = j + len(key)
    for _ in range(nscalars):
        sp = take_sexpr(sst, i)
        assert sst[sp[0]:sp[1]].isdigit(), \
            f"{ctor} scalar expected, got {sst[sp[0]:sp[1]]!r}"
        i = sp[1]
    box = take_sexpr(sst, i)  # (Tactus.Box.mk X)
    assert sst[box[0]:box[0] + 15] == "(Tactus.Box.mk ", f"{ctor}: tail not boxed"
    inner = take_sexpr(sst, box[0] + 14)
    end = match_paren(sst, j)
    assert end + 1 == box[1] + 1, f"{ctor}: trailing args after tail?"
    return sst[:j] + sst[inner[0]:inner[1]] + sst[end + 1:]


# ── bootstrap-78 S4: the mut-call frame kills (D5, subject call_inc —
# the CLOSING mut cert; vec_push7/fill_zeros are A7-class honest-fails).
# One kill per call_stm output channel. call_inc's first call's post is
# `FBind mut_post_1 · FHyp bound · FBind ret_2 · FHyp ens · FLet rebind`,
# so occurrence indexes are: FBind#1 = mut_post binder, FHyp#1 = bound,
# FHyp#2 = ens, FLet#1 = rebind. All SST-side (the frames live in the
# CERT's Call post — refWp's own input is perturbed).

def mut_post_binder_drop(sst):
    """Drop the Phase-1 `∀ mut_post` existential binder (FBind#1)."""
    return _drop_frame_node(sst, "FBind", 2, 1)


def mut_bound_hyp_drop(sst):
    """Drop the mut-post type-bound hyp (FHyp#1 — the
    `type_bound_predicate` mirror channel; u64 subject so it exists)."""
    return _drop_frame_node(sst, "FHyp", 2, 1)


def mut_ens_hyp_drop(sst):
    """Drop the instantiated-ensures hyp (FHyp#2) — distinct from b70's
    ∀-path frame kills (probe38): those covered a no-mut call's frames;
    this pins the hyp inside a MUT post assembly."""
    return _drop_frame_node(sst, "FHyp", 2, 2)


def mut_rebind_drop(sst):
    """Drop the Phase-4 rebind `FLet local := mut_post` (FLet#1) — the
    stale-local channel (continuation would read the PRE-call value)."""
    return _drop_frame_node(sst, "FLet", 2, 1)


def mut_gensym_rename(sst):
    """Single-site counter kill (D5): divert the mut_post BINDER's name
    leaf to the 999999 sentinel while the rebind FLet's value slot keeps
    the real id — models an emit-counter bug shifting a gensym name at
    one consumption site (the two sites disagree exactly as a mis-count
    makes serializer text diverge from production's goal names)."""
    key = "(lib.FrameList.FBind "
    j = _find_nth(sst, key, 1)
    sp = take_sexpr(sst, j + len(key))
    assert sst[sp[0]:sp[1]].isdigit() and sst[sp[0]:sp[1]] != "999999"
    return sst[:sp[0]] + "999999" + sst[sp[1]:]


# ── bootstrap-79: the break-form Loop kills (subject count_to_len — the
# minimal call-in-cond while; ONE Loop node). One kill per new Loop-arm
# output channel: the transcribed setup, the exit-reclose obligations,
# and the three cond-flavored guard leaves. All SST-side.

def _loop_args(sst):
    """Locate the (single) `lib.StmData.Loop` node and return its positional
    arg spans: (6 boxed lists, 11 scalars, decrease_oblig, setup, body).
    Layout per tactus-core (b79; F4 era 2 dropped cond_poison): inv_hyps,
    inv_obligs, inv_obligs_exit, inv_obligs_break, binders, binder_bounds,
    then cond_name, cond_ann, neg_cond_ann, neg_neg_cond_ann,
    break_guard_ann, break_use_ann, d_old_name, d_old_ty, d_old_val,
    d_old_eq_name, d_old_eq_prop, then decrease_oblig (RawExp), setup,
    body."""
    key = "lib.StmData.Loop "
    j = sst.find(key)
    assert j != -1, "loop: no `lib.StmData.Loop` node — subject lost its loop"
    assert sst.find(key, j + 1) == -1, "loop: multiple Loop nodes; splitter assumes one"
    i = j + len(key)
    lists = []
    for _ in range(6):
        sp = take_sexpr(sst, i)
        assert sst[sp[0]] == '(', f"loop: list arg not a paren group: {sst[sp[0]:sp[1]]!r}"
        lists.append(sp)
        i = sp[1]
    scalars = []
    for _ in range(11):
        sp = take_sexpr(sst, i)
        assert sst[sp[0]:sp[1]].isdigit(), f"loop: expected scalar, got {sst[sp[0]:sp[1]]!r}"
        scalars.append(sp)
        i = sp[1]
    decrease = take_sexpr(sst, i)
    setup = take_sexpr(sst, decrease[1])
    body = take_sexpr(sst, setup[1])
    assert sst[setup[0]] == '(' and sst[body[0]] == '(', "loop: setup/body not paren groups"
    return lists, scalars, setup, body


def loop_setup_drop(sst):
    """b79 kill (SST-side): drop the transcribed cond-setup (setup → Skip):
    refWp takes the CLASSICAL derivation — no exit-reclose family, the
    classical cond-hyp maintain telescope, no setup prefix on the
    post-loop continuation — so production's break-form goals diverge on
    EVERY family. Models the Loop arm silently dropping the setup slot
    (the byte-stability churn check in reverse)."""
    _, _, (s0, s1), _ = _loop_args(sst)
    assert "Skip" not in sst[s0:s1], "loop_setup_drop: setup already Skip (not a break-form subject)"
    return sst[:s0] + "(Tactus.Box.mk lib.StmData.Skip)" + sst[s1:]


def loop_break_oblig_drop(sst):
    """b79 kill (SST-side): drop the exit-reclose obligations
    (inv_obligs_break → Nil): the break-leaf goal family vanishes from
    refWp's output while production emits |invs| exit-reclose theorems
    (the normalized body's `if ¬exp { break }` break leaf)."""
    lists, _, _, _ = _loop_args(sst)
    s0, s1 = lists[3]
    assert "RawExpList.Cons" in sst[s0:s1], "loop_break_oblig_drop: inv_obligs_break already Nil"
    return sst[:s0] + "(Tactus.Box.mk lib.RawExpList.Nil)" + sst[s1:]


def loop_guard_leaf_drop(sst):
    """b79 kill (SST-side): degenerate the exit-guard leaf
    (break_guard_ann — the SPAN-MARK'd `¬exp`, walk_if's annotation of
    the synthesized guard) to the 999999 sentinel. The exit-reclose
    telescope's guard hyp diverges from production's `/- @rust…-/ ¬(…)`."""
    _, scalars, _, _ = _loop_args(sst)
    s, e = scalars[4]  # break_guard_ann
    assert sst[s:e] != "999999", "loop_guard_leaf_drop: break_guard_ann already sentinel?"
    return sst[:s] + "999999" + sst[e:]


def loop_negneg_leaf_drop(sst):
    """b79 kill (SST-side): degenerate the maintain else-guard leaf
    (neg_neg_cond_ann — the `¬(span_mark'd ¬exp)` double negation the
    normalized If's else branch carries) to the 999999 sentinel."""
    _, scalars, _, _ = _loop_args(sst)
    s, e = scalars[3]  # neg_neg_cond_ann
    assert sst[s:e] != "999999", "loop_negneg_leaf_drop: neg_neg_cond_ann already sentinel?"
    return sst[:s] + "999999" + sst[e:]


def loop_use_leaf_drop(sst):
    """b79 kill (SST-side): degenerate the post-loop exit-fact leaf
    (break_use_ann — the BARE `¬exp` production's exit_wrap pushes
    unmarked) to the 999999 sentinel. The post-loop continuation's
    ¬cond hyp diverges."""
    _, scalars, _, _ = _loop_args(sst)
    s, e = scalars[5]  # break_use_ann
    assert sst[s:e] != "999999", "loop_use_leaf_drop: break_use_ann already sentinel?"
    return sst[:s] + "999999" + sst[e:]


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
    # bootstrap-80 stage 2 (F4): the poison mark is DERIVED reference-side
    # now — the kills re-point at the derivation INPUTS (the ctx's
    # residue_names / prop_deeps), both directions + the missing-entry
    # case. The old zero-the-bits kill is retired: era-1 bits are unread.
    ("add_capped", "poison_residue_drop", "zero the residue_names table (F4 poison derivation, miss direction)", poison_residue_drop, "ctx", "close"),
    ("add_capped", "poison_deep_drop", "drop the residue-mentioning prop_deeps entries (F4 missing-entry kill)", poison_deep_drop, "ctx", "close"),
    # b77 arm-structure kills (card §Follow-ups): pin the NEW IfCtor /
    # AssertQueryTactus arms. The four IfCtor kills are ALSO the interim
    # N2-detector cross-check pin (serializer header contract, second
    # trusted predicate): the peel-to-IsVariant DECISION is shared
    # common-mode, but the FRAME ASSEMBLY is recomputed independently —
    # one kill per assembly output channel (ctor-equation hyp,
    # field-binder telescope, else-branch hyp, arm attachment) proves
    # each is load-bearing in the bridge until A7 derives the detector
    # reference-side.
    ("head_exec",  "ifctor_eq_drop",  "IfCtor: degenerate the ctor-equation hyp leaf (A5/N2 frame assembly)", ifctor_eq_drop,  "sst", "close"),
    ("head_exec",  "ifctor_binder_drop", "IfCtor: drop the field-binder telescope (A5/N2 frame assembly)",    ifctor_binder_drop, "sst", "close"),
    ("head_exec",  "ifctor_neg_drop", "IfCtor: degenerate the else-branch neg hyp leaf (A5/N2 frame assembly)", ifctor_neg_drop, "sst", "close"),
    ("head_exec",  "ifctor_arm_swap", "IfCtor: swap thn/els arm bodies (A5 fork structure)",                   ifctor_arm_swap, "sst", "close"),
    ("assert_by_default", "aqt_hyp_drop", "AssertQueryTactus: drop the AssertFact bare-P hyp (A3)",            aqt_hyp_drop,    "sst", "close"),
    # bootstrap-78 S4: the mut-call frame kills (D5) — one per call_stm
    # output channel, on the CLOSING mut subject call_inc.
    ("call_inc", "mut_post_binder_drop", "mut call: drop the ∀ mut_post existential binder (Phase 1)", mut_post_binder_drop, "sst", "close"),
    ("call_inc", "mut_bound_hyp_drop",   "mut call: drop the mut-post type-bound hyp (Phase 1)",       mut_bound_hyp_drop,   "sst", "close"),
    ("call_inc", "mut_ens_hyp_drop",     "mut call: drop the instantiated-ensures hyp (Phase 3)",      mut_ens_hyp_drop,     "sst", "close"),
    ("call_inc", "mut_rebind_drop",      "mut call: drop the rebind FLet (Phase 4, stale-local)",      mut_rebind_drop,      "sst", "close"),
    ("call_inc", "mut_gensym_rename",    "mut call: single-site gensym-name divergence (counter channel)", mut_gensym_rename, "sst", "close"),
    # bootstrap-79: the break-form Loop kills — one per new Loop-arm
    # output channel, on the minimal call-in-cond subject count_to_len.
    ("count_to_len", "loop_setup_drop",       "Loop break-form: drop the transcribed cond-setup (b79)",        loop_setup_drop,       "sst", "close"),
    ("count_to_len", "loop_break_oblig_drop", "Loop break-form: drop the exit-reclose obligations (b79)",      loop_break_oblig_drop, "sst", "close"),
    ("count_to_len", "loop_guard_leaf_drop",  "Loop break-form: degenerate the exit-guard span-mark'd ¬exp (b79)", loop_guard_leaf_drop, "sst", "close"),
    ("count_to_len", "loop_negneg_leaf_drop", "Loop break-form: degenerate the maintain ¬(¬cond) else-guard (b79)", loop_negneg_leaf_drop, "sst", "close"),
    ("count_to_len", "loop_use_leaf_drop",    "Loop break-form: degenerate the post-loop bare ¬cond (b79)",    loop_use_leaf_drop,    "sst", "close"),
    # bootstrap-80 A7: the expected-typ channel kill — the per-arg callee
    # param typs the RawList pairs carry are load-bearing (flipping one
    # flips the derived `Int.ofNat`, hence the bridge).
    ("vec_read", "expected_typ_drop", "drop the Seq.index arg's EXPECTED typ TyInt→TyNat (A7 reconcile channel)", expected_typ_drop, "sst", "close"),
    # bootstrap-81 (row 11b): the assert-forall scope-binder kills — one
    # per DeadEnd-arm output channel (binder presence, bound hyp, binder
    # typ), on the two new fixture subjects (Int NoBound / u64 Bound).
    ("forall_int_skolem", "scope_binder_drop", "DeadEnd: drop the assert-forall scope binder (b81 ∀-telescope arm)", scope_binder_drop, "sst", "close"),
    ("forall_u64_skolem", "scope_bound_drop", "DeadEnd: drop the skolem type-bound hyp (b81 Bound slot)", scope_bound_drop, "sst", "close"),
    ("forall_int_skolem", "scope_binder_typ_flip", "DeadEnd: flip the skolem binder typ leaf Int→Nat (b81)", scope_binder_typ_flip, "sst", "close"),
    # b81 review R2: the dedup mirror is load-bearing — rebinding the
    # dedup'd skolem on the inner scope flips the bridge.
    ("forall_nested_shadow", "scope_dedup_rebind", "DeadEnd: rebind the dedup'd skolem on the inner scope (b81 R2 dedup channel)", scope_dedup_rebind, "sst", "close"),
    # b81 review R1: the post-scope hyp-name channel — drifts to the
    # pre-restore value (the ordinal-restore fix's regression pin).
    ("forall_leading_prefix", "scope_exit_name_drift", "DeadEnd: drift the post-scope ∀-fact hyp name _h_hoist_1→_h_hoist_2 (b81 R1 ordinal channel)", scope_exit_name_drift, "sst", "close"),
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
    L.append("-- bootstrap-79: the leaf-normalized comparison, retained for")
    L.append("-- reference — count_to_len's Loop classes used it while the")
    L.append("-- subject was A7-class. A7 landed (bootstrap-80): the Loop")
    L.append("-- classes now run the FULL deep bridge (strips unused).")
    L.append("noncomputable def strip : lib.GoalData → lib.GoalData")
    L.append("  | .All x t b => .All x t ⟨strip b.deref⟩")
    L.append("  | .Imp h b => .Imp h ⟨strip b.deref⟩")
    L.append("  | .Let x v b => .Let x v ⟨strip b.deref⟩")
    L.append("  | .LeafE _ => .LeafE (lib.ExprData.Atom 0)")
    L.append("  | .Leaf _ => .Leaf 0")
    L.append("noncomputable def strips : lib.GoalList → lib.GoalList")
    L.append("  | .Cons g t => .Cons ⟨strip g.deref⟩ ⟨(strips t.deref)⟩")
    L.append("  | .Nil => .Nil")
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
        # bootstrap-79: count_to_len's Loop classes used the leaf-normalized
        # comparison while the subject was A7-class. A7 LANDED (bootstrap-80,
        # 2026-07-31): count_to_len CLOSES the full deep bridge, so the
        # classes run at full strength now (norm = False; the strips
        # normalizer is retained above for reference).
        norm = False
        def cmp(sst_term, goals_term):
            if norm:
                return f"lib.goals_eq (strips (lib.ref_wp {cls}_ctx {sst_term})) (strips {goals_term})"
            return f"lib.goals_eq (lib.ref_wp {cls}_ctx {sst_term}) {goals_term}"
        if side == "goals":
            L.append(f"@[reducible] def {cls}_goals_mut : lib.GoalList := {mut_fn(goals)}")
            kill = cmp(f"{cls}_sst", f"{cls}_goals_mut")
        elif side == "sst":  # sst-side mutation: the reference's own input is perturbed
            L.append(f"@[reducible] def {cls}_sst_mut : lib.StmData := {mut_fn(sst)}")
            kill = cmp(f"{cls}_sst_mut", f"{cls}_goals")
        else:  # ctx-side mutation: the derivation input is perturbed (F4)
            L.append(f"@[reducible] def {cls}_ctx_mut : lib.FnCtxData := {mut_fn(ctx)}")
            kill = f"lib.goals_eq (lib.ref_wp {cls}_ctx_mut {cls}_sst) {cls}_goals"
        L.append(f"-- baseline: the unperturbed deep bridge closes.")
        L.append(f"example : {cmp(f'{cls}_sst', f'{cls}_goals')} = 1 := by decide")
        L.append(f"-- kill: the single-edit mutation FLIPS the bridge.")
        L.append(f"example : {kill} = 0 := by decide")
        L.append("")
        fired += 1

    out = pathlib.Path(__file__).with_name("ExprMutations.lean")
    out.write_text("\n".join(L))
    print(f"wrote {out}  ({fired} classes: baseline + coercion-drop kill each)")


if __name__ == "__main__":
    main()
