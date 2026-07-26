// Bootstrap fixture crate — the canonical minimal module covering every
// SST/goal shape the R2 bridge must handle (DESIGN-bootstrap.md W0/W1/W3).
// Each item is labeled with the feature it pins. Deliberately tiny fns:
// one shape each. This crate is the differential-gate seed corpus (W3)
// and the hand-bridge target set (W0 residue).
//
// Emit with (from the repo root, main checkout binary is fine read-only):
//   TACTUS_LEAN_OUT=$PWD/bootstrap-fixture/out \
//   <tactus>/source/target-verus/release/verus --crate-type=lib \
//     --lean-backend --emit-lean --lean-all-proofs bootstrap-fixture/lib.rs

use vstd::prelude::*;

verus! {

// ── Defs-layer shapes (W7 targets, referenced by goals below) ──────────────

// F1: plain spec fn
pub open spec fn sq(x: nat) -> nat { x * x }

// F2: recursive spec fn, bare-Nat-param decreases (the W1.5 structural target)
pub open spec fn tri(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 } else { n + tri((n - 1) as nat) }
}

// F3: user datatype + match + datatype-decreases recursive spec fn
//     (height-measure emission; accessors; Box decoration)
pub enum Tree {
    Leaf(u64),
    Node(Box<Tree>, Box<Tree>),
}

pub open spec fn sum_tree(t: Tree) -> nat
    decreases t
{
    match t {
        Tree::Leaf(v) => v as nat,
        Tree::Node(l, r) => sum_tree(*l) + sum_tree(*r),
    }
}

pub open spec fn tree_head(t: Tree) -> u64 {
    match t {
        Tree::Leaf(v) => v,
        Tree::Node(_l, _r) => 0,
    }
}

// F20 (W7 / bootstrap-34): multi-arg spec-fn application in a def body — the
// `AppN`/`CallN` shape. The callers' bodies (`g2(x, y)`, `g3(x, y, z)`) are the
// only ≥2-arg calls in the fixture, so they force the widened `raw_vir_exp` /
// `lexpr_to_exprdata` arms and close the `def_eq` bridge over `AppN`. Kept
// all-`nat` (no per-arg `as` cast) to isolate the flat multi-arg spine from the
// Cast machinery — the step-2a dump proved any real coercion rides a `Clip`
// INSIDE the arg, handled by the existing per-node recursion, not the list.
pub open spec fn g2(a: nat, b: nat) -> nat { a + b }

pub open spec fn call_g2(x: nat, y: nat) -> nat { g2(x, y) }

pub open spec fn g3(a: nat, b: nat, c: nat) -> nat { a + b + c }

pub open spec fn call_g3(x: nat, y: nat, z: nat) -> nat { g3(x, y, z) }

// Keep the F20 spec fns alive through Verus dead-code pruning: an unreferenced
// `open spec fn` is dropped from the pruned krate before emission, so it would
// never reach the def-cert pass. A ghost reference in an exec body pulls
// `call_g2`/`call_g3` — and transitively `g2`/`g3` — into the emitted defs
// (the `appn_probe.rs` keep-alive pattern). `ensures true` cannot fail, so this
// is verification-neutral for the e2e/differential gate.
pub fn use_multiarg(x: u64) -> (r: u64)
    ensures true,
{
    let _g2: Ghost<nat> = Ghost(call_g2(x as nat, x as nat));
    let _g3: Ghost<nat> = Ghost(call_g3(x as nat, x as nat, x as nat));
    0
}

// ── proof-fn shapes ─────────────────────────────────────────────────────────

// F4: plain proof fn, no tactic block (the --lean-all-proofs route; fuel unfold)
proof fn tri_one()
    ensures tri(1) == 1,
{
    assert(tri(0) == 0);
}

// F21 (W7 residual, bootstrap-36): a >=2-arg spec-fn call in OBLIGATION
// position. `tri_one` above covers the single-arg `Call` arm of `raw_exp`
// (its `tri(1)==1` ensures emits `RawExp.Call` in the SST obligation slot);
// these force the WIDENED `raw_exp` `CallN` arm (bootstrap-34, L708) into an
// obligation slot so the refWp obligation bridge (probe9) exercises the live
// `CallN -> AppN` render on the SST side — the one path bootstrap-34 left
// covered only on the DEF side (VIR `raw_vir_exp`). Both are pure-`nat` (no
// per-arg `as` cast), so the obligation is the flat multi-arg spine. Bodies
// are empty: `g2`/`g3` are `open spec fn`, so each ensures unfolds
// definitionally (`g2(x,y)==x+y` -> `x+y==x+y`), no tactic needed.
proof fn call_g2_ob(x: nat, y: nat)
    ensures g2(x, y) == x + y,
{
}

proof fn call_g3_ob(x: nat, y: nat, z: nat)
    ensures g3(x, y, z) == x + y + z,
{
}

// F5: tactic-block proof fn (verbatim pass-through)
proof fn add_comm_t(a: int, b: int)
    ensures a + b == b + a
by { omega }

// F6: assert-by with a user tactic inside an exec fn (Wp::Scope / DeadEnd)
//     — see also F9's invariant asserts. (Verus-style assert-by in plain
//     proof fns is the StmX::DeadEnd family from the F4 arc.)
proof fn scope_shape(n: nat)
    ensures tri(n) >= 0,
{
    assert(tri(n) >= 0);
}

// F14: the cast-shape pins (DECISION-cast-rendering): elided var cast vs
//      compound materialization — (x as nat) * (x as nat) vs sq
proof fn cast_shapes(x: u64)
    ensures (x as nat) * (x as nat) == sq(x as nat)
by { simp only [sq] }

// ── exec-fn shapes ──────────────────────────────────────────────────────────

// F7: let-binding, mutation, overflow obligation, inline assert
pub fn add_capped(x: u64, y: u64) -> (r: u64)
    requires x < 1000, y < 1000,
    ensures r == x + y,
{
    let mut s = x + y;
    assert(s < 2000);
    s = s + 0;
    s
}

// F8: value-position if (walk_let fork)
pub fn max_u64(x: u64, y: u64) -> (r: u64)
    ensures r >= x, r >= y,
{
    let m = if x < y { y } else { x };
    m
}

// F9: while loop — invariant init/maintain/use triple, havoc, decreases,
//     cast in invariant ((acc as nat) == tri(...)), user assert-by-tactic
pub fn sum_to(n: u64) -> (r: u64)
    requires n <= 1000,
    ensures r as nat == tri(n as nat),
{
    let mut i: u64 = 0;
    let mut acc: u64 = 0;
    while i < n
        invariant
            i <= n,
            n <= 1000,
            acc as nat == tri(i as nat),
            acc <= 1000 * 1000,
        decreases n - i,
    {
        i = i + 1;
        acc = acc + i;
    }
    acc
}

// F10: nested loop + early `return` (early-exit control flow)
pub fn find_square(limit: u64) -> (r: u64)
    requires limit < 100,
    ensures true,
{
    let mut a: u64 = 0;
    while a < limit
        invariant a <= limit, limit < 100,
        decreases limit - a,
    {
        let mut b: u64 = 0;
        while b < limit
            invariant b <= limit, a < limit, limit < 100,
            decreases limit - b,
        {
            if a * b == 36 {
                return a;
            }
            b = b + 1;
        }
        a = a + 1;
    }
    0
}

// F12a: exec call with contract inlining at the call site
pub fn double_exec(x: u64) -> (r: u64)
    requires x < 1000,
    ensures r == 2 * x,
{
    x + x
}

pub fn quad_exec(x: u64) -> (r: u64)
    requires x < 500,
    ensures r == 4 * x,
{
    let a = double_exec(x);
    double_exec(a / 2) + a
}

// F12b: exec recursion with decreases (CheckDecreaseHeight family)
pub fn count_down(n: u64) -> (r: u64)
    ensures r == 0,
    decreases n,
{
    if n == 0 { 0 } else { count_down(n - 1) }
}

// F13: Vec — view dispatch (v@), index bounds obligation, &mut + old()
pub fn vec_read(v: &Vec<u64>, i: usize) -> (r: u64)
    requires i < v@.len(),
    ensures r == v@[i as int],
{
    v[i]
}

pub fn vec_push7(v: &mut Vec<u64>)
    requires old(v)@.len() < 100,
    ensures v@.len() == old(v)@.len() + 1, v@[old(v)@.len() as int] == 7,
{
    v.push(7);
}

// F14b (bootstrap-78 S3): the minimal-mut pair. `inc` is a USER `&mut`
// callee (new-mut-ref MutRef encoding — unlike the vstd legacy-`is_mut`
// `Vec::push`), so `call_inc` exercises the caller-side BorrowMut
// machinery; `u64` makes the mut-post existential carry a TYPE-BOUND
// hyp and the rebind a wrapper COERCION (`.deref`) — the two channels
// vec_push7's Vec subject leaves dormant (card §Open-items).
pub fn inc(x: &mut u64)
    requires *old(x) < 1000,
    ensures *x == *old(x) + 1,
{
    *x = *x + 1;
}

pub fn call_inc(y: u64) -> (r: u64)
    requires y < 500,
    ensures r == y + 2,
{
    let mut z = y;
    inc(&mut z);
    inc(&mut z);
    z
}

// F15: generic fn (type param; Nonempty-bracket plumbing on the spec side)
pub fn id_generic<T>(t: T) -> (r: T)
    ensures r == t,
{
    t
}

// F17: match on user enum in exec (case split), Box deref, accessor shapes
pub fn head_exec(t: &Tree) -> (r: u64)
    ensures r == tree_head(*t),
{
    match t {
        Tree::Leaf(v) => *v,
        Tree::Node(_l, _r) => 0,
    }
}

// F18: forall in ensures + invariant (quantified goal shapes)
pub fn fill_zeros(n: usize) -> (v: Vec<u64>)
    requires n < 100,
    ensures
        v@.len() == n as nat,
        forall|k: int| 0 <= k < n as int ==> v@[k] == 0,
{
    let mut v: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> v@[k] == 0,
        decreases n - i,
    {
        v.push(0);
        i = i + 1;
    }
    v
}

// F19: struct + tuple shapes
pub struct Point { pub x: u64, pub y: u64 }

pub fn mk_point(a: u64, b: u64) -> (p: Point)
    ensures p.x == a, p.y == b,
{
    Point { x: a, y: b }
}

pub fn swap_pair(a: u64, b: u64) -> (r: (u64, u64))
    ensures r.0 == b, r.1 == a,
{
    (b, a)
}

// F21 (bootstrap-71): ∀-path Call — callee ensures carry no `r == E`
// conjunct, so the post-call frame takes the FBind ∀-path
// (`FBind(dest, ret_typ, FHyp(ret_bound) FHyp(ens))`), not the #128
// ret-eq substitution path.
pub fn clamped_inc(x: u64) -> (r: u64)
    ensures r >= x, r <= x + 1,
{
    if x < 0xFFFF_FFFF_FFFF_FFFF { x + 1 } else { x }
}

pub fn use_clamped(a: u64) -> (r: u64)
    requires a < 1000,
    ensures r >= a,
{
    let t = clamped_inc(a);
    t
}

// F20 (bootstrap-69): assert-query NonLinear — an isolated
// `by(nonlinear_arith)` query inside an exec fn. The serializer emits
// `StmData.AssertQueryNl`; the refWp mirror recurses on the body under
// `strip_hyps(f)` (Let/Binder frames kept, Hyp frames dropped) with no
// frame delta for the continuation — the proven fact re-enters via the
// Assume production itself emits after the query.
pub fn mul_bound(a: u64, b: u64) -> (r: u64)
    requires a < 100, b < 100,
    ensures r == a * b, r < 10000,
{
    assert(a * b < 10000) by(nonlinear_arith)
        requires a < 100, b < 100;
    a * b
}

// F22 (bootstrap-77 A5): plain-cond value-if in RETURN position — the
// default Return route (`Wp::Let` → `walk_let`) FORKS it into per-branch
// goals with `_h_hoist_1 : cond` / `¬cond` hyps + per-branch RetLetH.
// The serializer mirrors via `ret_fork` → `StmData::If` (no ctor
// upgrade — the cond is a plain comparison).
pub fn pick_max(x: u64, y: u64) -> (r: u64)
    ensures r >= x, r >= y,
{
    if x < y { y } else { x }
}

// F23 (bootstrap-77 A5): match in ASSIGN position — the whole body folds
// into `Return(Bind(Let(m := If …), m))`, and `walk_let`'s Bind arm
// renders the binder RHS OPAQUE (b77 E1: NO fork; the if stays inside
// `_h_m_hoist1 : m = (if …)`). Negative control for the fork gate.
pub fn head_via_let(t: &Tree) -> (r: u64)
    ensures r == tree_head(*t),
{
    let m = match t {
        Tree::Leaf(v) => *v,
        Tree::Node(_l, _r) => 0,
    };
    m
}

// F24 (bootstrap-77 A3): Tactus-mode assert-by inside a DEFAULT-closer
// fn — production emits a separate `_tactus_assert_*` theorem for P
// (never hoisted: `emit_with_closer`) while the other goals hoist; the
// mirror closes the `StmData::AssertQueryTactus` obligation under
// `f + FUserCloser` (the R1 per-goal force-wrap, exercised nowhere in
// tgt — every tgt assert-query fn is wrap-mode by attr/proof-block).
pub fn assert_by_default(x: u64) -> (r: u64)
    requires x < 100,
    ensures r == x + 1,
{
    assert(x + 1 <= 100) by { omega };
    x + 1
}

// F25 (bootstrap-77 A3): proof-block prefix (Tactus kind ProofBlock) —
// structurally ABSENT from the mirror (the tactic rides the closer
// prefix, not stage-A-certified) but flips the fn-level
// `closer_is_default` DFS: this fn is wrap-mode, its Return keeps the
// legacy folded shape, and the cert's FnCtxData carries
// `closer_default = 0`.
pub fn proof_block_fn(x: u64) -> (r: u64)
    requires x < 100,
    ensures r == x + 1,
{
    proof { omega }
    x + 1
}

} // verus!
