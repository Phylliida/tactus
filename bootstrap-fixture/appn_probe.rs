// bootstrap-34 step 2a — SST/VIR dump probe for multi-arg (AppN/CallN).
// Purpose: settle the materialize-vs-elide fork (probe18_appn/REPORT.md
// "Architectural fork"). Does Verus (lean-backend) render an implicit
// per-arg u64->nat call coercion as a Clip node *inside the arg subexpr*
// (world (a): existing no-TypData render_list suffices, just widen the
// fail-loud arms), or does it ELIDE it and leave the arg bare u64 with the
// expected type only derivable from the callee signature (world (b): the
// cache-churning per-arg-TypData RawList edit is load-bearing)?
//
// Dump both levels (raw_exp reads SST Exp; raw_vir_exp reads VIR ExprX):
//   ../source/target-verus/release/verus --crate-type=lib --lean-backend \
//     --log-dir .verus-log-appn --log vir --log vir-sst appn_probe.rs
//
// Read the args of each `g2*` Call in crate.vir / crate.sst: bare Var(x)
// (elide) vs Clip{Nat}(Var x) (materialize)?

use vstd::prelude::*;

verus! {

// heterogeneous 2-arg spec fn: param 0 nat, param 1 int (the Case-B shape)
pub open spec fn g2(a: nat, b: int) -> int {
    a as int + b
}

// caller EXPLICIT: arg 0 has a source `as nat`, arg 1 bare int (no coercion)
pub open spec fn call_explicit(x: u64, y: int) -> int {
    g2(x as nat, y)
}

// FINDING (step 2a): the implicit callers `g2(x, y)` / `g2n(x, m)` are HARD
// TYPE ERRORS in Verus spec code (`expected nat, found u64`). So there are NO
// implicit per-arg call coercions — every coercion is a source `as` = a Clip
// node inside the arg. (World (a): materialize.) Kept explicit callers only.

// homogeneous 2-arg (both nat) — the Case-A shape, both args coerce
pub open spec fn g2n(a: nat, b: nat) -> nat {
    a + b
}

pub open spec fn call_two_nat_explicit(x: u64, m: u64) -> nat {
    g2n(x as nat, m as nat)
}

// length-3 spine (Case D)
pub open spec fn g3(a: nat, b: int, c: nat) -> int {
    a as int + b + c as int
}

pub open spec fn call_three(x: u64, y: int, z: u64) -> int {
    g3(x as nat, y, z as nat)
}

// ── ref-deref-in-list-position (probe18 Case C): does a `&`-arg materialize
//    its `.deref`, or is it derived from the arg being ref-typed? This is the
//    SECONDARY question (orthogonal to per-arg TypData): render_list currently
//    has no per-element deref_if, unlike the single-arg Call arm. ──
pub enum Tree { Leaf(u64), Node(Box<Tree>, Box<Tree>) }

pub open spec fn count_at(a: nat, t: Tree) -> nat
    decreases t
{
    match t {
        Tree::Leaf(v) => a + v as nat,
        Tree::Node(l, r) => count_at(a, *l) + count_at(a, *r),
    }
}

// exec fn with a &Tree param whose ensures calls the 2-arg spec fn with the
// ref — the head_exec pattern that made the single-arg deref_if fire.
pub fn call_ref(n: u64, t: &Tree) -> (r: u64)
    ensures true,
{
    let _g: Ghost<nat> = Ghost(count_at(n as nat, *t));
    0
}

} // verus!
