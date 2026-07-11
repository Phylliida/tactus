// W1.5/W1 de-risk probe: the tactus-core AUTHORING IDIOM, end to end.
// Mirror-type shape: recursive datatype through Box + own cons-list
// (NOT Seq — opaque axiom type, kernel-inert). Mutual-style recursion
// via two fns. Question answered on the emitted Lean (probe8):
// does `termination_by structural` accept recursion through Box.deref,
// and does the def then kernel-reduce (decide/rfl)?
//
//   TACTUS_LEAN_OUT=$PWD/out <tactus>/source/target-verus/release/verus \
//     --crate-type=lib --lean-backend --emit-lean --lean-all-proofs w15_probe.rs

use vstd::prelude::*;

verus! {

pub enum PExpr {
    Lit(u64),
    Add(Box<PExpr>, Box<PExpr>),
}

pub enum PList {
    Nil,
    Cons(Box<PExpr>, Box<PList>),
}

pub open spec fn esize(e: PExpr) -> nat
    decreases e
{
    match e {
        PExpr::Lit(_v) => 1,
        PExpr::Add(a, b) => esize(*a) + esize(*b),
    }
}

pub open spec fn lsize(l: PList) -> nat
    decreases l
{
    match l {
        PList::Nil => 0,
        PList::Cons(h, t) => esize(*h) + lsize(*t),
    }
}

} // verus!

verus! {

proof fn use_sizes(e: PExpr, l: PList)
    ensures esize(e) >= 0, lsize(l) >= 0
by { constructor <;> omega }

} // verus!

verus! {

// Review probe: plain `let` of a Box-typed value in a spec body — the
// block_to_node Decl path (documented residue of the pattern-binder fix).
pub open spec fn head_size(t: Tree2) -> nat {
    match t {
        Tree2::Leaf2(_v) => 0,
        Tree2::Node2(l, _r) => { let b = l; tsize(*b) }
    }
}

pub enum Tree2 { Leaf2(u64), Node2(Box<Tree2>, Box<Tree2>) }

pub open spec fn tsize(t: Tree2) -> nat
    decreases t
{
    match t { Tree2::Leaf2(_v) => 1, Tree2::Node2(a, b) => tsize(*a) + tsize(*b) }
}

proof fn use_head_size(t: Tree2) ensures head_size(t) >= 0 by { simp }

} // verus!
