// W1.5/W1 de-risk probe: the tactus-core AUTHORING IDIOM, end to end.
// Mirror-type shape: recursive datatype through Box + own cons-list
// (NOT Seq — opaque axiom type, kernel-inert). Mutual-style recursion
// via two fns. Question answered on the emitted Lean (probe8):
// does `termination_by structural` accept recursion through Box.deref,
// and does the def then kernel-reduce (decide/rfl)?
//
//   Canonical check (live Lean, package gate — N1a validated: 5/0,
//   composition + axiom closures kernel-verified):
//     TACTUS_LEAN_OUT=$PWD/out ../source/target-verus/release/verus \
//       --crate-type=lib --lean-backend --lean-all-proofs \
//       --tactus-package-check w15_probe.rs
//   Emission-only corpus dump (islands into out/, no Lean run):
//     add --emit-lean, drop --tactus-package-check

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

#[verifier::structural_decreases]
pub open spec fn esize(e: PExpr) -> nat
    decreases e
{
    match e {
        PExpr::Lit(_v) => 1,
        PExpr::Add(a, b) => esize(*a) + esize(*b),
    }
}

#[verifier::structural_decreases]
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

#[verifier::structural_decreases]
pub open spec fn tsize(t: Tree2) -> nat
    decreases t
{
    match t { Tree2::Leaf2(_v) => 1, Tree2::Node2(a, b) => tsize(*a) + tsize(*b) }
}

proof fn use_head_size(t: Tree2) ensures head_size(t) >= 0 by { simp }

} // verus!

verus! {

// N1c probe 1 (SST ctor class): exec body CONSTRUCTS a Box-field datatype;
// the ensures compares against the spec-side ctor (VIR-AST path, fixed).
// Exercises whether the SST renderer re-wraps erased Box::new at ctor slots.
pub fn mk_node(a: u64, b: u64) -> (r: Tree2)
    ensures r == Tree2::Node2(Box::new(Tree2::Leaf2(a)), Box::new(Tree2::Leaf2(b)))
{
    Tree2::Node2(Box::new(Tree2::Leaf2(a)), Box::new(Tree2::Leaf2(b)))
}

// N1c probe 2 (SST match-binder class): exec match BINDS a Box-typed field
// and uses it at inner type (deref through the binder), mirrored by a
// spec fn with the same shape.
pub open spec fn spec_left_val(t: Tree2) -> u64 {
    match t {
        Tree2::Leaf2(v) => v,
        Tree2::Node2(l, _r) => match *l {
            Tree2::Leaf2(v) => v,
            Tree2::Node2(_, _) => 0,
        },
    }
}

#[verifier::tactus_tactic("simp only [w15_probe.spec_left_val]; split <;> cases ht : t.deref <;> simp_all <;> (try (split <;> simp_all)) <;> (try (split <;> simp_all))")]
pub fn left_val(t: &Tree2) -> (r: u64)
    ensures r == spec_left_val(*t)
{
    match t {
        Tree2::Leaf2(v) => *v,
        Tree2::Node2(l, _r) => match &**l {
            Tree2::Leaf2(v) => *v,
            Tree2::Node2(_, _) => 0,
        },
    }
}

} // verus!
