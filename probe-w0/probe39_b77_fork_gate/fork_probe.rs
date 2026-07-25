// Fork-gate probe (A5 step-0): which value-if positions does production's
// walk_let fork? Three discriminating shapes, all default-closer.
use vstd::prelude::*;

verus! {

pub enum Tree {
    Leaf(u64),
    Node(Box<Tree>, Box<Tree>),
}

pub open spec fn tree_head(t: Tree) -> int {
    match t {
        Tree::Leaf(v) => v as int,
        Tree::Node(_l, _r) => 0,
    }
}

// P1: plain-cond value-if in RETURN position (max_u64's if, head_exec's position)
pub fn probe_if_ret(x: u64, y: u64) -> (r: u64)
    ensures r >= x, r >= y,
{
    if x < y { y } else { x }
}

// P2: plain-cond value-if in ASSIGN position (max_u64 twin)
pub fn probe_if_assign(x: u64, y: u64) -> (r: u64)
    ensures r >= x, r >= y,
{
    let m = if x < y { y } else { x };
    m
}

// P3: match (discriminator if) in ASSIGN position (head_exec's cond, max_u64's position)
pub fn probe_match_assign(t: &Tree) -> (r: u64)
    ensures r == tree_head(*t),
{
    let m = match t {
        Tree::Leaf(v) => *v,
        Tree::Node(_l, _r) => 0,
    };
    m
}

} // verus!
