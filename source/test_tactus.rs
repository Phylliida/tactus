use builtin::*;
use builtin_macros::*;

verus! {

spec fn double(x: nat) -> nat {
    x + x
}

#[verifier::tactic]
proof fn lemma_double_pos(x: nat)
    requires x > 0
    ensures double(x) > x
{
    unfold double; omega
}

} // verus!
