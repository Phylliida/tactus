use builtin::*;
use builtin_macros::*;

verus! {

spec fn double(x: nat) -> nat {
    x + x
}

proof fn lemma_double_pos(x: nat)
    requires x > 0
    ensures double(x) > x
{
    // Tactic body: unfold double; omega
    unfold double; omega
}

} // verus!
