// nla-15 gate probe: the verified `nonlinear_arith` primary arm,
// decisive edition. o139 over `int` — the transitivity-of-fractions
// census goal (a·db ≤ b·da ∧ b·dc ≤ c·db ∧ denoms positive ⊢
// a·dc ≤ c·da). nlinarith CANNOT close this shape (the certificate
// needs degree-3 cross products — the multiplier-pool ladder's caps
// exclude them); z3-4.12.5 closes it via nlsat (6 conflicts). If this
// file verifies, the new arm did something the old ladder
// structurally could not.
//
//   Check:
//     ../source/target-verus/release/verus --crate-type=lib \
//       --lean-backend nla15_probe.rs

use vstd::prelude::*;

verus! {

pub proof fn o139_int(a: int, b: int, c: int, da: int, db: int, dc: int)
    requires
        a * db <= b * da,
        b * dc <= c * db,
        0 < da,
        0 < db,
        0 < dc,
{
    assert(a * dc <= c * da) by(nonlinear_arith);
}

} // verus!
