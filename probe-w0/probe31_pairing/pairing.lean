-- ══════════════════════════════════════════════════════════════════════
-- W5f v2 / board bootstrap-58 — FEASIBILITY probe for the deferred hard kernel.
--
-- bootstrap-57 (rung 3) grounded ctorTag/ctorField to a REAL parity encoding of
-- fixlib.Tree, but the Node encoding stores only the SUM `embTree l + embTree r`
-- (`2·(embTree l + embTree r)+1`), so it is NOT injective on Node children — a
-- faithful Node-child DECODE needs an invertible UNBOUNDED PAIRING for
-- `(embTree l, embTree r)`.
--
-- bootstrap-58's recon flagged this as the crux worry: "Cantor (needs a triangular
-- sqrt) / 2-adic (needs a valuation) are OUTSIDE omega's Presburger fragment, and
-- there is no Mathlib in the probe." This left OPEN whether an injective pairing
-- with a machine-checked round-trip is even ACHIEVABLE in the probe environment.
--
-- THIS PROBE settles that question: YES. A bit-interleaving pairing sidesteps the
-- Presburger obstacle entirely — it needs neither a sqrt nor a valuation, only
-- per-digit `%2` / `/2` / `/4` arithmetic, each step of which IS in omega's
-- fragment. Making it FUEL-STRUCTURAL (recursion on an explicit fuel Nat) also
-- avoids any well-founded-termination proof, so the whole thing is: three
-- structural defs + two round-trip theorems by induction on fuel, each step a
-- single `omega`. No Mathlib. No wf. No sorry. Standard axioms only.
--
-- This is the reusable FOUNDATION a future Node-child decode plugs into:
--   embTree (Node l r) := 2 * pair (zz (embTree l)) (zz (embTree r)) + 1
-- (zz = the Int→Nat zig-zag below), whose two children are recovered by
-- unfst/unsnd. The tree-integration + the Int seam is the remaining engineering
-- (still deferred: the census has no live Node-child-inspecting Match — see
-- board bootstrap-58), but the mathematically hard part — the unbounded invertible
-- pairing the card feared — is DISCHARGED here.
-- ══════════════════════════════════════════════════════════════════════

set_option autoImplicit false

namespace Probe31Pairing

-- ── the pairing (bit-interleave): bit i of `a` goes to output position 2i, bit i
--    of `b` to position 2i+1. `fuel` bounds how many bit-pairs are woven — a `pair`
--    is faithful once `fuel` exceeds the bit-length of both inputs (the round-trip
--    theorems below make that `a < 2^fuel ∧ b < 2^fuel` hypothesis explicit). ──
def pair : Nat → Nat → Nat → Nat
  | 0,          _, _ => 0
  | Nat.succ f, a, b => (a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2)

-- ── the two projections. `unfst` reads the even bit-positions (a's bits),
--    `unsnd` the odd ones (b's bits); both peel two output bits per step (`/4`). ──
def unfst : Nat → Nat → Nat
  | 0,          _ => 0
  | Nat.succ f, n => (n % 2) + 2 * unfst f (n / 4)

def unsnd : Nat → Nat → Nat
  | 0,          _ => 0
  | Nat.succ f, n => ((n / 2) % 2) + 2 * unsnd f (n / 4)

-- ── the head equations (rfl-grade; make the unfolds explicit for the proofs). ──
theorem pair_succ (f a b : Nat) :
    pair (f + 1) a b = (a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2) := rfl
theorem unfst_succ (f n : Nat) :
    unfst (f + 1) n = (n % 2) + 2 * unfst f (n / 4) := rfl
theorem unsnd_succ (f n : Nat) :
    unsnd (f + 1) n = ((n / 2) % 2) + 2 * unsnd f (n / 4) := rfl

-- ══ ROUND-TRIP 1 — the first projection inverts the pairing (given enough fuel).
--    Induction on fuel; each step is one omega over the peeled bits. The `2^(f+1) =
--    2^f * 2` step (via Nat.pow_succ, core — no Mathlib) lets omega propagate the
--    bit-length bound to the children with `2^f` held abstract. ══
theorem unfst_pair (f : Nat) : ∀ a b : Nat, a < 2 ^ f → b < 2 ^ f →
    unfst f (pair f a b) = a := by
  induction f with
  | zero =>
    intro a b ha _hb
    -- a < 2^0 = 1 ⇒ a = 0; unfst 0 _ = 0.
    simp only [Nat.pow_zero] at ha
    show (0 : Nat) = a
    omega
  | succ f ih =>
    intro a b ha hb
    have hpow : (2 : Nat) ^ (f + 1) = 2 ^ f * 2 := by rw [Nat.pow_succ]
    -- child bounds: a/2 < 2^f, b/2 < 2^f (with 2^f abstract, from the succ bound).
    have ha2 : a / 2 < 2 ^ f := by rw [hpow] at ha; omega
    have hb2 : b / 2 < 2 ^ f := by rw [hpow] at hb; omega
    have hchild := ih (a / 2) (b / 2) ha2 hb2   -- IH: unfst f (pair f (a/2)(b/2)) = a/2
    rw [pair_succ, unfst_succ]
    -- n = (a%2) + 2*(b%2) + 4*P where P = pair f (a/2)(b/2).
    -- n % 2 = a%2  and  n / 4 = P  (both omega: a%2<2, b%2<2 ⇒ the low part < 4).
    have hlow : ((a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2)) % 2 = a % 2 := by omega
    have hdiv : ((a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2)) / 4
              = pair f (a / 2) (b / 2) := by omega
    rw [hlow, hdiv, hchild]
    -- (a % 2) + 2 * (a / 2) = a.
    omega

-- ══ ROUND-TRIP 2 — the second projection inverts the pairing. Same shape; the odd
--    bit-lane is read by `(n/2) % 2`. ══
theorem unsnd_pair (f : Nat) : ∀ a b : Nat, a < 2 ^ f → b < 2 ^ f →
    unsnd f (pair f a b) = b := by
  induction f with
  | zero =>
    intro a b _ha hb
    simp only [Nat.pow_zero] at hb
    show (0 : Nat) = b
    omega
  | succ f ih =>
    intro a b ha hb
    have hpow : (2 : Nat) ^ (f + 1) = 2 ^ f * 2 := by rw [Nat.pow_succ]
    have ha2 : a / 2 < 2 ^ f := by rw [hpow] at ha; omega
    have hb2 : b / 2 < 2 ^ f := by rw [hpow] at hb; omega
    have hchild := ih (a / 2) (b / 2) ha2 hb2
    rw [pair_succ, unsnd_succ]
    have hlane : (((a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2)) / 2) % 2 = b % 2 := by
      omega
    have hdiv : ((a % 2) + 2 * (b % 2) + 4 * pair f (a / 2) (b / 2)) / 4
              = pair f (a / 2) (b / 2) := by omega
    rw [hlane, hdiv, hchild]
    omega

-- ══ INJECTIVITY (the property the Node decode actually needs) — a corollary of the
--    two round-trips: equal codes with enough fuel ⇒ equal component pairs. ══
theorem pair_injective (f a b a' b' : Nat)
    (ha : a < 2 ^ f) (hb : b < 2 ^ f) (ha' : a' < 2 ^ f) (hb' : b' < 2 ^ f)
    (h : pair f a b = pair f a' b') : a = a' ∧ b = b' := by
  constructor
  · have e1 := unfst_pair f a b ha hb
    have e2 := unfst_pair f a' b' ha' hb'
    rw [h] at e1
    rw [e1] at e2
    exact e2
  · have e1 := unsnd_pair f a b ha hb
    have e2 := unsnd_pair f a' b' ha' hb'
    rw [h] at e1
    rw [e1] at e2
    exact e2

-- ══ THE Int SEAM (completing the picture) — `embTree (Leaf v) = 2·v` ranges over
--    ALL Int (v : Int, incl. negatives), so a real Node decode first maps Int→Nat
--    injectively via the zig-zag `zz` before pairing; `unzz` inverts it. Both
--    round-trips are pure omega (the zig-zag IS in the Presburger fragment). ══
def zz (x : Int) : Nat := if x ≥ 0 then 2 * x.toNat else 2 * (-x).toNat - 1
def unzz (n : Nat) : Int := if n % 2 = 0 then (n / 2 : Int) else -(((n : Int) + 1) / 2)

theorem unzz_zz (x : Int) : unzz (zz x) = x := by
  unfold zz unzz
  split <;> omega

end Probe31Pairing

-- ══════════════════════════════════════════════════════════════════════
-- axiom closure (the whole point of the probe): the injective pairing + its two
-- round-trips + the Int-seam zig-zag close over ONLY standard axioms. No Mathlib,
-- no Classical.choice, no sorryAx — the pairing the bootstrap-58 card feared was
-- "outside omega's Presburger fragment / no Mathlib" is discharged by fuel-
-- structural bit-interleaving + per-step omega. Expect `[propext]` (or empty).
-- ══════════════════════════════════════════════════════════════════════
#print axioms Probe31Pairing.unfst_pair
#print axioms Probe31Pairing.unsnd_pair
#print axioms Probe31Pairing.pair_injective
#print axioms Probe31Pairing.unzz_zz
