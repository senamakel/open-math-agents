import Mathlib

/-!
# A072031: A Lambert series identity for the divisor-counting function

Source: https://oeis.org/A072031
Credit: @senamakel

Peter Bala's comment gives the equivalent coefficient identity below.
The divisor count at zero is zero, as in the comment and Mathlib's
finite set of divisors.
-/

namespace OMA.S_oeis_a072031

open Finset

/-- The number of positive divisors, with `τ(0) = 0`. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- The coefficient identity for the square of the divisor Lambert series. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (∑ k ∈ Icc 1 n, tau k * tau (n - k)) =
      ∑ d ∈ n.divisors, ∑ k ∈ Icc 1 d, tau (k * (d - k)) := by
  sorry

end OMA.S_oeis_a072031
