import Mathlib

/-!
# A131662: Consecutive divisibility by each integer from 1 to 12

Source: https://oeis.org/A131662
Credit: @senamakel

The positive qualifying integers are enumerated in increasing order.
The generating function starts at index one. The constant term is zero.
The rational generating-function identity is stated after multiplying by
the denominator, which has constant term one.
-/

namespace OMA.S_oeis_a131662

/-- Every divisor in the given range divides at least one of n and n+1. -/
def qualifies (n : ℕ) : Prop :=
  0 < n ∧ ∀ d : ℕ, 1 ≤ d → d ≤ 12 → d ∣ n ∨ d ∣ n+1

/-- The positive sequence with a zero constant term for its generating function. -/
noncomputable def term : ℕ → ℕ
  | 0 => 0
  | n+1 => Nat.nth qualifies n

open PowerSeries

noncomputable def denominator : PowerSeries ℤ :=
  (1-X)^2 * (1+X) * (1+X^2) * (1+X^4)

noncomputable def numerator : PowerSeries ℤ :=
  X * (2519 + 9360*X + 1441*X^2 + 1079*X^3 + 1441*X^4 +
    9360*X^5 + 2519*X^6 + X^7)

noncomputable def series : PowerSeries ℤ := mk (fun n => (term n : ℤ))

/-- Colin Barker's generating function and recurrence. -/
theorem main :
    denominator * series = numerator ∧
    ∀ n : ℕ, 9 < n → term n + term (n-9) = term (n-1) + term (n-8) := by
  sorry

end OMA.S_oeis_a131662
