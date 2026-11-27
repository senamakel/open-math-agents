import Mathlib

/-!
# A091258: Denominators of the quotient of divisor sums

Source: https://oeis.org/A091258
Comparison sequence: https://oeis.org/A004611
Credit: @senamakel

Michel Marcus's conjecture says the set of reduced denominators of
`σ₃(n) / σ₁(n)` for positive `n` is the set of positive integers whose
prime divisors are all congruent to one modulo three.
-/

namespace OMA.S_oeis_a091258

open scoped ArithmeticFunction.sigma

/-- Reduced denominator of the quotient of the two divisor sums. -/
def denominator (n : ℕ) : ℕ := ((σ 3 n : ℚ) / (σ 1 n : ℚ)).den

/-- The set of distinct terms of A091258 is A004611. -/
theorem main :
    {d : ℕ | ∃ n : ℕ, 0 < n ∧ denominator n = d} =
      {d : ℕ | 0 < d ∧ ∀ q : ℕ, q.Prime → q ∣ d → q % 3 = 1} := by
  sorry

end OMA.S_oeis_a091258
