import Mathlib

/-!
# OEIS A343260, a Chebyshev congruence

Source: https://oeis.org/A343260

The normalized Chebyshev polynomial satisfies C_n(2x) = 2 T_n(x).
Thus the sequence in the entry is C_n evaluated at n+1.
-/

namespace OMA.S_oeis_a343260

noncomputable def term (n : ℕ) : ℤ :=
  (Polynomial.Chebyshev.C ℤ (n : ℤ)).eval ((n : ℤ) + 1)

theorem main : ∀ p r : ℕ, p.Prime → 5 ≤ p → 0 < r →
    Int.ModEq ((p : ℤ) ^ (2*r)) (term (p^r)) 1 := by
  sorry

end OMA.S_oeis_a343260
