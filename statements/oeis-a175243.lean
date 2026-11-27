import Mathlib

/-!
# OEIS A175243, the complete prism spanning-tree array

Source: https://oeis.org/A175243

The terms are defined by the Chebyshev formula for the array given in the
source. A monic integer polynomial of degree d gives a homogeneous recurrence
of order d via its coefficients, with the last term having coefficient one.
-/

open scoped BigOperators

namespace OMA.S_oeis_a175243

noncomputable def column (m n : ℕ) : ℝ :=
  (n : ℝ) * (2 * (Polynomial.Chebyshev.T ℝ n).eval (1+(m : ℝ)/2)-2)^(m-1) / (m : ℝ)

theorem main : ∀ m : ℕ, 0 < m →
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 4*m-2 ∧
      ∀ n : ℕ, 0 < n →
        ∑ i ∈ Finset.range (P.natDegree+1), (P.coeff i : ℝ) * column m (n+i) = 0 := by
  sorry

end OMA.S_oeis_a175243
