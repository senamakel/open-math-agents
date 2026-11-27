import Mathlib

/-!
# A211419: Divisibility of a factorial ratio by products of linear factors

Source: https://oeis.org/A211419
Credit: @senamakel

The assertions are stated after clearing the positive factorial denominator.
The third family uses integer factors, including negative factors at small n.
-/

namespace OMA.S_oeis_a211419

open Finset

def numerator (n : ℕ) : ℤ := ((6*n).factorial : ℤ) * ((2*n).factorial : ℤ)
def denominator (n : ℕ) : ℤ := ((4*n).factorial : ℤ) * ((3*n).factorial : ℤ) * (n.factorial : ℤ)

def factorsC (r n : ℕ) : ℤ := ∏ i ∈ range r, ((n : ℤ) + i + 1)
def factorsD (r n : ℕ) : ℤ := ∏ i ∈ range r, (4*(n : ℤ) + 2*i + 1)
def factorsK (r n : ℕ) : ℤ := ∏ i ∈ range r, (6*(n : ℤ) - (2*i + 1))

/-- The three explicit factors and the three uniform multiplier families. -/
theorem main :
    (∀ n : ℕ, denominator n * ((n : ℤ)+1) ∣ 5*numerator n) ∧
    (∀ n : ℕ, denominator n * (4*(n : ℤ)+1) ∣ numerator n) ∧
    (∀ n : ℕ, denominator n * (6*(n : ℤ)-1) ∣ numerator n) ∧
    (∀ r : ℕ, 0 < r → ∃ C : ℤ, 0 < C ∧
      ∀ n : ℕ, denominator n * factorsC r n ∣ C * numerator n) ∧
    (∀ r : ℕ, 0 < r → ∃ D : ℤ, 0 < D ∧
      ∀ n : ℕ, denominator n * factorsD r n ∣ D * numerator n) ∧
    (∀ r : ℕ, 0 < r → ∃ K : ℤ, 0 < K ∧
      ∀ n : ℕ, denominator n * factorsK r n ∣ K * numerator n) := by
  sorry

end OMA.S_oeis_a211419
