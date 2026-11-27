import Mathlib

/-!
# A055203 interval relation counts

Source: https://oeis.org/A055203
The weighted Stirling formula is given by Vladeta Jovovic in the entry.
For a positive modulus, an eventual period equal to its totient is
equivalent to the least positive eventual period dividing the totient.
-/

open scoped BigOperators

namespace OMA.S_oeis_a055203

/-- The sum of the counts of labelled graphs with `k` edges and no isolated
vertices. The inner sum excludes isolated vertices by inclusion–exclusion. -/
def weight (k : ℕ) : ℤ :=
  ∑ v ∈ Finset.range (2 * k + 1),
    ∑ i ∈ Finset.range (v + 1),
      (-1 : ℤ) ^ (v - i) * (v.choose i : ℤ) * ((i.choose 2).choose k : ℤ)

/-- OEIS A055203, using its weighted Stirling formula. -/
def term (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * Nat.stirlingSecond n k * weight k

theorem main :
    (∀ n, (term n : ZMod 12) = 1) ∧
      (∀ m : ℕ, 0 < m → ∃ N : ℕ, ∀ n ≥ N,
        (term (n + m.totient) : ZMod m) = (term n : ZMod m)) := by
  sorry

end OMA.S_oeis_a055203
