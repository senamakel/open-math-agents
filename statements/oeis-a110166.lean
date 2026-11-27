import Mathlib

/-!
# A110166: Counting words with at least as many zeros as ones

Source: https://oeis.org/A110166
Credit: @senamakel

Peter Bala conjectures a coefficient formula and a recurrence for this
count for every alphabet size at least two.
-/

namespace OMA.S_oeis_a110166

/-- Number of occurrences of a digit in a word. -/
def occurrences {k n : ℕ} (w : Fin n → Fin k) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => (w j).val = i)).card

/-- Number of k-ary words of length n with no more ones than zeros. -/
def wordCount (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin k => occurrences w 1 ≤ occurrences w 0)).card

/-- The series kX + 1/(1+X), represented by its integral coefficients. -/
noncomputable def series (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C (k : ℤ) * PowerSeries.X +
    PowerSeries.rescale (-1 : ℤ) (PowerSeries.invOneSubPow ℤ 1).val

/-- Both of Bala's formulas, with the recurrence at index n+2. -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    (∀ n : ℕ, (wordCount k n : ℤ) = PowerSeries.coeff n (series k ^ n)) ∧
    wordCount k 0 = 1 ∧ wordCount k 1 = k - 1 ∧
    (∀ n : ℕ, ((n : ℤ) + 2) * (wordCount k (n + 2) : ℤ) =
      ((k : ℤ) - 2) * (2 * (n : ℤ) + 3) * (wordCount k (n + 1) : ℤ) -
        (k : ℤ) * ((k : ℤ) - 4) * ((n : ℤ) + 1) * (wordCount k n : ℤ) +
        (k : ℤ) ^ (n + 1)) := by
  sorry

end OMA.S_oeis_a110166
