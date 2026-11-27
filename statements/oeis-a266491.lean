import Mathlib

/-!
# A266491: Divisibility and first column of the difference rows

Source: https://oeis.org/A266491
Comparison sequence: https://oeis.org/A190621
Credit: @senamakel
-/

namespace OMA.S_oeis_a266491

/-- The sequence n times the periodic sequence 1, 1, 2, 2. -/
def base (n : ℕ) : ℤ := (n : ℤ) * if n % 4 < 2 then 1 else 2

/-- The value in column n of the i-th forward-difference row. -/
def row : ℕ → ℕ → ℤ
  | 0, n => base n
  | i + 1, n => row i (n + 1) - row i n

/-- The proposed divisor, 1,1,1,1,2,2,4,4, and so on. -/
def scale (i : ℕ) : ℤ := 2 ^ (i / 2 - 1)

/-- Both conjectures, including comparison with the absolute values in A190621. -/
theorem main :
    (∀ i n : ℕ, scale i ∣ row i n) ∧
    (∀ i : ℕ, (row i 0 / scale i).natAbs = if i % 4 = 0 then 0 else i) := by
  sorry

end OMA.S_oeis_a266491
