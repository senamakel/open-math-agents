import Mathlib

/-!
# A195915: A power-of-two shift in an XOR triangle

Source: https://oeis.org/A195915
Credit: @senamakel

Rows keep their OEIS indices. Column indices are zero-based, so the first
column has index zero and carries the row number. The recursion gives zero
outside the triangle.
-/

namespace OMA.S_oeis_a195915

/-- The XOR triangle, extended by zero past the end of each row. -/
def entry : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, 0 => n+1
  | n+1, k+1 => Nat.xor (entry n k) (entry n (k+1))

/-- Shifting the row and column by the given power of two preserves the entry. -/
theorem main :
    ∀ j n k : ℕ, k < n → n < 2^j → entry (2^j+n) (2^j+k) = entry n k := by
  sorry

end OMA.S_oeis_a195915
